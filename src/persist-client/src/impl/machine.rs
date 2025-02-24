// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! Implementation of the persist state machine.

use std::convert::Infallible;
use std::fmt::Debug;
use std::ops::{ControlFlow, ControlFlow::Break, ControlFlow::Continue};
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};

use differential_dataflow::difference::Semigroup;
use differential_dataflow::lattice::Lattice;
use differential_dataflow::trace::Description;
use mz_persist::location::{Consensus, ExternalError, Indeterminate, SeqNo, VersionedData};
use mz_persist::retry::Retry;
use mz_persist_types::{Codec, Codec64};
use timely::progress::{Antichain, Timestamp};
use tracing::{debug, debug_span, info, trace, trace_span, Instrument};

use crate::error::InvalidUsage;
use crate::r#impl::metrics::{
    CmdMetrics, CmdsMetrics, MetricsRetryStream, RetriesMetrics, RetryMetrics,
};
use crate::r#impl::state::{ReadCapability, Since, State, StateCollections, Upper};
use crate::read::ReaderId;
use crate::{Metrics, ShardId};

#[derive(Debug)]
pub struct Machine<K, V, T, D> {
    consensus: Arc<dyn Consensus + Send + Sync>,
    cmd_metrics: Arc<CmdsMetrics>,
    retry_metrics: Arc<RetriesMetrics>,

    state: State<K, V, T, D>,
}

// Impl Clone regardless of the type params.
impl<K, V, T: Clone, D> Clone for Machine<K, V, T, D> {
    fn clone(&self) -> Self {
        Self {
            consensus: Arc::clone(&self.consensus),
            cmd_metrics: Arc::clone(&self.cmd_metrics),
            retry_metrics: Arc::clone(&self.retry_metrics),
            state: self.state.clone(),
        }
    }
}

impl<K, V, T, D> Machine<K, V, T, D>
where
    K: Debug + Codec,
    V: Debug + Codec,
    T: Timestamp + Lattice + Codec64,
    D: Semigroup + Codec64,
{
    pub async fn new(
        shard_id: ShardId,
        consensus: Arc<dyn Consensus + Send + Sync>,
        metrics: &Metrics,
    ) -> Result<Self, InvalidUsage<T>> {
        let cmd_metrics = Arc::new(metrics.cmds_metrics());
        let retry_metrics = Arc::new(metrics.retries_metrics());
        let state = cmd_metrics
            .init_state
            .run_cmd(|| Self::maybe_init_state(consensus.as_ref(), &retry_metrics, shard_id))
            .await?;
        Ok(Machine {
            consensus,
            cmd_metrics,
            retry_metrics,
            state,
        })
    }

    pub fn shard_id(&self) -> ShardId {
        self.state.shard_id()
    }

    pub async fn fetch_upper(&mut self) -> Antichain<T> {
        self.fetch_and_update_state().await;
        self.state.upper()
    }

    pub fn upper(&self) -> Antichain<T> {
        self.state.upper()
    }

    pub async fn register(&mut self, reader_id: &ReaderId) -> (Upper<T>, ReadCapability<T>) {
        let cmd_metrics = Arc::clone(&self.cmd_metrics);
        let (seqno, (shard_upper, read_cap)) = self
            .apply_unbatched_idempotent_cmd(&cmd_metrics.register, |seqno, state| {
                state.register(seqno, reader_id)
            })
            .await;
        debug_assert_eq!(seqno, read_cap.seqno);
        (shard_upper, read_cap)
    }

    pub async fn clone_reader(&mut self, new_reader_id: &ReaderId) -> ReadCapability<T> {
        let cmd_metrics = Arc::clone(&self.cmd_metrics);
        let (seqno, read_cap) = self
            .apply_unbatched_idempotent_cmd(&cmd_metrics.clone_reader, |seqno, state| {
                state.clone_reader(seqno, new_reader_id)
            })
            .await;
        debug_assert_eq!(seqno, read_cap.seqno);
        read_cap
    }

    pub async fn compare_and_append(
        &mut self,
        keys: &[String],
        desc: &Description<T>,
    ) -> Result<Result<Result<SeqNo, Upper<T>>, InvalidUsage<T>>, Indeterminate> {
        let cmd_metrics = Arc::clone(&self.cmd_metrics);
        loop {
            let (seqno, res) = self
                .apply_unbatched_cmd(&cmd_metrics.compare_and_append, |_, state| {
                    state.compare_and_append(keys, desc)
                })
                .await?;

            match res {
                Ok(()) => {
                    return Ok(Ok(Ok(seqno)));
                }
                Err(Ok(_current_upper)) => {
                    // If the state machine thinks that the shard upper is not
                    // far enough along, it could be because the caller of this
                    // method has found out that it advanced via some some
                    // side-channel that didn't update our local cache of the
                    // machine state. So, fetch the latest state and try again
                    // if we indeed get something different.
                    self.fetch_and_update_state().await;
                    let current_upper = self.upper();

                    // We tried to to a compare_and_append with the wrong
                    // expected upper, that won't work.
                    if &current_upper != desc.lower() {
                        return Ok(Ok(Err(Upper(current_upper))));
                    } else {
                        // The upper stored in state was outdated. Retry after
                        // updating.
                    }
                }
                Err(Err(invalid_usage)) => {
                    return Ok(Err(invalid_usage));
                }
            }
        }
    }

    pub async fn downgrade_since(
        &mut self,
        reader_id: &ReaderId,
        new_since: &Antichain<T>,
    ) -> (SeqNo, Since<T>) {
        let cmd_metrics = Arc::clone(&self.cmd_metrics);
        self.apply_unbatched_idempotent_cmd(&cmd_metrics.downgrade_since, |_, state| {
            state.downgrade_since(reader_id, new_since)
        })
        .await
    }

    pub async fn expire_reader(&mut self, reader_id: &ReaderId) -> SeqNo {
        let cmd_metrics = Arc::clone(&self.cmd_metrics);
        let (seqno, _existed) = self
            .apply_unbatched_idempotent_cmd(&cmd_metrics.expire_reader, |_, state| {
                state.expire_reader(reader_id)
            })
            .await;
        seqno
    }

    pub async fn snapshot(
        &mut self,
        as_of: &Antichain<T>,
    ) -> Result<Vec<(String, Description<T>)>, Since<T>> {
        let mut retry: Option<MetricsRetryStream> = None;
        loop {
            let upper = match self.state.snapshot(as_of) {
                Ok(Ok(x)) => return Ok(x),
                Ok(Err(Upper(upper))) => {
                    // The upper isn't ready yet, fall through and try again.
                    upper
                }
                Err(Since(since)) => return Err(Since(since)),
            };
            // Only sleep after the first fetch, because the first time through
            // maybe our state was just out of date.
            retry = Some(match retry.take() {
                None => self
                    .retry_metrics
                    .snapshot
                    .stream(Retry::persist_defaults(SystemTime::now()).into_retry_stream()),
                Some(retry) => {
                    // Use a duration based threshold here instead of the usual
                    // INFO_MIN_ATTEMPTS because here we're waiting on an
                    // external thing to arrive.
                    if retry.next_sleep() >= Duration::from_millis(64) {
                        info!(
                            "snapshot as of {:?} not yet available for upper {:?} retrying in {:?}",
                            as_of,
                            upper,
                            retry.next_sleep()
                        );
                    } else {
                        debug!(
                            "snapshot as of {:?} not yet available for upper {:?} retrying in {:?}",
                            as_of,
                            upper,
                            retry.next_sleep()
                        );
                    }
                    retry.sleep().await
                }
            });
            self.fetch_and_update_state().await;
        }
    }

    // NB: Unlike the other methods here, this one is read-only.
    pub async fn verify_listen(&self, as_of: &Antichain<T>) -> Result<Self, Since<T>> {
        match self.state.verify_listen(as_of) {
            Ok(Ok(())) => Ok(self.clone()),
            Ok(Err(Upper(_))) => {
                // The upper may not be ready yet (maybe it would be ready if we
                // re-fetched state), but that's okay! One way to think of
                // Listen is as an async stream where creating the stream at any
                // legal as_of does not block but then updates trickle in once
                // they are available.
                Ok(self.clone())
            }
            Err(Since(since)) => return Err(Since(since)),
        }
    }

    pub async fn next_listen_batch(
        &mut self,
        frontier: &Antichain<T>,
    ) -> (Vec<String>, Description<T>) {
        let mut retry: Option<MetricsRetryStream> = None;
        loop {
            if let Some((keys, desc)) = self.state.next_listen_batch(frontier) {
                return (keys.to_owned(), desc.clone());
            }
            // Only sleep after the first fetch, because the first time through
            // maybe our state was just out of date.
            retry = Some(match retry.take() {
                None => self
                    .retry_metrics
                    .next_listen_batch
                    .stream(Retry::persist_defaults(SystemTime::now()).into_retry_stream()),
                Some(retry) => {
                    // Wait a bit and try again. Intentionally don't ever log
                    // this at info level.
                    //
                    // TODO: See if we can watch for changes in Consensus to be
                    // more reactive here.
                    debug!(
                        "next_listen_batch didn't find new data, retrying in {:?}",
                        retry.next_sleep()
                    );
                    retry.sleep().instrument(trace_span!("listen::sleep")).await
                }
            });
            self.fetch_and_update_state().await;
        }
    }

    async fn apply_unbatched_idempotent_cmd<
        R,
        WorkFn: FnMut(SeqNo, &mut StateCollections<T>) -> ControlFlow<Infallible, R>,
    >(
        &mut self,
        cmd: &CmdMetrics,
        mut work_fn: WorkFn,
    ) -> (SeqNo, R) {
        let mut retry = self
            .retry_metrics
            .idempotent_cmd
            .stream(Retry::persist_defaults(SystemTime::now()).into_retry_stream());
        loop {
            match self.apply_unbatched_cmd(cmd, &mut work_fn).await {
                Ok((seqno, x)) => match x {
                    Ok(x) => return (seqno, x),
                    Err(infallible) => match infallible {},
                },
                Err(err) => {
                    if retry.attempt() >= INFO_MIN_ATTEMPTS {
                        info!("apply_unbatched_idempotent_cmd {} received an indeterminate error, retrying in {:?}: {}", cmd.name, retry.next_sleep(), err);
                    } else {
                        debug!("apply_unbatched_idempotent_cmd {} received an indeterminate error, retrying in {:?}: {}", cmd.name, retry.next_sleep(), err);
                    }
                    retry = retry.sleep().await;
                    continue;
                }
            }
        }
    }

    async fn apply_unbatched_cmd<
        R,
        E,
        WorkFn: FnMut(SeqNo, &mut StateCollections<T>) -> ControlFlow<E, R>,
    >(
        &mut self,
        cmd: &CmdMetrics,
        mut work_fn: WorkFn,
    ) -> Result<(SeqNo, Result<R, E>), Indeterminate> {
        cmd.run_cmd(|| async {
            let path = self.shard_id().to_string();

            loop {
                let (work_ret, new_state) = match self.state.clone_apply(&mut work_fn) {
                    Continue(x) => x,
                    Break(err) => return Ok((self.state.seqno(), Err(err))),
                };
                trace!(
                    "apply_unbatched_cmd {} attempting {}\n  new_state={:?}",
                    cmd.name,
                    self.state.seqno(),
                    new_state
                );

                let new = VersionedData::from((new_state.seqno(), &new_state));
                // SUBTLE! Unlike the other consensus and blob uses, we can't
                // automatically retry indeterminate ExternalErrors here. However,
                // if the state change itself is _idempotent_, then we're free to
                // retry even indeterminate errors. See
                // [Self::apply_unbatched_idempotent_cmd].
                let payload_len = new.data.len();
                let cas_res = retry_determinate(
                    &self.retry_metrics.determinate.apply_unbatched_cmd_cas,
                    || async {
                        self.consensus
                            .compare_and_set(
                                Instant::now() + FOREVER,
                                &path,
                                Some(self.state.seqno()),
                                new.clone(),
                            )
                            .await
                    },
                )
                .instrument(debug_span!("apply_unbatched_cmd::cas", payload_len))
                .await
                .map_err(|err| {
                    debug!("apply_unbatched_cmd {} errored: {}", cmd.name, err);
                    err
                })?;
                match cas_res {
                    Ok(()) => {
                        trace!(
                            "apply_unbatched_cmd {} succeeded {}\n  new_state={:?}",
                            cmd.name,
                            new_state.seqno(),
                            new_state
                        );
                        self.state = new_state;

                        // Bound the number of entries in consensus.
                        let () = retry_external(
                            &self.retry_metrics.external.apply_unbatched_cmd_truncate,
                            || async {
                                self.consensus
                                    .truncate(Instant::now() + FOREVER, &path, self.state.seqno())
                                    .await
                            },
                        )
                        .instrument(debug_span!("apply_unbatched_cmd::truncate"))
                        .await;

                        return Ok((self.state.seqno(), Ok(work_ret)));
                    }
                    Err(current) => {
                        debug!(
                            "apply_unbatched_cmd {} lost the CaS race, retrying: {} vs {:?}",
                            cmd.name,
                            self.state.seqno(),
                            current.as_ref().map(|x| x.seqno)
                        );
                        self.update_state(current).await;

                        // Intentionally don't backoff here. It would only make
                        // starvation issues even worse.
                        continue;
                    }
                }
            }
        })
        .await
    }

    async fn maybe_init_state(
        consensus: &(dyn Consensus + Send + Sync),
        retry_metrics: &RetriesMetrics,
        shard_id: ShardId,
    ) -> Result<State<K, V, T, D>, InvalidUsage<T>> {
        debug!("Machine::maybe_init_state shard_id={}", shard_id);

        let path = shard_id.to_string();
        let mut current = retry_external(&retry_metrics.external.maybe_init_state_head, || async {
            consensus.head(Instant::now() + FOREVER, &path).await
        })
        .await;

        loop {
            // First, check if the shard has already been initialized.
            if let Some(current) = current.as_ref() {
                let current_state = match State::decode(&current.data) {
                    Ok(x) => x,
                    Err(err) => return Err(err),
                };
                debug_assert_eq!(current.seqno, current_state.seqno());
                return Ok(current_state);
            }

            // It hasn't been initialized, try initializing it.
            let state = State::new(shard_id);
            let new = VersionedData::from((state.seqno(), &state));
            trace!(
                "maybe_init_state attempting {}\n  state={:?}",
                new.seqno,
                state
            );
            let cas_res = retry_external(&retry_metrics.external.maybe_init_state_cas, || async {
                consensus
                    .compare_and_set(Instant::now() + FOREVER, &path, None, new.clone())
                    .await
            })
            .await;
            match cas_res {
                Ok(()) => {
                    trace!(
                        "maybe_init_state succeeded {}\n  state={:?}",
                        state.seqno(),
                        state
                    );
                    return Ok(state);
                }
                Err(x) => {
                    // We lost a CaS race, use the value included in the CaS
                    // expectation error. Because we used None for expected,
                    // this should never be None.
                    debug!(
                        "maybe_init_state lost the CaS race, using current value: {:?}",
                        x.as_ref().map(|x| x.seqno)
                    );
                    debug_assert!(x.is_some());
                    current = x
                }
            }
        }
    }

    pub async fn fetch_and_update_state(&mut self) {
        let shard_id = self.shard_id();
        let current = retry_external(
            &self.retry_metrics.external.fetch_and_update_state_head,
            || async {
                self.consensus
                    .head(Instant::now() + FOREVER, &shard_id.to_string())
                    .await
            },
        )
        .instrument(trace_span!("fetch_and_update_state::head"))
        .await;
        self.update_state(current).await;
    }

    async fn update_state(&mut self, current: Option<VersionedData>) {
        let current = match current {
            Some(x) => x,
            None => {
                // Machine is only constructed once, we've successfully
                // retrieved state from durable storage, but now it's gone? In
                // the future, maybe this means the shard was deleted or
                // something, but for now it's entirely unexpected.
                panic!("internal error: missing state {}", self.state.shard_id());
            }
        };
        let current_state = State::decode(&current.data)
            // We received a State with different declared codecs than a
            // previous SeqNo of the same State. Fail loudly.
            .expect("internal error: new durable state disagreed with old durable state");
        debug_assert_eq!(current.seqno, current_state.seqno());
        debug_assert!(self.state.seqno() <= current.seqno);
        self.state = current_state;
    }
}

pub const INFO_MIN_ATTEMPTS: usize = 3;

pub const FOREVER: Duration = Duration::from_secs(1_000_000_000);

pub async fn retry_external<R, F, WorkFn>(metrics: &RetryMetrics, mut work_fn: WorkFn) -> R
where
    F: std::future::Future<Output = Result<R, ExternalError>>,
    WorkFn: FnMut() -> F,
{
    let mut retry = metrics.stream(Retry::persist_defaults(SystemTime::now()).into_retry_stream());
    loop {
        match work_fn().await {
            Ok(x) => {
                if retry.attempt() > 0 {
                    debug!(
                        "external operation {} succeeded after failing at least once",
                        metrics.name,
                    );
                }
                return x;
            }
            Err(err) => {
                if retry.attempt() >= INFO_MIN_ATTEMPTS {
                    info!(
                        "external operation {} failed, retrying in {:?}: {:#}",
                        metrics.name,
                        retry.next_sleep(),
                        err
                    );
                } else {
                    debug!(
                        "external operation {} failed, retrying in {:?}: {:#}",
                        metrics.name,
                        retry.next_sleep(),
                        err
                    );
                }
                retry = retry.sleep().await;
            }
        }
    }
}

pub async fn retry_determinate<R, F, WorkFn>(
    metrics: &RetryMetrics,
    mut work_fn: WorkFn,
) -> Result<R, Indeterminate>
where
    F: std::future::Future<Output = Result<R, ExternalError>>,
    WorkFn: FnMut() -> F,
{
    let mut retry = metrics.stream(Retry::persist_defaults(SystemTime::now()).into_retry_stream());
    loop {
        match work_fn().await {
            Ok(x) => {
                if retry.attempt() > 0 {
                    debug!(
                        "external operation {} succeeded after failing at least once",
                        metrics.name,
                    );
                }
                return Ok(x);
            }
            Err(ExternalError::Determinate(err)) => {
                if retry.attempt() >= INFO_MIN_ATTEMPTS {
                    info!(
                        "external operation {} failed, retrying in {:?}: {:#}",
                        metrics.name,
                        retry.next_sleep(),
                        err
                    );
                } else {
                    debug!(
                        "external operation {} failed, retrying in {:?}: {:#}",
                        metrics.name,
                        retry.next_sleep(),
                        err
                    );
                }
                retry = retry.sleep().await;
                continue;
            }
            Err(ExternalError::Indeterminate(x)) => return Err(x),
        }
    }
}

#[cfg(test)]
mod tests {
    use mz_ore::cast::CastFrom;

    use crate::tests::new_test_client;
    use crate::ShardId;

    use super::*;

    #[tokio::test]
    async fn apply_unbatched_cmd_truncate() {
        mz_ore::test::init_logging();

        let (mut write, _) = new_test_client()
            .await
            .expect_open::<String, (), u64, i64>(ShardId::new())
            .await;
        let consensus = Arc::clone(&write.machine.consensus);

        // Write a bunch of batches. This should result in a bounded number of
        // live entries in consensus.
        const NUM_BATCHES: u64 = 100;
        for idx in 0..NUM_BATCHES {
            write
                .expect_compare_and_append(&[((idx.to_string(), ()), idx, 1)], idx, idx + 1)
                .await;
        }
        let key = write.machine.shard_id().to_string();
        let consensus_entries = consensus
            .scan(Instant::now() + FOREVER, &key, SeqNo::minimum())
            .await
            .expect("scan failed");
        // Make sure we constructed the key correctly.
        assert!(consensus_entries.len() > 0);
        // Make sure the number of entries is bounded.
        //
        // In practice, this is always 1 right now, but when we implement
        // incremental state, it will be something like log(NUM_BATCHES).
        let max_entries = usize::cast_from(NUM_BATCHES.next_power_of_two().trailing_zeros());
        assert!(
            consensus_entries.len() <= max_entries,
            "expected at most {} entries got {}",
            max_entries,
            consensus_entries.len()
        );
    }
}
