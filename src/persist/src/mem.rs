// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

//! In-memory implementations for testing and benchmarking.

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::Instant;

use anyhow::anyhow;
use async_trait::async_trait;
use bytes::Bytes;

use crate::error::Error;
use crate::location::{Atomicity, BlobMulti, Consensus, ExternalError, SeqNo, VersionedData};

/// An in-memory representation of a set of [Log]s and [Blob]s that can be reused
/// across dataflows
#[cfg(test)]
#[derive(Debug)]
pub struct MemMultiRegistry {
    blob_multi_by_path: HashMap<String, Arc<tokio::sync::Mutex<MemBlobMultiCore>>>,
}

#[cfg(test)]
impl MemMultiRegistry {
    /// Constructs a new, empty [MemMultiRegistry].
    pub fn new() -> Self {
        MemMultiRegistry {
            blob_multi_by_path: HashMap::new(),
        }
    }

    /// Opens a [MemBlobMulti] associated with `path`.
    ///
    /// TODO: Replace this with PersistClientCache once they're in the same
    /// crate.
    pub async fn blob_multi(&mut self, path: &str) -> MemBlobMulti {
        if let Some(blob) = self.blob_multi_by_path.get(path) {
            MemBlobMulti::open(MemBlobMultiConfig {
                core: Arc::clone(&blob),
            })
        } else {
            let blob = Arc::new(tokio::sync::Mutex::new(MemBlobMultiCore::default()));
            self.blob_multi_by_path
                .insert(path.to_string(), Arc::clone(&blob));
            MemBlobMulti::open(MemBlobMultiConfig { core: blob })
        }
    }
}

#[derive(Debug, Default)]
struct MemBlobMultiCore {
    dataz: HashMap<String, Bytes>,
}

impl MemBlobMultiCore {
    fn get(&self, key: &str) -> Result<Option<Vec<u8>>, ExternalError> {
        Ok(self.dataz.get(key).map(|x| x.to_vec()))
    }

    fn set(&mut self, key: &str, value: Bytes) -> Result<(), ExternalError> {
        self.dataz.insert(key.to_owned(), value);
        Ok(())
    }

    fn list_keys(&self) -> Result<Vec<String>, ExternalError> {
        Ok(self.dataz.keys().cloned().collect())
    }

    fn delete(&mut self, key: &str) -> Result<(), ExternalError> {
        self.dataz.remove(key);
        Ok(())
    }
}

/// Configuration for opening a [MemBlobMulti].
#[derive(Debug, Default)]
pub struct MemBlobMultiConfig {
    core: Arc<tokio::sync::Mutex<MemBlobMultiCore>>,
}

/// An in-memory implementation of [BlobMulti].
#[derive(Debug)]
pub struct MemBlobMulti {
    core: Arc<tokio::sync::Mutex<MemBlobMultiCore>>,
}

impl MemBlobMulti {
    /// Opens the given location for non-exclusive read-write access.
    pub fn open(config: MemBlobMultiConfig) -> Self {
        MemBlobMulti { core: config.core }
    }
}

#[async_trait]
impl BlobMulti for MemBlobMulti {
    async fn get(&self, _deadline: Instant, key: &str) -> Result<Option<Vec<u8>>, ExternalError> {
        self.core.lock().await.get(key)
    }

    async fn list_keys(&self, _deadline: Instant) -> Result<Vec<String>, ExternalError> {
        self.core.lock().await.list_keys()
    }

    async fn set(
        &self,
        _deadline: Instant,
        key: &str,
        value: Bytes,
        _atomic: Atomicity,
    ) -> Result<(), ExternalError> {
        // NB: This is always atomic, so we're free to ignore the atomic param.
        self.core.lock().await.set(key, value)
    }

    async fn delete(&self, _deadline: Instant, key: &str) -> Result<(), ExternalError> {
        self.core.lock().await.delete(key)
    }
}

/// An in-memory implementation of [Consensus].
#[derive(Debug)]
pub struct MemConsensus {
    // TODO: This was intended to be a tokio::sync::Mutex but that seems to
    // regularly deadlock in the `concurrency` test.
    data: Arc<Mutex<HashMap<String, Vec<VersionedData>>>>,
}

impl Default for MemConsensus {
    fn default() -> Self {
        Self {
            data: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

#[async_trait]
impl Consensus for MemConsensus {
    async fn head(
        &self,
        _deadline: Instant,
        key: &str,
    ) -> Result<Option<VersionedData>, ExternalError> {
        let store = self.data.lock().map_err(Error::from)?;
        let values = match store.get(key) {
            None => return Ok(None),
            Some(values) => values,
        };

        Ok(values.last().cloned())
    }

    async fn compare_and_set(
        &self,
        _deadline: Instant,
        key: &str,
        expected: Option<SeqNo>,
        new: VersionedData,
    ) -> Result<Result<(), Option<VersionedData>>, ExternalError> {
        if let Some(expected) = expected {
            if new.seqno <= expected {
                return Err(ExternalError::from(
                        anyhow!("new seqno must be strictly greater than expected. Got new: {:?} expected: {:?}",
                                 new.seqno, expected)));
            }
        }

        if new.seqno.0 > i64::MAX.try_into().expect("i64::MAX known to fit in u64") {
            return Err(ExternalError::from(anyhow!(
                "sequence numbers must fit within [0, i64::MAX], received: {:?}",
                new.seqno
            )));
        }
        let mut store = self.data.lock().map_err(Error::from)?;

        let data = match store.get(key) {
            None => None,
            Some(values) => values.last(),
        };

        let seqno = data.as_ref().map(|data| data.seqno);

        if seqno != expected {
            return Ok(Err(data.cloned()));
        }

        store.entry(key.to_string()).or_default().push(new);

        Ok(Ok(()))
    }

    async fn scan(
        &self,
        _deadline: Instant,
        key: &str,
        from: SeqNo,
    ) -> Result<Vec<VersionedData>, ExternalError> {
        let store = self.data.lock().map_err(Error::from)?;
        let mut results = vec![];
        if let Some(values) = store.get(key) {
            // TODO: we could instead binary search to find the first valid
            // key and then binary search the rest.
            for value in values {
                if value.seqno >= from {
                    results.push(value.clone());
                }
            }
        }

        if results.is_empty() {
            Err(ExternalError::from(anyhow!(
                "sequence number lower bound too high for scan: {:?}",
                from
            )))
        } else {
            Ok(results)
        }
    }

    async fn truncate(
        &self,
        deadline: Instant,
        key: &str,
        seqno: SeqNo,
    ) -> Result<(), ExternalError> {
        let current = self.head(deadline, key).await?;
        if current.map_or(true, |data| data.seqno < seqno) {
            return Err(ExternalError::from(anyhow!(
                "upper bound too high for truncate: {:?}",
                seqno
            )));
        }

        let mut store = self.data.lock().map_err(Error::from)?;

        if let Some(values) = store.get_mut(key) {
            values.retain(|val| val.seqno >= seqno);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::location::tests::{blob_multi_impl_test, consensus_impl_test};

    use super::*;

    #[tokio::test]
    async fn mem_blob_multi() -> Result<(), ExternalError> {
        let registry = Arc::new(tokio::sync::Mutex::new(MemMultiRegistry::new()));
        blob_multi_impl_test(move |path| {
            let path = path.to_owned();
            let registry = Arc::clone(&registry);
            async move { Ok(registry.lock().await.blob_multi(&path).await) }
        })
        .await
    }

    #[tokio::test]
    async fn mem_consensus() -> Result<(), ExternalError> {
        consensus_impl_test(|| async { Ok(MemConsensus::default()) }).await
    }
}
