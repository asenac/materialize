// Copyright Materialize, Inc. and contributors. All rights reserved.
//
// Use of this software is governed by the Business Source License
// included in the LICENSE file.
//
// As of the Change Date specified in that file, in accordance with
// the Business Source License, use of this software will be governed
// by the Apache License, Version 2.0.

use std::pin::Pin;
use std::time::Duration;

use async_trait::async_trait;
use futures::StreamExt;
use pubnub_hyper::core::data::{channel, message::Type};
use pubnub_hyper::{Builder, DefaultRuntime, DefaultTransport, PubNub};
use timely::scheduling::SyncActivator;
use tracing::info;

use mz_dataflow_types::connections::ConnectionContext;
use mz_dataflow_types::sources::{
    encoding::SourceDataEncoding, ExternalSourceConnection, MzOffset,
};
use mz_expr::PartitionId;
use mz_repr::{Datum, GlobalId, Row};

use crate::source::{SourceMessage, SourceMessageType, SourceReader, SourceReaderError};

/// Information required to sync data from PubNub
pub struct PubNubSourceReader {
    channel: channel::Name,
    pubnub: PubNub,
    stream: Option<Pin<Box<pubnub_hyper::core::Subscription<DefaultRuntime>>>>,
}

#[async_trait(?Send)]
impl SourceReader for PubNubSourceReader {
    type Key = ();
    type Value = Row;
    type Diff = ();

    fn new(
        _source_name: String,
        _source_id: GlobalId,
        _worker_id: usize,
        _worker_count: usize,
        _consumer_activator: SyncActivator,
        connection: ExternalSourceConnection,
        _restored_offsets: Vec<(PartitionId, Option<MzOffset>)>,
        _encoding: SourceDataEncoding,
        _: crate::source::metrics::SourceBaseMetrics,
        _: ConnectionContext,
    ) -> Result<Self, anyhow::Error> {
        let pubnub_conn = match connection {
            ExternalSourceConnection::PubNub(pubnub_conn) => pubnub_conn,
            _ => {
                panic!(
                    "PubNub is the only legitimate ExternalSourceConnection for PubNubSourceReader"
                )
            }
        };
        let transport = DefaultTransport::new()
            // we don't need a publish key for subscribing
            .publish_key("")
            .subscribe_key(&pubnub_conn.subscribe_key)
            .build()?;

        let pubnub = Builder::new()
            .transport(transport)
            // TODO(guswynn): figure out if this or hyper spawns tasks
            // here, and if we need to name them
            .runtime(DefaultRuntime)
            .build();

        let channel = pubnub_conn.channel;
        let channel: channel::Name = channel
            .parse()
            .or_else(|_| Err(anyhow::anyhow!("invalid pubnub channel: {}", channel)))?;

        Ok(Self {
            channel,
            pubnub,
            stream: None,
        })
    }

    async fn next(
        &mut self,
        timestamp_frequency: Duration,
    ) -> Option<Result<SourceMessageType<Self::Key, Self::Value, Self::Diff>, SourceReaderError>>
    {
        loop {
            let stream = match &mut self.stream {
                None => {
                    self.stream = Some(Box::pin(self.pubnub.subscribe(self.channel.clone()).await));
                    self.stream.as_mut().expect("we just created the stream")
                }
                Some(stream) => stream,
            };

            match stream.next().await {
                Some(msg) => {
                    if msg.message_type == Type::Publish {
                        let s = msg.json.dump();

                        let row = Row::pack_slice(&[Datum::String(&s)]);

                        return Some(Ok(SourceMessageType::Finalized(SourceMessage {
                            partition: PartitionId::None,
                            offset: MzOffset {
                                // NOTE(guswynn):
                                //
                                // We convert the u64 timetoken that should
                                // 10ns granularity to a u64. Hopefully,
                                // this doesn't overflow, but we may convert
                                // MzOffset to a u64.
                                //
                                // Also, we elect to skip the `region` part of
                                // the timetoken structure, as I can't find
                                // documentation on the pubnub website on
                                // if it is required to produce monotonic
                                // timetokens.
                                offset: msg.timetoken.t,
                            },
                            upstream_time_millis: None,
                            key: (),
                            value: row,
                            headers: None,
                            specific_diff: (),
                        })));
                    }
                }
                None => {
                    info!(
                        "pubnub channel {:?} disconnected. reconnecting",
                        self.channel.to_string()
                    );
                    self.stream.take();
                    tokio::time::sleep(timestamp_frequency).await;
                }
            }
        }
    }
}
