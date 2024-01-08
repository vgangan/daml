// Copyright (c) 2023 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.canton.ledger.client.services.updates

import com.daml.grpc.adapter.ExecutionSequencerFactory
import com.daml.grpc.adapter.client.pekko.ClientAdapter
import com.daml.ledger.api.v2.participant_offset.ParticipantOffset
import com.daml.ledger.api.v2.transaction_filter.TransactionFilter
import com.daml.ledger.api.v2.update_service.UpdateServiceGrpc.UpdateServiceStub
import com.daml.ledger.api.v2.update_service.{GetUpdatesRequest, GetUpdatesResponse}
import org.apache.pekko.NotUsed
import org.apache.pekko.stream.scaladsl.Source

class UpdateServiceClient(service: UpdateServiceStub)(implicit
    esf: ExecutionSequencerFactory
) {
  def getUpdatesSource(
      begin: ParticipantOffset,
      filter: TransactionFilter,
      verbose: Boolean = false,
      end: Option[ParticipantOffset] = None,
  ): Source[GetUpdatesResponse, NotUsed] = {
    ClientAdapter
      .serverStreaming(
        GetUpdatesRequest(
          beginExclusive = Some(begin),
          endInclusive = end,
          filter = Some(filter),
          verbose = verbose,
        ),
        service.getUpdates,
      )
  }

}
