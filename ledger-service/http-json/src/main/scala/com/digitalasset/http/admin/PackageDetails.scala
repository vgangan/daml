// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.http.admin

import java.time.Instant

import com.daml.api.util.TimestampConversion

final case class PackageDetails(
    packageId: String,
    packageSize: Long,
    knownSince: Option[Instant],
    sourceDescription: Option[String]
)

object PackageDetails {
  def fromLedgerApi(
      a: com.daml.ledger.api.v1.admin.package_management_service.PackageDetails): PackageDetails =
    PackageDetails(
      packageId = a.packageId,
      packageSize = a.packageSize,
      knownSince = a.knownSince.map(TimestampConversion.toInstant),
      sourceDescription = Option(a.sourceDescription).filter(_.nonEmpty)
    )
}
