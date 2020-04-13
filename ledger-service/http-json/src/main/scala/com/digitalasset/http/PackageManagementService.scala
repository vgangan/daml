// Copyright (c) 2020 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.http

import com.daml.jwt.domain.Jwt

import scala.concurrent.{ExecutionContext, Future}

class PackageManagementService(
    listKnownPackagesFn: LedgerClientJwt.ListKnownPackages,
    uploadDarFileFn: LedgerClientJwt.UploadDarFile
)(implicit ec: ExecutionContext) {

  def listKnownPackages(jwt: Jwt): Future[Seq[admin.PackageDetails]] =
    listKnownPackagesFn(jwt).map(_.map(admin.PackageDetails.fromLedgerApi))

}
