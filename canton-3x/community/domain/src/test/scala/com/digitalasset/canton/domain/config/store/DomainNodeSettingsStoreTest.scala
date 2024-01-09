// Copyright (c) 2023 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.canton.domain.config.store

import com.daml.nameof.NameOf.functionFullName
import com.digitalasset.canton.BaseTest
import com.digitalasset.canton.resource.DbStorage
import com.digitalasset.canton.store.db.{DbTest, H2Test, PostgresTest}
import org.scalatest.wordspec.{AsyncWordSpec, AsyncWordSpecLike}

import scala.concurrent.Future

trait DomainNodeSettingsStoreTest {
  this: AsyncWordSpecLike with BaseTest =>

  protected def makeConfig(uniqueKeys: Boolean = false) =
    StoredDomainNodeSettings(
      defaultStaticDomainParameters.update(uniqueContractKeys = uniqueKeys)
    )

  protected def domainNodeSettingsStoreTest(
      // argument: reset static domain parameters
      mkStore: => BaseNodeSettingsStore[StoredDomainNodeSettings]
  ): Unit = {

    "returns stored values" in {
      val store = mkStore
      val config = makeConfig()
      for {
        _ <- store.saveSettings(config).valueOrFail("save")
        current <- store.fetchSettings.valueOrFail("fetch")
      } yield {
        current should contain(config)
      }
    }

    "supports updating values" in {
      defaultStaticDomainParameters.uniqueContractKeys shouldBe false // test assumes that this default doesn't change
      val store = mkStore
      val config = makeConfig()
      val updateConfig = makeConfig(true)

      for {
        _ <- store.saveSettings(config).valueOrFail("save")
        _ <- store.saveSettings(updateConfig).valueOrFail("save")
        current <- store.fetchSettings.valueOrFail("fetch")
      } yield {
        current should contain(updateConfig)
      }
    }

  }

}

class DomainNodeSettingsStoreTestInMemory
    extends AsyncWordSpec
    with BaseTest
    with DomainNodeSettingsStoreTest {

  behave like domainNodeSettingsStoreTest(
    new InMemoryBaseNodeConfigStore[StoredDomainNodeSettings](loggerFactory)
  )
}

trait DbDomainNodeSettingsStoreTest
    extends AsyncWordSpec
    with BaseTest
    with DomainNodeSettingsStoreTest {
  this: DbTest =>

  override def cleanDb(storage: DbStorage): Future[Unit] = {
    import storage.api.*
    storage
      .update(
        DBIO.seq(
          sqlu"truncate table domain_node_settings"
        ),
        functionFullName,
      )

  }

  behave like domainNodeSettingsStoreTest(mkStore)

  private def mkStore =
    new DbDomainNodeSettingsStore(
      storage,
      timeouts,
      loggerFactory,
    )
}

class DbDomainNodeSettingsStoreTestPostgres extends DbDomainNodeSettingsStoreTest with PostgresTest

class DbDomainNodeSettingsStoreTestH2 extends DbDomainNodeSettingsStoreTest with H2Test