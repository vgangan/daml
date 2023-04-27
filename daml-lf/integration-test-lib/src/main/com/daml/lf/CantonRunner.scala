// Copyright (c) 2023 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.lf
package integrationtest

import com.daml.bazeltools.BazelRunfiles._
import com.daml.grpc.adapter.ExecutionSequencerFactory
import com.daml.jwt.JwtSigner
import com.daml.jwt.domain.DecodedJwt
import com.daml.lf.data.Ref
import com.daml.ledger.api.auth
import com.daml.ledger.resources.{ResourceContext, ResourceOwner, Resource}
import com.daml.platform.services.time.TimeProviderType
import com.daml.ports.{Port, LockedFreePort, PortLock}
import com.daml.scalautil.Statement.discard
import com.daml.timer.RetryStrategy
import com.google.protobuf.ByteString
import spray.json.JsString

import scala.concurrent.duration.DurationInt
import scala.concurrent.Future
import scala.sys.process.Process
import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Files}

object CantonRunner {

  private val logger = org.slf4j.LoggerFactory.getLogger(getClass)

  private[integrationtest] def toJson(s: String): String = JsString(s).toString()
  private[integrationtest] def toJson(path: Path): String = toJson(path.toString)

  def run(config: CantonConfig, tmpDir: Path)(implicit
      esf: ExecutionSequencerFactory
  ): ResourceOwner[Vector[Port]] =
    new ResourceOwner[Vector[Port]] {
      import config._
      protected val cantonConfigFile = tmpDir.resolve("participant.config")
      protected val cantonLogFile = tmpDir.resolve("canton.log")
      protected val portFile = tmpDir.resolve("portfile")
      def info(s: String) = if (debug) logger.info(s)

      override def acquire()(implicit context: ResourceContext): Resource[Vector[Port]] = {
        def start(): Future[
          ((PortLock.Locked, PortLock.Locked), Vector[(PortLock.Locked, PortLock.Locked)], Process)
        ] = {
          val ports =
            Vector.fill(nParticipants)(LockedFreePort.find() -> LockedFreePort.find())
          val domainPublicApi = LockedFreePort.find()
          val domainAdminApi = LockedFreePort.find()

          val cantonPath = rlocation(
            "external/canton/lib/canton-open-source-2.7.0-SNAPSHOT.jar"
          )
          val exe = if (sys.props("os.name").toLowerCase.contains("windows")) ".exe" else ""
          val java = s"${System.getenv("JAVA_HOME")}/bin/java${exe}"
          val (timeType, clockType) = timeProviderType match {
            case TimeProviderType.Static => (Some("monotonic-time"), Some("sim-clock"))
            case TimeProviderType.WallClock => (None, None)
          }
          val authConfig = authSecret.fold("")(secret => s"""auth-services = [{
                                                            |          type = unsafe-jwt-hmac-256
                                                            |          secret = "${toJson(secret)}"
                                                            |        }]
                                                            |""".stripMargin)
          val tls = tlsConfig.fold("")(config => s"""tls {
                 |          cert-chain-file = ${toJson(config.serverCrt)}
                 |          private-key-file = ${toJson(config.serverPem)}
                 |          trust-collection-file = ${toJson(config.caCrt)}
                 |        }""".stripMargin)

          def participantConfig(i: Int) = {
            val (adminPort, ledgerApiPort) = ports(i)
            s"""participant${i} {
               |      admin-api.port = ${adminPort.port}
               |      ledger-api{
               |        port = ${ledgerApiPort.port}
               |        ${authConfig}
               |        ${tls}
               |      }
               |      storage.type = memory
               |      parameters = {
               |        enable-engine-stack-traces = true
               |        dev-version-support = ${devMode}
               |      }
               |      ${timeType.fold("")(x => "testing-time.type = " + x)}
               |    }""".stripMargin
          }
          val participantsConfig =
            (0 until nParticipants).map(participantConfig).mkString("\n")
          val cantonConfig =
            s"""canton {
               |  parameters{
               |    non-standard-config = yes
               |    dev-version-support = yes
               |    ports-file = ${toJson(portFile)}
               |    ${clockType.fold("")(x => "clock.type = " + x)}
               |  }
               |
               |  domains {
               |    local {
               |      storage.type = memory
               |      public-api.port = ${domainPublicApi.port}
               |      admin-api.port = ${domainAdminApi.port}
               |      init.domain-parameters.protocol-version = ${if (devMode) "dev" else "4"}
               |    }
               |  }
               |  participants {
               |    ${participantsConfig}
               |  }
               |}
          """.stripMargin
          discard(Files.write(cantonConfigFile, cantonConfig.getBytes(StandardCharsets.UTF_8)))
          val debugOptions =
            if (debug) List("--log-file-name", cantonLogFile.toString, "--verbose")
            else List.empty
          info(
            s"""Starting canton with parameters:
               |  authSecret = ${authSecret}
               |  darFiles = ${darFiles}
               |  devMode = ${devMode}
               |  nParticipants = ${nParticipants}
               |  timeProviderType = ${timeProviderType}
               |  tlsEnable = ${config.tlsConfig.isDefined}
               |""".stripMargin
          )
          for {
            proc <- Future(
              Process(
                java ::
                  "-jar" ::
                  cantonPath ::
                  "daemon" ::
                  "--auto-connect-local" ::
                  "-c" ::
                  cantonConfigFile.toString ::
                  debugOptions
              ).run()
            )
            _ <- RetryStrategy.constant(attempts = 240, waitTime = 1.seconds) { (_, _) =>
              info("waiting for Canton to start")
              Future(Files.size(portFile))
            }
            _ = info("Canton started")
            _ <-
              Future.traverse(ports) { case (_, ledgerPort) =>
                for {
                  client <- ledgerClient(ledgerPort.port, adminToken)
                  _ <- Future.traverse(darFiles) { file =>
                    client.packageManagementClient.uploadDarFile(
                      ByteString.copyFrom(Files.readAllBytes(file))
                    )
                  }
                } yield ()
              }
            _ = info(s"${darFiles.size} packages loaded to ${ports.size} participants")
          } yield ((domainAdminApi, domainPublicApi), ports, proc)
        }
        def stop(
            r: (
                (PortLock.Locked, PortLock.Locked),
                Vector[(PortLock.Locked, PortLock.Locked)],
                Process,
            )
        ): Future[Unit] = {
          val ((domainAdminApi, domainPublicApi), ports, process) = r
          process.destroy()
          discard(process.exitValue())
          domainAdminApi.unlock()
          domainPublicApi.unlock()
          ports.foreach { case (p1, p2) =>
            p1.unlock()
            p2.unlock()
          }
          Future.unit
        }
        Resource(start())(stop).map({ case (_, ports, _) => ports.map(_._2.port) })
      }
    }

  def getToken(
      userId: String,
      authSecret: Option[String] = None,
  ): Option[String] = authSecret.map { secret =>
    val payload = auth.StandardJWTPayload(
      issuer = None,
      userId = userId,
      participantId = None,
      exp = None,
      format = auth.StandardJWTTokenFormat.Scope,
      audiences = List.empty,
    )
    val header = """{"alg": "HS256", "typ": "JWT"}"""
    val jwt = DecodedJwt[String](header, auth.AuthServiceJWTCodec.writeToString(payload))
    JwtSigner.HMAC256.sign(jwt, secret).toEither match {
      case Right(a) => a.value
      case Left(e) => throw new IllegalStateException(e.toString)
    }
  }

  val adminUserId = Ref.UserId.assertFromString("participant_admin")
}
