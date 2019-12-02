// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.platform.sandbox.stores.ledger.inmemory

import java.time.Instant
import java.util.concurrent.atomic.AtomicReference

import akka.NotUsed
import akka.stream.scaladsl.Source
import com.daml.ledger.participant.state.index.v2.PackageDetails
import com.daml.ledger.participant.state.v1._
import com.digitalasset.api.util.TimeProvider
import com.digitalasset.daml.lf.data.Ref.LedgerString.ordering
import com.digitalasset.daml.lf.data.Ref.{PackageId, Party, TransactionIdString}
import com.digitalasset.daml.lf.data.{ImmArray, Time}
import com.digitalasset.daml.lf.engine.Blinding
import com.digitalasset.daml.lf.language.Ast
import com.digitalasset.daml.lf.transaction.Node
import com.digitalasset.daml.lf.value.Value.{AbsoluteContractId, ContractId}
import com.digitalasset.daml_lf_dev.DamlLf.Archive
import com.digitalasset.ledger.api.domain.{
  ApplicationId,
  CommandId,
  LedgerId,
  PartyDetails,
  RejectionReason
}
import com.digitalasset.ledger.api.health.{HealthStatus, Healthy}
import com.digitalasset.platform.participant.util.EventFilter.TemplateAwareFilter
import com.digitalasset.platform.sandbox.services.transaction.SandboxEventIdFormatter
import com.digitalasset.platform.sandbox.stores.ActiveLedgerState.ActiveContract
import com.digitalasset.platform.sandbox.stores.deduplicator.Deduplicator
import com.digitalasset.platform.sandbox.stores.ledger.LedgerEntry.{Checkpoint, Rejection}
import com.digitalasset.platform.sandbox.stores.ledger.ScenarioLoader.LedgerEntryOrBump
import com.digitalasset.platform.sandbox.stores.ledger._
import com.digitalasset.platform.sandbox.stores.{
  ActiveLedgerState,
  InMemoryActiveLedgerState,
  InMemoryPackageStore
}
import org.slf4j.LoggerFactory

import scala.concurrent.Future
import scala.util.{Failure, Success, Try}

sealed trait InMemoryEntry extends Product with Serializable
final case class InMemoryLedgerEntry(entry: LedgerEntry) extends InMemoryEntry
final case class InMemoryConfigEntry(entry: ConfigurationEntry) extends InMemoryEntry
final case class InMemoryPartyEntry(entry: PartyAllocationLedgerEntry) extends InMemoryEntry
final case class InMemoryPackageEntry(entry: PackageUploadLedgerEntry) extends InMemoryEntry

/** This stores all the mutable data that we need to run a ledger: the PCS, the ACS, and the deduplicator.
  *
  */
class InMemoryLedger(
    val ledgerId: LedgerId,
    participantId: ParticipantId,
    timeProvider: TimeProvider,
    acs0: InMemoryActiveLedgerState,
    packageStoreInit: InMemoryPackageStore,
    ledgerEntries: ImmArray[LedgerEntryOrBump])
    extends Ledger {

  private val logger = LoggerFactory.getLogger(this.getClass)

  private val entries = {
    val l = new LedgerEntries[InMemoryEntry](_.toString)
    ledgerEntries.foreach {
      case LedgerEntryOrBump.Bump(increment) =>
        l.incrementOffset(increment)
        ()
      case LedgerEntryOrBump.Entry(entry) =>
        l.publish(InMemoryLedgerEntry(entry))
        ()
    }
    l
  }

  private val packageStoreRef = new AtomicReference[InMemoryPackageStore](packageStoreInit)

  override def currentHealth(): HealthStatus = Healthy

  override def ledgerEntries(offset: Option[Long]): Source[(Long, LedgerEntry), NotUsed] =
    entries
      .getSource(offset)
      .collect { case (offset, InMemoryLedgerEntry(entry)) => offset -> entry }

  // mutable state
  private var acs = acs0
  private var deduplicator = Deduplicator()
  private var ledgerConfiguration: Option[Configuration] = None

  override def ledgerEnd: Long = entries.ledgerEnd

  // need to take the lock to make sure the two pieces of data are consistent.
  override def snapshot(filter: TemplateAwareFilter): Future[LedgerSnapshot] =
    Future.successful(this.synchronized {
      LedgerSnapshot(
        entries.ledgerEnd,
        Source.fromIterator[ActiveContract](() => acs.activeContracts.valuesIterator))
    })

  override def lookupContract(
      contractId: AbsoluteContractId,
      forParty: Party): Future[Option[ActiveLedgerState.Contract]] =
    Future.successful(this.synchronized {
      acs.activeContracts.get(contractId).filter(ac => isVisibleFor(ac.id, forParty))
    })

  private def isVisibleFor(contractId: AbsoluteContractId, forParty: Party): Boolean =
    acs.activeContracts
      .get(contractId)
      .exists(ac => ac.witnesses.contains(forParty) || ac.divulgences.contains(forParty))

  override def lookupKey(key: Node.GlobalKey, forParty: Party): Future[Option[AbsoluteContractId]] =
    Future.successful(this.synchronized {
      acs.keys.get(key).filter(isVisibleFor(_, forParty))
    })

  override def publishHeartbeat(time: Instant): Future[Unit] =
    Future.successful(this.synchronized[Unit] {
      entries.publish(InMemoryLedgerEntry(Checkpoint(time)))
      ()
    })

  override def publishTransaction(
      submitterInfo: SubmitterInfo,
      transactionMeta: TransactionMeta,
      transaction: SubmittedTransaction): Future[SubmissionResult] =
    Future.successful(
      this.synchronized[SubmissionResult] {
        val (newDeduplicator, isDuplicate) =
          deduplicator.checkAndAdd(
            submitterInfo.submitter,
            ApplicationId(submitterInfo.applicationId),
            CommandId(submitterInfo.commandId))
        deduplicator = newDeduplicator
        if (isDuplicate)
          logger.warn(
            "Ignoring duplicate submission for applicationId {}, commandId {}",
            submitterInfo.applicationId: Any,
            submitterInfo.commandId)
        else
          handleSuccessfulTx(entries.toTransactionId, submitterInfo, transactionMeta, transaction)

        SubmissionResult.Acknowledged
      }
    )

  private def handleSuccessfulTx(
      trId: TransactionIdString,
      submitterInfo: SubmitterInfo,
      transactionMeta: TransactionMeta,
      transaction: SubmittedTransaction): Unit = {
    val recordTime = timeProvider.getCurrentTime
    if (recordTime.isAfter(submitterInfo.maxRecordTime.toInstant)) {
      // This can happen if the DAML-LF computation (i.e. exercise of a choice) takes longer
      // than the time window between LET and MRT allows for.
      // See https://github.com/digital-asset/daml/issues/987
      handleError(
        submitterInfo,
        RejectionReason.TimedOut(
          s"RecordTime $recordTime is after MaxiumRecordTime ${submitterInfo.maxRecordTime}"))
    } else {
      val toAbsCoid: ContractId => AbsoluteContractId =
        SandboxEventIdFormatter.makeAbsCoid(trId)

      val blindingInfo = Blinding.blind(transaction)
      val mappedDisclosure = blindingInfo.disclosure.map {
        case (nodeId, v) => SandboxEventIdFormatter.fromTransactionId(trId, nodeId) -> v
      }
      val mappedLocalDivulgence = blindingInfo.localDivulgence.map {
        case (nodeId, v) => SandboxEventIdFormatter.fromTransactionId(trId, nodeId) -> v
      }
      val mappedGlobalDivulgence = blindingInfo.globalDivulgence

      val mappedTx = transaction
        .mapContractIdAndValue(toAbsCoid, _.mapContractId(toAbsCoid))
        .mapNodeId(SandboxEventIdFormatter.fromTransactionId(trId, _))
      // 5b. modify the ActiveContracts, while checking that we do not have double
      // spends or timing issues
      val acsRes = acs.addTransaction(
        transactionMeta.ledgerEffectiveTime.toInstant,
        trId,
        transactionMeta.workflowId,
        mappedTx,
        mappedDisclosure,
        mappedLocalDivulgence,
        mappedGlobalDivulgence,
        List.empty
      )
      acsRes match {
        case Left(err) =>
          handleError(
            submitterInfo,
            RejectionReason.Inconsistent(s"Reason: ${err.mkString("[", ", ", "]")}"))
        case Right(newAcs) =>
          acs = newAcs
          val recordBlinding =
            blindingInfo.disclosure.map {
              case (nid, parties) =>
                (SandboxEventIdFormatter.fromTransactionId(trId, nid), parties)
            }
          val entry = LedgerEntry
            .Transaction(
              Some(submitterInfo.commandId),
              trId,
              Some(submitterInfo.applicationId),
              Some(submitterInfo.submitter),
              transactionMeta.workflowId,
              transactionMeta.ledgerEffectiveTime.toInstant,
              recordTime,
              mappedTx,
              recordBlinding
            )
          entries.publish(InMemoryLedgerEntry(entry))
          ()
      }
    }

  }

  private def handleError(submitterInfo: SubmitterInfo, reason: RejectionReason): Unit = {
    logger.warn(s"Publishing error to ledger: ${reason.description}")
    entries.publish(
      InMemoryLedgerEntry(
        Rejection(
          timeProvider.getCurrentTime,
          submitterInfo.commandId,
          submitterInfo.applicationId,
          submitterInfo.submitter,
          reason)
      )
    )
    ()
  }

  override def close(): Unit = ()

  override def lookupTransaction(
      transactionId: TransactionIdString): Future[Option[(Long, LedgerEntry.Transaction)]] = {

    Try(transactionId.toLong) match {
      case Failure(_) =>
        Future.successful(None)
      case Success(n) =>
        Future.successful(
          entries
            .getEntryAt(n)
            .collect {
              case InMemoryLedgerEntry(t: LedgerEntry.Transaction) =>
                (n, t) // the transaction id is also the offset
            })
    }
  }

  override def parties: Future[List[PartyDetails]] =
    Future.successful(this.synchronized {
      acs.parties.values.toList
    })

  override def allocateParty(
      party: Party,
      displayName: Option[String],
      submissionId: SubmissionId,
      participantId: ParticipantId): Future[SubmissionResult] =
    Future.successful(this.synchronized {
      val ids = acs.parties.keySet

      if (ids.contains(party)) {
        entries.publish(
          InMemoryPartyEntry(
            PartyAllocationLedgerEntry
              .Rejected(
                submissionId,
                participantId,
                timeProvider.getCurrentTime,
                s"Party $party already exists"))
        )
        SubmissionResult.Acknowledged
      } else {
        val details = PartyDetails(party, displayName, isLocal = true)
        acs = acs.addParty(details)
        entries.publish(
          InMemoryPartyEntry(PartyAllocationLedgerEntry
            .Accepted(submissionId, participantId, timeProvider.getCurrentTime, details)))
        SubmissionResult.Acknowledged
      }
    })

  override def listLfPackages(): Future[Map[PackageId, PackageDetails]] =
    packageStoreRef.get.listLfPackages()

  override def getLfArchive(packageId: PackageId): Future[Option[Archive]] =
    packageStoreRef.get.getLfArchive(packageId)

  override def getLfPackage(packageId: PackageId): Future[Option[Ast.Package]] =
    packageStoreRef.get.getLfPackage(packageId)

  override def lookupPackageUploadEntry(
      submissionId: SubmissionId): Future[Option[PackageUploadLedgerEntry]] =
    Future.successful {
      entries.getItems
        .collectFirst {
          case (_, InMemoryPackageEntry(entry)) if entry.submissionId == submissionId => entry
        }
    }

  override def uploadPackages(
      knownSince: Instant,
      sourceDescription: Option[String],
      payload: List[Archive],
      submissionId: SubmissionId,
      participantId: ParticipantId): Future[SubmissionResult] = {
    val recordTime = timeProvider.getCurrentTime
    val oldStore = packageStoreRef.get
    oldStore
      .withPackages(knownSince, sourceDescription, payload)
      .fold(
        err => {
          entries.publish(
            InMemoryPackageEntry(
              PackageUploadLedgerEntry.Rejected(submissionId, participantId, recordTime, err)))
          Future.successful(SubmissionResult.InternalError(err))
        },
        newStore => {
          if (packageStoreRef.compareAndSet(oldStore, newStore)) {
            entries.publish(
              InMemoryPackageEntry(
                PackageUploadLedgerEntry.Accepted(submissionId, participantId, recordTime)))
            Future.successful(SubmissionResult.Acknowledged)
          } else uploadPackages(knownSince, sourceDescription, payload, submissionId, participantId)
        }
      )
  }

  override def lookupPartyAllocationEntry(
      submissionId: SubmissionId): Future[Option[PartyAllocationLedgerEntry]] =
    Future.successful {
      entries.getItems
        .collectFirst {
          case (_, InMemoryPartyEntry(entry)) if entry.submissionId == submissionId => entry
        }
    }

  override def publishConfiguration(
      maxRecordTime: Time.Timestamp,
      submissionId: SubmissionId,
      config: Configuration): Future[SubmissionResult] =
    Future.successful {
      this.synchronized {
        ledgerConfiguration match {
          case Some(currentConfig) if config.generation != currentConfig.generation =>
            entries.publish(InMemoryConfigEntry(ConfigurationEntry.Rejected(
              submissionId,
              participantId,
              "Generation mismatch, expected ${currentConfig.generation}, got ${config.generation}",
              config)))

          case _ =>
            entries.publish(
              InMemoryConfigEntry(ConfigurationEntry.Accepted(submissionId, participantId, config)))
            ledgerConfiguration = Some(config)
        }
        SubmissionResult.Acknowledged
      }
    }

  override def lookupLedgerConfiguration(): Future[Option[Configuration]] =
    Future.successful(this.synchronized { ledgerConfiguration })

  override def configurationEntries(
      offset: Option[Long]): Source[(Long, ConfigurationEntry), NotUsed] =
    entries
      .getSource(offset)
      .collect { case (offset, InMemoryConfigEntry(entry)) => offset -> entry }

}
