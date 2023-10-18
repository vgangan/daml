// Copyright (c) 2023 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.canton.participant.protocol.transfer

import cats.Eval
import cats.implicits.*
import com.daml.nonempty.{NonEmpty, NonEmptyUtil}
import com.digitalasset.canton.concurrent.FutureSupervisor
import com.digitalasset.canton.config.DefaultProcessingTimeouts
import com.digitalasset.canton.crypto.provider.symbolic.SymbolicCrypto
import com.digitalasset.canton.crypto.{DomainSnapshotSyncCryptoApi, HashPurpose}
import com.digitalasset.canton.data.ViewType.TransferOutViewType
import com.digitalasset.canton.data.{
  CantonTimestamp,
  FullTransferOutTree,
  TransferSubmitterMetadata,
}
import com.digitalasset.canton.lifecycle.FutureUnlessShutdown
import com.digitalasset.canton.participant.metrics.ParticipantTestMetrics
import com.digitalasset.canton.participant.protocol.ProcessingStartingPoints
import com.digitalasset.canton.participant.protocol.conflictdetection.ConflictDetectionHelpers.{
  mkActivenessResult,
  mkActivenessSet,
}
import com.digitalasset.canton.participant.protocol.submission.{
  EncryptedViewMessageFactory,
  InFlightSubmissionTracker,
  SeedGenerator,
}
import com.digitalasset.canton.participant.protocol.transfer.TransferOutProcessingSteps.PendingTransferOut
import com.digitalasset.canton.participant.protocol.transfer.TransferOutProcessorError.*
import com.digitalasset.canton.participant.protocol.transfer.TransferProcessingSteps.{
  IncompatibleProtocolVersions,
  NoTransferSubmissionPermission,
  TransferProcessorError,
}
import com.digitalasset.canton.participant.store.memory.*
import com.digitalasset.canton.participant.store.{MultiDomainEventLog, SyncDomainEphemeralState}
import com.digitalasset.canton.participant.util.TimeOfChange
import com.digitalasset.canton.protocol.*
import com.digitalasset.canton.protocol.messages.*
import com.digitalasset.canton.sequencing.protocol.*
import com.digitalasset.canton.store.IndexedDomain
import com.digitalasset.canton.time.{DomainTimeTracker, TimeProofTestUtil}
import com.digitalasset.canton.topology.*
import com.digitalasset.canton.topology.client.TopologySnapshot
import com.digitalasset.canton.topology.transaction.ParticipantPermission.{
  Confirmation,
  Observation,
  Submission,
}
import com.digitalasset.canton.topology.transaction.{ParticipantPermission, VettedPackages}
import com.digitalasset.canton.tracing.TraceContext
import com.digitalasset.canton.version.Transfer.{SourceProtocolVersion, TargetProtocolVersion}
import com.digitalasset.canton.version.{HasTestCloseContext, ProtocolVersion}
import com.digitalasset.canton.{
  BaseTest,
  HasExecutorService,
  LedgerApplicationId,
  LedgerCommandId,
  LedgerTransactionId,
  LfPackageId,
  LfPartyId,
  RequestCounter,
  SequencerCounter,
  TransferCounter,
  TransferCounterO,
}
import com.google.protobuf.ByteString
import org.scalatest.Assertion
import org.scalatest.wordspec.AsyncWordSpec

import java.util.UUID
import scala.annotation.nowarn
import scala.concurrent.{ExecutionContext, Future}

@nowarn("msg=match may not be exhaustive")
final class TransferOutProcessingStepsTest
    extends AsyncWordSpec
    with BaseTest
    with HasExecutorService
    with HasTestCloseContext {

  private implicit val ec: ExecutionContext = executorService

  private val sourceDomain = SourceDomainId(
    DomainId(UniqueIdentifier.tryFromProtoPrimitive("source::domain"))
  )
  private val sourceMediator = MediatorRef(
    MediatorId(UniqueIdentifier.tryFromProtoPrimitive("source::mediator"))
  )
  private val targetDomain = TargetDomainId(
    DomainId(UniqueIdentifier.tryFromProtoPrimitive("target::domain"))
  )

  private val submitter: LfPartyId = PartyId(
    UniqueIdentifier.tryFromProtoPrimitive("submitter::party")
  ).toLf
  private val party1: LfPartyId = PartyId(
    UniqueIdentifier.tryFromProtoPrimitive("party1::party")
  ).toLf
  private val party2: LfPartyId = PartyId(
    UniqueIdentifier.tryFromProtoPrimitive("party2::party")
  ).toLf

  private val submittingParticipant = ParticipantId(
    UniqueIdentifier.tryFromProtoPrimitive("submitting::participant")
  )

  private val templateId =
    LfTemplateId.assertFromString("transferoutprocessingstepstestpackage:template:id")

  private val initialTransferCounter: TransferCounterO =
    TransferCounter.forCreatedContract(testedProtocolVersion)

  private def submitterMetadata(submitter: LfPartyId): TransferSubmitterMetadata = {
    TransferSubmitterMetadata(
      submitter,
      LedgerApplicationId.assertFromString("tests"),
      submittingParticipant.toLf,
      LedgerCommandId.assertFromString("transfer-out-processing-steps-command-id"),
      submissionId = None,
      workflowId = None,
    )
  }

  private val adminSubmitter: LfPartyId = submittingParticipant.adminParty.toLf

  private val pureCrypto = TestingIdentityFactory.pureCrypto()

  private val multiDomainEventLog = mock[MultiDomainEventLog]
  private val persistentState =
    new InMemorySyncDomainPersistentStateOld(
      IndexedDomain.tryCreate(sourceDomain.unwrap, 1),
      testedProtocolVersion,
      pureCrypto,
      enableAdditionalConsistencyChecks = true,
      loggerFactory,
      timeouts,
      futureSupervisor,
    )

  private def mkState: SyncDomainEphemeralState =
    new SyncDomainEphemeralState(
      submittingParticipant,
      persistentState,
      Eval.now(multiDomainEventLog),
      mock[InFlightSubmissionTracker],
      ProcessingStartingPoints.default,
      _ => mock[DomainTimeTracker],
      ParticipantTestMetrics.domain,
      DefaultProcessingTimeouts.testing,
      loggerFactory,
      FutureSupervisor.Noop,
    )

  private val damle =
    DAMLeTestInstance(submittingParticipant, signatories = Set(party1), stakeholders = Set(party1))(
      loggerFactory
    )

  private def createTestingIdentityFactory(
      topology: Map[ParticipantId, Map[LfPartyId, ParticipantPermission]],
      packages: Seq[VettedPackages] = Seq.empty,
      domains: Set[DomainId] = Set(DefaultTestIdentities.domainId),
  ) =
    TestingTopology(domains)
      .withReversedTopology(topology)
      .withPackages(packages)
      .build(loggerFactory)

  private def vet(
      participants: Iterable[ParticipantId],
      packages: Seq[LfPackageId],
  ): Seq[VettedPackages] =
    participants.view.map(VettedPackages(_, packages)).toSeq

  private def createTestingTopologySnapshot(
      topology: Map[ParticipantId, Map[LfPartyId, ParticipantPermission]],
      packages: Seq[LfPackageId] = Seq.empty,
  ): TopologySnapshot =
    createTestingIdentityFactory(topology, vet(topology.keys, packages)).topologySnapshot()

  private def createCryptoFactory(packages: Seq[LfPackageId] = Seq(templateId.packageId)) = {
    val topology = Map(
      submittingParticipant -> Map(
        party1 -> ParticipantPermission.Submission,
        submittingParticipant.adminParty.toLf -> ParticipantPermission.Submission,
      )
    )
    createTestingIdentityFactory(
      topology = topology,
      packages = vet(topology.keys, packages),
      domains = Set(sourceDomain.unwrap, targetDomain.unwrap),
    )
  }

  private val cryptoFactory = createCryptoFactory()

  private def createCryptoSnapshot(testingIdentityFactory: TestingIdentityFactory = cryptoFactory) =
    testingIdentityFactory
      .forOwnerAndDomain(submittingParticipant, sourceDomain.unwrap)
      .currentSnapshotApproximation

  private val cryptoSnapshot = createCryptoSnapshot()

  private val seedGenerator = new SeedGenerator(pureCrypto)

  private val cantonContractIdVersion =
    CantonContractIdVersion.fromProtocolVersion(testedProtocolVersion)

  private def createTransferCoordination(
      cryptoSnapshot: DomainSnapshotSyncCryptoApi = cryptoSnapshot
  ) =
    TestTransferCoordination(
      Set(TargetDomainId(sourceDomain.unwrap), targetDomain),
      CantonTimestamp.Epoch,
      Some(cryptoSnapshot),
      Some(None),
      loggerFactory,
      Seq(templateId.packageId),
    )(directExecutionContext)

  private val coordination: TransferCoordination =
    createTransferCoordination()

  private def createOutProcessingSteps(transferCoordination: TransferCoordination = coordination) =
    new TransferOutProcessingSteps(
      sourceDomain,
      submittingParticipant,
      damle,
      transferCoordination,
      seedGenerator,
      SourceProtocolVersion(testedProtocolVersion),
      loggerFactory,
    )(executorService)

  private val outProcessingSteps: TransferOutProcessingSteps = createOutProcessingSteps()

  private val Seq(
    (participant1, admin1),
    (participant2, _),
    (participant3, admin3),
    (participant4, admin4),
  ) =
    (1 to 4).map { i =>
      val participant =
        ParticipantId(UniqueIdentifier.tryFromProtoPrimitive(s"participant$i::participant"))
      val admin = participant.adminParty.toLf
      participant -> admin
    }

  private val timeEvent =
    TimeProofTestUtil.mkTimeProof(timestamp = CantonTimestamp.Epoch, targetDomain = targetDomain)

  "TransferOutRequest.validated" should {
    val testingTopology = createTestingTopologySnapshot(
      topology = Map(
        submittingParticipant -> Map(submitter -> Submission),
        participant1 -> Map(party1 -> Submission),
        participant2 -> Map(party2 -> Submission),
      ),
      packages = Seq(templateId.packageId),
    )

    val contractId = cantonContractIdVersion.fromDiscriminator(
      ExampleTransactionFactory.lfHash(10),
      Unicum(pureCrypto.digest(HashPurpose.MerkleTreeInnerNode, ByteString.copyFromUtf8("unicum"))),
    )

    def mkTxOutRes(
        stakeholders: Set[LfPartyId],
        sourceTopologySnapshot: TopologySnapshot,
        targetTopologySnapshot: TopologySnapshot,
    ): Either[TransferProcessorError, TransferOutRequestValidated] =
      TransferOutRequest
        .validated(
          submittingParticipant,
          timeEvent,
          contractId,
          templateId,
          submitterMetadata(submitter),
          stakeholders,
          sourceDomain,
          SourceProtocolVersion(testedProtocolVersion),
          sourceMediator,
          targetDomain,
          TargetProtocolVersion(testedProtocolVersion),
          sourceTopologySnapshot,
          targetTopologySnapshot,
          initialTransferCounter,
          logger,
        )
        .value
        .failOnShutdown
        .futureValue

    "fail if submitter is not a stakeholder" in {
      val stakeholders = Set(party1, party2)
      val result = mkTxOutRes(stakeholders, testingTopology, testingTopology)
      result.left.value shouldBe a[SubmittingPartyMustBeStakeholderOut]
    }

    "fail if submitting participant does not have submission permission" in {
      val ipsNoSubmissionPermission =
        createTestingTopologySnapshot(Map(submittingParticipant -> Map(submitter -> Confirmation)))

      val result = mkTxOutRes(Set(submitter), ipsNoSubmissionPermission, testingTopology)
      result.left.value shouldBe a[NoTransferSubmissionPermission]
    }

    "fail if a stakeholder cannot submit on target domain" in {
      val ipsNoSubmissionOnTarget = createTestingTopologySnapshot(
        Map(
          submittingParticipant -> Map(submitter -> Submission),
          participant1 -> Map(party1 -> Confirmation),
        )
      )

      val stakeholders = Set(submitter, party1)
      val result = mkTxOutRes(stakeholders, testingTopology, ipsNoSubmissionOnTarget)
      result.left.value shouldBe a[PermissionErrors]
    }

    "fail if a stakeholder cannot confirm on target domain" in {
      val ipsConfirmationOnSource = createTestingTopologySnapshot(
        Map(
          submittingParticipant -> Map(submitter -> Submission),
          participant1 -> Map(party1 -> Confirmation),
        )
      )

      val ipsNoConfirmationOnTarget = createTestingTopologySnapshot(
        Map(
          submittingParticipant -> Map(submitter -> Submission),
          participant1 -> Map(party1 -> Observation),
        )
      )

      val stakeholders = Set(submitter, party1)
      val result = mkTxOutRes(stakeholders, ipsConfirmationOnSource, ipsNoConfirmationOnTarget)
      result.left.value shouldBe a[PermissionErrors]
    }

    "fail if a stakeholder is not hosted on the same participant on both domains" in {
      val ipsDifferentParticipant = createTestingTopologySnapshot(
        Map(
          submittingParticipant -> Map(submitter -> Submission),
          participant1 -> Map(party1 -> Confirmation),
          participant2 -> Map(party1 -> Submission),
        )
      )

      val stakeholders = Set(submitter, party1)
      val result = mkTxOutRes(stakeholders, testingTopology, ipsDifferentParticipant)
      result.left.value shouldBe a[PermissionErrors]
    }

    "fail if participant cannot confirm for admin party" in {
      val ipsAdminNoConfirmation = createTestingTopologySnapshot(
        Map(
          submittingParticipant -> Map(adminSubmitter -> Submission, submitter -> Submission),
          participant1 -> Map(party1 -> Observation),
        )
      )
      val result =
        loggerFactory.suppressWarningsAndErrors(
          mkTxOutRes(Set(submitter, party1), ipsAdminNoConfirmation, testingTopology)
        )
      result.left.value shouldBe a[PermissionErrors]
    }

    // TODO(i13201) This should ideally be covered in integration tests as well
    "fail if the package for the contract being transferred is unvetted on the target domain" in {

      val sourceDomainTopology =
        createTestingTopologySnapshot(
          topology = Map(
            submittingParticipant -> Map(submitter -> Submission),
            participant1 -> Map(party1 -> Submission),
          ),
          packages = Seq(templateId.packageId), // The package is known on the source domain
        )

      val targetDomainTopology =
        createTestingTopologySnapshot(
          topology = Map(
            submittingParticipant -> Map(submitter -> Submission),
            participant1 -> Map(party1 -> Submission),
          ),
          packages = Seq.empty, // The package is not known on the target domain
        )

      val result =
        mkTxOutRes(
          stakeholders = Set(submitter, adminSubmitter, admin1),
          sourceTopologySnapshot = sourceDomainTopology,
          targetTopologySnapshot = targetDomainTopology,
        )

      result.left.value shouldBe a[PackageIdUnknownOrUnvetted]
    }

    "fail if the package for the contract being transferred is unvetted on one non-transferring participant connected to the target domain" in {

      val sourceDomainTopology =
        createTestingIdentityFactory(
          topology = Map(
            submittingParticipant -> Map(submitter -> Submission),
            participant1 -> Map(party1 -> Submission),
          ),
          // On the source domain, the package is vetted on all participants
          packages = Seq(
            VettedPackages(submittingParticipant, Seq(templateId.packageId)),
            VettedPackages(participant1, Seq(templateId.packageId)),
          ),
        ).topologySnapshot()

      val targetDomainTopology =
        createTestingIdentityFactory(
          topology = Map(
            submittingParticipant -> Map(submitter -> Submission),
            participant1 -> Map(party1 -> Submission),
          ),
          // On the target domain, the package is not vetted on `participant1`
          packages = Seq(
            VettedPackages(submittingParticipant, Seq(templateId.packageId))
          ),
        ).topologySnapshot()

      // `party1` is a stakeholder hosted on `participant1`, but it has not vetted `templateId.packageId` on the target domain
      val result =
        mkTxOutRes(
          stakeholders = Set(submitter, party1, adminSubmitter, admin1),
          sourceTopologySnapshot = sourceDomainTopology,
          targetTopologySnapshot = targetDomainTopology,
        )

      result.left.value shouldBe a[PackageIdUnknownOrUnvetted]

    }

    "pick the active confirming admin party" in {
      val ipsAdminNoConfirmation = createTestingTopologySnapshot(
        Map(
          submittingParticipant -> Map(adminSubmitter -> Submission, submitter -> Submission),
          participant1 -> Map(party1 -> Confirmation),
          participant2 -> Map(party1 -> Observation),
        )
      )
      val result =
        loggerFactory.suppressWarningsAndErrors(
          mkTxOutRes(Set(submitter, party1), ipsAdminNoConfirmation, testingTopology)
        )
      result.value shouldEqual
        TransferOutRequestValidated(
          TransferOutRequest(
            submitterMetadata = submitterMetadata(submitter),
            stakeholders = Set(submitter, party1),
            adminParties = Set(adminSubmitter, admin1),
            contractId = contractId,
            templateId = templateId,
            sourceDomain = sourceDomain,
            sourceProtocolVersion = SourceProtocolVersion(testedProtocolVersion),
            sourceMediator = sourceMediator,
            targetDomain = targetDomain,
            targetProtocolVersion = TargetProtocolVersion(testedProtocolVersion),
            targetTimeProof = timeEvent,
            transferCounter = initialTransferCounter,
          ),
          Set(submittingParticipant, participant1, participant2),
        )
    }

    "work if topology constraints are satisfied" in {
      val ipsSource = createTestingTopologySnapshot(
        Map(
          submittingParticipant -> Map(adminSubmitter -> Submission, submitter -> Submission),
          participant1 -> Map(adminSubmitter -> Observation, submitter -> Confirmation),
          participant2 -> Map(party1 -> Submission),
          participant3 -> Map(party1 -> Submission),
          participant4 -> Map(party1 -> Confirmation),
        ),
        packages = Seq(templateId.packageId),
      )
      val ipsTarget = createTestingTopologySnapshot(
        Map(
          submittingParticipant -> Map(submitter -> Submission),
          participant1 -> Map(submitter -> Observation),
          participant3 -> Map(party1 -> Submission),
          participant4 -> Map(party1 -> Confirmation),
        ),
        packages = Seq(templateId.packageId),
      )
      val stakeholders = Set(submitter, party1)
      val result = mkTxOutRes(stakeholders, ipsSource, ipsTarget)
      result.value shouldEqual
        TransferOutRequestValidated(
          TransferOutRequest(
            submitterMetadata = submitterMetadata(submitter),
            stakeholders = stakeholders,
            adminParties = Set(adminSubmitter, admin3, admin4),
            contractId = contractId,
            templateId = templateId,
            sourceDomain = sourceDomain,
            sourceProtocolVersion = SourceProtocolVersion(testedProtocolVersion),
            sourceMediator = sourceMediator,
            targetDomain = targetDomain,
            targetProtocolVersion = TargetProtocolVersion(testedProtocolVersion),
            targetTimeProof = timeEvent,
            transferCounter = initialTransferCounter,
          ),
          Set(submittingParticipant, participant1, participant2, participant3, participant4),
        )
    }

    "allow admin parties as stakeholders" in {
      val stakeholders = Set(submitter, adminSubmitter, admin1)
      mkTxOutRes(stakeholders, testingTopology, testingTopology) shouldBe Right(
        TransferOutRequestValidated(
          TransferOutRequest(
            submitterMetadata = submitterMetadata(submitter),
            stakeholders = stakeholders,
            adminParties = Set(adminSubmitter, admin1),
            contractId = contractId,
            templateId = templateId,
            sourceDomain = sourceDomain,
            sourceProtocolVersion = SourceProtocolVersion(testedProtocolVersion),
            sourceMediator = sourceMediator,
            targetDomain = targetDomain,
            targetProtocolVersion = TargetProtocolVersion(testedProtocolVersion),
            targetTimeProof = timeEvent,
            transferCounter = initialTransferCounter,
          ),
          Set(submittingParticipant, participant1),
        )
      )
    }
  }

  "prepare submission" should {
    "succeed without errors" in {
      val state = mkState
      val contractId = ExampleTransactionFactory.suffixedId(10, 0)
      val contract = ExampleTransactionFactory.asSerializable(
        contractId,
        contractInstance = ExampleTransactionFactory.contractInstance(templateId = templateId),
        metadata = ContractMetadata.tryCreate(
          signatories = Set(party1),
          stakeholders = Set(party1),
          maybeKeyWithMaintainers = None,
        ),
      )
      val transactionId = ExampleTransactionFactory.transactionId(1)
      val submissionParam =
        TransferOutProcessingSteps.SubmissionParam(
          submitterMetadata = submitterMetadata(party1),
          contractId,
          targetDomain,
          TargetProtocolVersion(testedProtocolVersion),
        )

      for {
        _ <- state.storedContractManager.addPendingContracts(
          RequestCounter(1),
          Seq(WithTransactionId(contract, transactionId)),
        )
        _ <- persistentState.activeContractStore
          .markContractsActive(
            Seq(contractId -> initialTransferCounter),
            TimeOfChange(RequestCounter(1), timeEvent.timestamp),
          )
          .value
        _ <-
          outProcessingSteps
            .prepareSubmission(
              submissionParam,
              sourceMediator,
              state,
              cryptoSnapshot,
            )
            .valueOrFailShutdown("prepare submission failed")
      } yield succeed
    }

    "check that the target domain is not equal to the source domain" in {
      val state = mkState
      val contractId = ExampleTransactionFactory.suffixedId(10, 0)
      val contract = ExampleTransactionFactory.asSerializable(
        contractId,
        contractInstance = ExampleTransactionFactory.contractInstance(),
      )
      val transactionId = ExampleTransactionFactory.transactionId(1)
      val submissionParam = TransferOutProcessingSteps.SubmissionParam(
        submitterMetadata = submitterMetadata(party1),
        contractId,
        TargetDomainId(sourceDomain.unwrap),
        TargetProtocolVersion(testedProtocolVersion),
      )

      for {
        _ <- state.storedContractManager.addPendingContracts(
          RequestCounter(1),
          Seq(WithTransactionId(contract, transactionId)),
        )
        submissionResult <- leftOrFailShutdown(
          outProcessingSteps.prepareSubmission(
            submissionParam,
            sourceMediator,
            state,
            cryptoSnapshot,
          )
        )("prepare submission succeeded unexpectedly")
      } yield {
        submissionResult shouldBe a[TargetDomainIsSourceDomain]
      }
    }

    "forbid transfer if the target domain does not support transfer counters and the source domain supports them" in {
      val targetProtocolVersion = TargetProtocolVersion(ProtocolVersion.v4)
      val state = mkState
      val contractId = ExampleTransactionFactory.suffixedId(10, 0)
      val contract = ExampleTransactionFactory.asSerializable(
        contractId,
        contractInstance = ExampleTransactionFactory.contractInstance(templateId = templateId),
        metadata = ContractMetadata.tryCreate(
          signatories = Set(party1),
          stakeholders = Set(party1),
          maybeKeyWithMaintainers = None,
        ),
      )
      val transactionId = ExampleTransactionFactory.transactionId(1)
      val submissionParam = TransferOutProcessingSteps.SubmissionParam(
        submitterMetadata = submitterMetadata(party1),
        contractId,
        TargetDomainId(targetDomain.id),
        targetProtocolVersion,
      )

      for {
        _ <- state.storedContractManager.addPendingContracts(
          RequestCounter(1),
          Seq(WithTransactionId(contract, transactionId)),
        )
        _ <- persistentState.activeContractStore
          .markContractsActive(
            Seq(contractId -> initialTransferCounter),
            TimeOfChange(RequestCounter(1), timeEvent.timestamp),
          )
          .value
        submissionResult <-
          outProcessingSteps
            .prepareSubmission(
              submissionParam,
              sourceMediator,
              state,
              cryptoSnapshot,
            )
            .value
            .failOnShutdown
      } yield {
        if (outProcessingSteps.sourceDomainProtocolVersion.v >= ProtocolVersion.CNTestNet) {
          submissionResult shouldBe Left(
            IncompatibleProtocolVersions(
              contractId,
              outProcessingSteps.sourceDomainProtocolVersion,
              targetProtocolVersion,
            )
          )
        } else {
          succeed
        }

      }
    }
  }

  "receive request" should {
    val contractId = ExampleTransactionFactory.suffixedId(10, 0)
    val outRequest = TransferOutRequest(
      submitterMetadata = submitterMetadata(party1),
      Set(party1),
      Set(party1),
      contractId,
      templateId = templateId,
      sourceDomain,
      SourceProtocolVersion(testedProtocolVersion),
      sourceMediator,
      targetDomain,
      TargetProtocolVersion(testedProtocolVersion),
      timeEvent,
      transferCounter = initialTransferCounter,
    )
    val outTree = makeFullTransferOutTree(outRequest)

    val encryptedOutRequestF = for {
      encrypted <- encryptTransferOutTree(outTree)
    } yield encrypted

    def checkSuccessful(
        result: outProcessingSteps.CheckActivenessAndWritePendingContracts
    ): Assertion =
      result match {
        case outProcessingSteps.CheckActivenessAndWritePendingContracts(
              activenessSet,
              pendingContracts,
              _,
            ) =>
          activenessSet shouldBe mkActivenessSet(deact = Set(contractId), prior = Set(contractId))
          pendingContracts shouldBe Seq.empty
        case _ => fail()
      }

    "succeed without errors" in {
      for {
        encryptedOutRequest <- encryptedOutRequestF
        envelopes =
          NonEmpty(
            Seq,
            OpenEnvelope(encryptedOutRequest, RecipientsTest.testInstance)(testedProtocolVersion),
          )
        decrypted <- valueOrFail(outProcessingSteps.decryptViews(envelopes, cryptoSnapshot))(
          "decrypt request failed"
        )
        result <- valueOrFail(
          outProcessingSteps.computeActivenessSetAndPendingContracts(
            CantonTimestamp.Epoch,
            RequestCounter(1),
            SequencerCounter(1),
            NonEmptyUtil.fromUnsafe(decrypted.views),
            Seq.empty,
            cryptoSnapshot,
            MediatorRef(MediatorId(UniqueIdentifier.tryCreate("another", "mediator"))),
          )
        )("compute activeness set failed")
      } yield {
        decrypted.decryptionErrors shouldBe Seq.empty
        checkSuccessful(result)
      }
    }
  }

  "construct pending data and response" should {

    def constructPendingDataAndResponseWith(
        transferOutProcessingSteps: TransferOutProcessingSteps
    ) = {
      val state = mkState
      val contractId = ExampleTransactionFactory.suffixedId(10, 0)
      val metadata = ContractMetadata.tryCreate(Set.empty, Set(party1), None)
      val contract = ExampleTransactionFactory.asSerializable(
        contractId,
        contractInstance = ExampleTransactionFactory.contractInstance(templateId = templateId),
        metadata = metadata,
      )
      val transactionId = ExampleTransactionFactory.transactionId(1)
      val outRequest = TransferOutRequest(
        submitterMetadata = submitterMetadata(party1),
        Set(party1),
        Set(submittingParticipant.adminParty.toLf),
        contractId,
        templateId = templateId,
        sourceDomain,
        SourceProtocolVersion(testedProtocolVersion),
        sourceMediator,
        targetDomain,
        TargetProtocolVersion(testedProtocolVersion),
        timeEvent,
        transferCounter = initialTransferCounter,
      )
      val fullTransferOutTree = makeFullTransferOutTree(outRequest)
      val dataAndResponseArgs = TransferOutProcessingSteps.PendingDataAndResponseArgs(
        fullTransferOutTree,
        Recipients.cc(submittingParticipant),
        CantonTimestamp.Epoch,
        RequestCounter(1),
        SequencerCounter(1),
        cryptoSnapshot,
      )

      state.storedContractManager
        .addPendingContracts(
          RequestCounter(1),
          Seq(WithTransactionId(contract, transactionId)),
        )
        .futureValue
        .discard

      transferOutProcessingSteps
        .constructPendingDataAndResponse(
          dataAndResponseArgs,
          state.transferCache,
          state.storedContractManager,
          FutureUnlessShutdown.pure(mkActivenessResult()),
          Future.unit,
          sourceMediator,
          freshOwnTimelyTx = true,
        )
        .value
        .onShutdown(fail("unexpected shutdown during a test"))
        .futureValue
    }

    "succeed without errors" in {
      constructPendingDataAndResponseWith(outProcessingSteps).valueOrFail(
        "construction of pending data and response failed"
      )
      succeed
    }

    // TODO(i13201) This should ideally be covered in integration tests as well
    "prevent the contract being transferred is not vetted on the target domain since version 5" in {
      val outProcessingStepsWithoutPackages = {
        val f = createCryptoFactory(packages = Seq.empty)
        val s = createCryptoSnapshot(f)
        val c = createTransferCoordination(s)
        createOutProcessingSteps(c)
      }

      if (testedProtocolVersion >= ProtocolVersion.v5) {
        constructPendingDataAndResponseWith(outProcessingStepsWithoutPackages).leftOrFail(
          "construction of pending data and response succeeded unexpectedly"
        ) shouldBe a[PackageIdUnknownOrUnvetted]
      } else {
        constructPendingDataAndResponseWith(outProcessingStepsWithoutPackages).valueOrFail(
          "construction of pending data and response failed"
        )
        succeed
      }

    }
  }

  "get commit set and contracts to be stored and event" should {
    "succeed without errors" in {
      val state = mkState
      val contractId = ExampleTransactionFactory.suffixedId(10, 0)
      val contractHash = ExampleTransactionFactory.lfHash(0)
      val transferId = TransferId(sourceDomain, CantonTimestamp.Epoch)
      val rootHash = mock[RootHash]
      when(rootHash.asLedgerTransactionId).thenReturn(LedgerTransactionId.fromString("id1"))
      val transferResult =
        TransferResult.create(
          RequestId(CantonTimestamp.Epoch),
          Set(),
          sourceDomain,
          Verdict.Approve(testedProtocolVersion),
          testedProtocolVersion,
        )

      val domainParameters = DynamicDomainParametersWithValidity(
        DynamicDomainParameters.defaultValues(testedProtocolVersion),
        CantonTimestamp.MinValue,
        None,
        targetDomain.unwrap,
      )

      for {
        signedResult <- SignedProtocolMessage.trySignAndCreate(
          transferResult,
          cryptoSnapshot,
          testedProtocolVersion,
        )
        deliver: Deliver[OpenEnvelope[SignedProtocolMessage[TransferOutResult]]] = {
          val batch: Batch[OpenEnvelope[SignedProtocolMessage[TransferOutResult]]] =
            Batch.of(testedProtocolVersion, (signedResult, Recipients.cc(submittingParticipant)))
          Deliver.create(
            SequencerCounter(0),
            CantonTimestamp.Epoch,
            sourceDomain.unwrap,
            Some(MessageId.tryCreate("msg-0")),
            batch,
            testedProtocolVersion,
          )
        }
        signedContent = SignedContent(
          deliver,
          SymbolicCrypto.emptySignature,
          None,
          testedProtocolVersion,
        )
        transferInExclusivity = domainParameters
          .transferExclusivityLimitFor(timeEvent.timestamp)
          .value
        pendingOut = PendingTransferOut(
          RequestId(CantonTimestamp.Epoch),
          RequestCounter(1),
          SequencerCounter(1),
          rootHash,
          WithContractHash(contractId, contractHash),
          initialTransferCounter,
          templateId = templateId,
          transferringParticipant = false,
          submitterMetadata = submitterMetadata(submitter),
          transferId,
          targetDomain,
          Set(party1),
          Set(party1),
          timeEvent,
          Some(transferInExclusivity),
          MediatorRef(MediatorId(UniqueIdentifier.tryCreate("another", "mediator"))),
        )
        _ <- valueOrFail(
          outProcessingSteps
            .getCommitSetAndContractsToBeStoredAndEvent(
              Right(signedContent),
              Right(transferResult),
              pendingOut,
              state.pendingTransferOutSubmissions,
              pureCrypto,
            )
        )("get commit set and contract to be stored and event")
      } yield succeed
    }
  }

  def makeFullTransferOutTree(
      request: TransferOutRequest,
      uuid: UUID = new UUID(6L, 7L),
  ): FullTransferOutTree = {
    val seed = seedGenerator.generateSaltSeed()
    valueOrFail(request.toFullTransferOutTree(pureCrypto, pureCrypto, seed, uuid))(
      "Failed to create fullTransferOutTree"
    )
    request.toFullTransferOutTree(pureCrypto, pureCrypto, seed, uuid).value
  }

  def encryptTransferOutTree(
      tree: FullTransferOutTree
  ): Future[EncryptedViewMessage[TransferOutViewType]] =
    EncryptedViewMessageFactory
      .create(TransferOutViewType)(tree, cryptoSnapshot, testedProtocolVersion)(
        implicitly[TraceContext],
        executorService,
      )
      .fold(error => fail(s"Failed to encrypt transfer-out request: $error"), Predef.identity)

  def makeRootHashMessage(
      request: FullTransferOutTree
  ): RootHashMessage[SerializedRootHashMessagePayload] =
    RootHashMessage(
      request.rootHash,
      sourceDomain.unwrap,
      testedProtocolVersion,
      TransferOutViewType,
      SerializedRootHashMessagePayload.empty,
    )
}