// Copyright (c) 2022 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.test.evidence.generator

import better.files.File
import com.daml.test.evidence.generator.TestEntry.{ReliabilityTestEntry, SecurityTestEntry}
import com.daml.test.evidence.tag.Reliability.{ReliabilityTest, ReliabilityTestSuite}
import com.daml.test.evidence.tag.Security.{SecurityTest, SecurityTestSuite}
import io.circe.Encoder
import io.circe.generic.auto._
import io.circe.syntax._
import org.scalatest.Suite
import com.daml.test.evidence.scalatest.JsonCodec.SecurityJson._
import com.daml.test.evidence.scalatest.JsonCodec.ReliabilityJson._
import org.scalatest.daml.ScalaTestAdapter

import scala.reflect.ClassTag

object Main {

  private def loadClasspath(): Option[String] = Some(System.getProperty("java.class.path"))

  private def writeEvidenceToFile[TE: Encoder](fileName: String, entries: List[TE]): Unit = {
    println(s"Writing inventory to $fileName...")
    val path = File(fileName)
      .write(entries.asJson.spaces2)
      .path
      .toAbsolutePath
      .toString
    println(s"Wrote to $path")
  }

  private def collectTestEvidence[TT: ClassTag, TS: ClassTag, TE](
      scalaTestSuites: List[Suite],
      testEntry: (String, String, TT, Boolean, Option[TS]) => TE,
  ): List[TE] =
    ScalaTestGeneratorSupport
      .testEntries[TT, TS, TE](scalaTestSuites, testEntry)

  def main(args: Array[String]): Unit = {
    val runpathList: List[String] = loadClasspath()
      .map(_.split(":").toList)
      .getOrElse(List.empty)

    val testSuites: List[Suite] = ScalaTestAdapter.loadTestSuites(runpathList)

    println("Writing security tests inventory..")

    val securityTestEntries =
      collectTestEvidence[SecurityTest, SecurityTestSuite, SecurityTestEntry](
        testSuites,
        SecurityTestEntry,
      )

    val reliabilityTestEntries =
      collectTestEvidence[ReliabilityTest, ReliabilityTestSuite, ReliabilityTestEntry](
        testSuites,
        ReliabilityTestEntry,
      )

    writeEvidenceToFile("security-tests.json", securityTestEntries)

    writeEvidenceToFile("reliability-tests.json", reliabilityTestEntries)

    sys.exit()
  }
}
