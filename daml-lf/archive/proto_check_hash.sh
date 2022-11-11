#!/usr/bin/env bash
# Copyright (c) 2022 Digital Asset (Switzerland) GmbH and/or its affiliates. All rights reserved.
# SPDX-License-Identifier: Apache-2.0


set -e

declare -a checkSums=(
 "500eefd480e9af6940adf12e7ec4c2cf4975d4cb9b25096c15edb0d57d364de8  daml-lf/archive/src/stable/protobuf/com/daml/daml_lf_1_14/daml_lf_1.proto"
 "22e549209116e91d8073a255e6d868be60515824c321015cc424f0b83634f199  daml-lf/archive/src/stable/protobuf/com/daml/daml_lf_1_14/daml_lf.proto"
 "b7e6ebf85f99d506c1b9b08ccf9543ac24c3d39ce8ba4583b0d8c1b97e979032  daml-lf/archive/src/stable/protobuf/com/daml/daml_lf_1_15/daml_lf_1.proto"
 "5e6e33e885e80384fcfde6ac5072b7d6a2e2582430a6a449f96cb06d48a0edbf  daml-lf/archive/src/stable/protobuf/com/daml/daml_lf_1_15/daml_lf.proto"
)

for checkSum in "${checkSums[@]}"; do
  echo ${checkSum} | sha256sum -c
done
