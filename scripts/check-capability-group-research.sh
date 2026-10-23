#!/usr/bin/env sh
set -eu

# Research results are checked separately from the production certificate list.
lake build \
  Sal.MRDTs.Instances.CapabilityGroupSPOT \
  Sal.MRDTs.Instances.CapabilityGroupOwnerOrder \
  Sal.MRDTs.Paper1.CapabilityGroupBridge
