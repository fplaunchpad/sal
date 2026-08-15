#!/bin/sh
set -eu

lake env lean \
  Sal/ConditionedMRDTs/MRDT_Instances/Peritext_WithTombstones/Peritext_Intent.lean
