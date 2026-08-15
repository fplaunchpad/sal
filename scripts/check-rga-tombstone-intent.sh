#!/bin/sh
set -eu

lake env lean \
  Sal/ConditionedMRDTs/MRDT_Instances/RGA_WithTombstones/RGA_Intent.lean
