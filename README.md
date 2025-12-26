# Port of the Neem MRDT and CRDT Framework to Lean

The code is built on top of the [Loom](https://github.com/verse-lab/loom/tree/master) repository. Initially, Loom was used to prove the correctness directly, but eventually pure Lean was used since the structures being verified did not have mutability. Therefore, some proofs use Loom and some do not. 

## Steps to run

Clone this repository, and run `lake update` followed by `lake build`. Ensure that the Lean version in `lean-toolchain` stays at  `v4.26.0`. The various proofs are in the [Neem](CaseStudies/Neem) directory. Click on each Lean file in VS code to run all the verification conditions. 

# Data structures implemented and description

TODO

# Counterexample generation using Plausible

Our implementation of the `en-wins flag` was erroneous, and it did not pass the `inter_right_1op` VC. Earlier, the counterexample needed to be worked out manually, but we can now automatically generate small counter-examples. The [Plausible](https://github.com/leanprover-community/plausible) generator was used to generate minimal examples. The section of code can be checked out [here](https://github.com/pranavramesh2003/Neem_Loom/blob/master/CaseStudies/Neem/en_wins_flag.lean#L312). We prove that both the pre and post conditions are decidable under a suitable upper bound, and generate counter examples. Subsequently, we use [Logging](https://leanprover.github.io/functional_programming_in_lean/monads.html#logging)-style monads to derive the computation tree for the left and right hand sides of the `ensures` equality. [This file](CaseStudies/Neem/WriterMonad_ENflag.lean) shows the computation path logged as a list. 
