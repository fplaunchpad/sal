import Lake
open Lake DSL
package vcAutoExperiment
require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "1f8a3b2f31366ec7da2a160e634004c52be6631e"
require Duper from git "https://github.com/leanprover-community/duper.git" @ "82606cd26168cb5e30e8e47375f0b3f091e769e0"
lean_lib VCAuto
