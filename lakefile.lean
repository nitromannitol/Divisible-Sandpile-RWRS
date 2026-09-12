import Lake
open Lake DSL

package «divisible-sandpile-rwrs» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability" @ "dd68065e6055a958c0ae02a47a90824854a80499"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

@[default_target]
lean_lib «RWRS» where
  globs := #[.andSubmodules `RWRS]
