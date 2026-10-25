import Lake
open Lake DSL

package «divisible-sandpile-rwrs» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "b5fa741a3b9b7ee5bde8459d6ccdda807e38faf7"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "065356127b1dc0016f66b7283ce0ce2c4055aa55"

/-- The comparator audit surface (`RWRSAudit/*/Challenge.lean`, `RWRSAudit/*/SolutionBasic.lean`,
`RWRSAudit/*/Solution.lean` and `RWRSAudit/Support/`).  Not a default target: it builds only on
demand (`lake build RWRSAudit`), so the ordinary build of `RWRS` is unchanged. -/
lean_lib «RWRSAudit» where
  globs := #[.submodules `RWRSAudit]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unusedSectionVars, true⟩,
    ⟨`linter.unusedSimpArgs, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩
  ]

@[default_target]
lean_lib «RWRS» where
  globs := #[.andSubmodules `RWRS]
