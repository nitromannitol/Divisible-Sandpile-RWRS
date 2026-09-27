import Lake
open Lake DSL

package «divisible-sandpile-rwrs» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require «lattice-probability» from git
  "https://github.com/nitromannitol/Lattice-Probability.git" @ "9d44b4d4670df393bb86ac5a4e042f215001cddf"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "81a5d257c8e410db227a6665ed08f64fea08e997"

/-- The comparator audit surface (`Audit/*/Challenge.lean`, `Audit/*/Solution.lean` and
`Audit/Support/`).  Not a default target: it builds only on demand (`lake build Audit`), so the
ordinary build of `RWRS` is unchanged. -/
lean_lib «Audit» where
  globs := #[.submodules `Audit]
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
