# Divisible-Sandpile-RWRS

A machine-checked **Lean 4** formalization of the paper
[*Divisible sandpiles via random walks in random scenery*](https://arxiv.org/abs/2604.13968)
(Ahmed Bou-Rabee, Yuval Peres and Ecaterina Sava-Huss, arXiv:2604.13968), built
on [`mathlib`](https://github.com/leanprover-community/mathlib4) and the shared
library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability).

The three main theorems of the paper are proved in the form in which its
introduction states them, and so is every other labelled theorem, lemma,
proposition and corollary.  Of the nine results the paper quotes from the
literature without proof, eight are proved here; the ninth, the ergodic
decomposition of stationary random networks, is an explicit hypothesis of the
statements that use it, and none of the three main theorems uses it.

[![CI](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/build.yml/badge.svg)](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/comparator.yml/badge.svg)](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/comparator.yml)

## What is proved

On a connected, locally finite graph, a divisible sandpile gives each vertex a
real mass.  A vertex with mass above 1 topples by keeping mass 1 and sending the
excess equally to its neighbours; toppling all unstable vertices in parallel
yields odometers `u_n(v)` that increase to `u_∞(v) ∈ [0,∞]`, where
`deg(v) · u_∞(v)` is the total mass emitted by `v`.  The configuration
stabilizes if `u_∞(v) < ∞` for every `v`, and explodes otherwise.  Let the graph
be infinite, connected and of bounded degree, with i.i.d. initial masses `σ(v)`
of mean `μ`.  Theorem 1.2 of the paper says that the sandpile explodes almost
surely if `μ > 1`, and if `μ = 1` with positive finite variance or with `σ − 1`
symmetric and `σ ≢ 1`.  Theorem 1.3 says that if `μ < 1` and
`E[(σ⁺)^p] < ∞` for some `p > 3`, it stabilizes almost surely and
`sup_v E[u_∞(v)^q] < ∞` for every `q ∈ [1, (p−1)/2)`, and that under polynomial
volume growth of degree `d_f` a moment of order `p > d_f` suffices.  Both are
deduced from Theorem 1.1, an optimal stopping result for random walk in random
scenery, through a representation of the odometer as an optimal stopping value.
The three theorems, formalized as stated in the introduction, are:

* **`RWRS.optimalStopping`** (Theorem 1.1, `thm:OS`): on an infinite connected
  graph of degree at most `d`, with an i.i.d. scenery `ξ` of law `ν` independent
  of simple random walk and `S_n = ∑_{k<n} ξ(X_k)/deg(X_k)`: if `E[ξ] > 0`, then
  `sup_n E_x[S_n | ξ] = ∞` almost surely; if `E[ξ] = 0` with positive finite
  variance, or with `ξ ≢ 0` symmetric, then `sup_τ E_x[S_τ | ξ] = ∞` almost
  surely over bounded stopping times, and `sup_n E_x[S_n | ξ] = ∞` if the graph
  is not doubly transient; if `E[ξ] < 0` and `E[(ξ⁺)^p] < ∞` for some `p > 3`,
  then `E_x[(sup_n S_n)^q] < ∞` for every `q ∈ [1, (p−1)/2)`.
* **`RWRS.explosion`** (Theorem 1.2, `thm:explosion`): i.i.d. masses of mean
  `μ > 1`, or of mean `μ = 1` with positive finite variance or with `σ − 1`
  symmetric and `σ ≢ 1`, stabilize with probability zero.
* **`RWRS.stabilization`** (Theorem 1.3, `thm:stab`): i.i.d. masses of mean
  `μ < 1` with `E[(σ⁺)^p] < ∞` for some `p > 3` have `sup_v E[u_∞(v)^q] < ∞`
  for every `q ∈ [1, (p−1)/2)` and stabilize almost surely; if
  `|B(o,r)| ≤ C r^{d_f}` for all `r ≥ 1`, then `E[(σ⁺)^p] < ∞` for some
  `p > d_f` suffices for almost sure stabilization.

The three theorems are stated in full in
[`RWRS/MainTheorems.lean`](RWRS/MainTheorems.lean), each proved by direct
application of its certified counterpart in `RWRS/Frozen/`, so the statements
displayed there are exactly the certified ones.  None of them carries a result
cited from the literature as a hypothesis.

This repository formalizes **every labelled theorem, lemma, proposition and
corollary of the paper**: Theorems 1.1 to 1.3, the random walk representation,
the stationary and critical cases, the sharpness constructions (the tree of
pipes and the recurrent graphs on which masses with `p < 3` explode, the
moment sharpness lemma, and the locally finite tree on which every integrable
law stabilizes), and the lemmas of the later sections.  The sharpness results
are the registered statements `thm:transient-nonstab`, `thm:recurrent-nonstab`,
`lem:moment-sharpness` and `ex:counterexample`.  Not formalized: the open
questions of Section 9, the proof ideas and related work of Sections 1.1
and 1.2, the `example` and `remark` environments, and the figures.

**Cited results.**  The paper quotes nine results from the literature without
proof.  Eight of them are proved outright in this repository, most of them
through Lattice-Probability, in the generality every use site needs: the von
Bahr–Esseen, Fuk–Nagaev and Bernstein inequalities unconditionally, the
bounded-degree heat kernel bound and heat kernel vanishing on every infinite
connected graph, the Efron–Stein inequality for a countable index set, the
pointwise Carne–Varopoulos bound on every connected, nontrivial, locally
finite graph, and the bounded voltage function on every infinite connected
graph, recurrent or transient (`RWRS.External.voltageFunction_of_connected`,
node `X-008`).  Each lives, proposition and proof together, as a single
`SEALED` theorem node in `RWRS/External/` (see `tools/check_manifest.py`), and
no statement carries it as a hypothesis; the theorems that need the voltage
function discharge it inside their proofs.  The ninth, the ergodic
decomposition of stationary random networks, is **not proved here**.  It is
stated in Lean as a proposition in `RWRS/External/` in state `FROZEN`, and the
statements whose proofs use it, `RWRS.Frozen.stationaryPhase`
(`thm:stationary-phase`) and `RWRS.Frozen.zeroOneStationary`
(`lem:01-stationary`), take it as an explicit hypothesis.
[`ASSUMPTIONS.md`](ASSUMPTIONS.md) gives its verbatim Lean statement.

**Registered statements.**  Every statement and every cited input is registered
in [`ledger/manifest.yaml`](ledger/manifest.yaml); the following summary is
generated from it.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **51 registered nodes: 50 SEALED (statements of the paper, proved), 1 FROZEN (cited external inputs, stated as hypotheses; 0 of them with a proved companion).**

The SEALED count includes 41 paper statements and 0 companion theorems. Their proofs are machine-checked,
and their axiom closures are exactly Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, and no axiom added by this development.
Run `python3 tools/check_axioms.py` to verify the registered theorems.

Cited inputs proved outright, as ordinary SEALED theorems: `X-001` (`RWRS.External.vonBahrEsseen`), `X-002` (`RWRS.External.fukNagaevTail`), `X-003` (`RWRS.External.bernstein`), `X-004` (`RWRS.External.heatKernelBoundedDegree_of_connected`), `X-005` (`RWRS.External.carneVaropoulos`), `X-006` (`RWRS.External.heatKernelVanishing_of_connected`), `X-007` (`RWRS.External.efronStein`), `X-008` (`RWRS.External.voltageFunction_of_connected`).
No frozen statement carries any of them as a hypothesis.

This section is generated by `python3 tools/sync_docs.py --write`.

<!-- STATUS-END -->

**Faithfulness.**  Every labelled statement of the paper is registered: one Lean
declaration per theorem, lemma, proposition and corollary, and one proposition
per cited result.  A registered statement's text between the lines
`-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` is pinned by the
SHA-256 of those bytes in [`ledger/manifest.yaml`](ledger/manifest.yaml),
together with the paper `\label` and line range it transcribes; the proof after
the end marker is not pinned.  In the manifest, a registered statement is
`SEALED` when it is proved with an axiom closure of exactly the three standard
axioms, and `FROZEN` when it is a cited result assumed rather than proved.  The
paper in `paper/rwrs.tex` is arXiv:2604.13968v1 with the corrections listed in
[`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md).

The paper-to-Lean map, node by node, is
[`CORRESPONDENCE.md`](CORRESPONDENCE.md), which also records the transcription
conventions and the frozen statements that carry a hypothesis of the paper
their proof does not use.  Modelling decisions:

- A graph is a Mathlib `SimpleGraph` with `LocallyFinite`; infiniteness,
  connectedness and a degree bound are hypotheses of the statements that use
  them, as in the paper (`RWRS/Basic.lean`).
- The parallel toppling procedure is iterated in closed form, and the limiting
  odometer `u_∞` is valued in `[0,∞]`, so an exploding vertex has the value `⊤`
  and not a junk real number.  Quantities the paper allows to be infinite (the
  Green function, `sup_n S_n`, the two optimal stopping suprema, every moment)
  live in `ℝ≥0∞`, and the extended mean in `EReal`, with `HasExtMean`
  excluding the indeterminate case `E[σ⁺] = E[σ⁻] = ∞`.
- The i.i.d. field is the product law `Measure.infinitePi` on `V → ℝ`, and the
  walk is the law of a trajectory driven by i.i.d. uniform instructions
  (`RWRS/Walk.lean`, `RWRS/Scenery.lean`); independence of walk and scenery is
  the product structure of their joint law.
- Expectations at a bounded horizon are written with the first-step recursion
  of the walk, a finite average needing no measure; a stopping time is a
  function of the trajectory whose value at `k` is decided by its first `k+1`
  positions.
- Uniform constants are bound before the quantities they must not depend on,
  and `tools/check_constants.py` checks it mechanically.

## Guarantees

- **No `sorry`** in the library; `tools/check_manifest.py` rejects any other
  than a registered `DRAFT_SORRY` node, and there is none.  The three
  comparator challenges under `Audit/` each contain one intentional
  statement-level `sorry`, which the corresponding solution file proves.
- **No custom axiom.**  The three main theorems depend only on mathlib's
  standard axioms `propext`, `Classical.choice` and `Quot.sound`.
  [`RWRS/Meta/AxiomsAudit.lean`](RWRS/Meta/AxiomsAudit.lean) prints their
  axiom dependencies, the axiom-audit step of the CI workflow fails on any
  warning, including a `sorry` warning, and `python3 tools/check_axioms.py`
  checks the axiom closure of every registered declaration.  The one cited
  result that is assumed, the ergodic decomposition, is a hypothesis, not an
  axiom.
- **Independent check of the statements.**  So that the main claims can be read
  without trusting the development, all three main theorems are restated using
  only Mathlib, with no project definitions, in
  [`Audit/OptimalStopping/Challenge.lean`](Audit/OptimalStopping/Challenge.lean),
  [`Audit/Explosion/Challenge.lean`](Audit/Explosion/Challenge.lean) and
  [`Audit/Stabilization/Challenge.lean`](Audit/Stabilization/Challenge.lean).
  Each challenge rebuilds the model from Mathlib primitives (the averaging
  operator and Laplacian of a locally finite graph, parallel toppling and its
  odometer, the heat kernel and Green function, the walk payoff, bounded
  stopping times, the law of simple random walk on path space, the i.i.d.
  scenery and its moments, the optimal stopping suprema, double transience,
  volume growth) and contains one intentional statement-level `sorry`, which
  the corresponding `Solution.lean` fills from the library through the
  identifications in `Audit/Support/`.  The configurations in
  `Audit/*/comparator.json` are for
  [`leanprover/comparator`](https://github.com/leanprover/comparator), which
  confirms that the two statements have identical elaborated types and that the
  proof reduces to the three standard axioms; all three pairs pass it, with the
  Lean kernel and with the independent nanoda kernel (pins and results in
  [`Audit/COMPARATOR_RUNS.md`](Audit/COMPARATOR_RUNS.md)).
  `Audit/StatementRegression.lean` checks locally that each solution statement
  is exactly the challenge statement and mentions no constant of the repository
  or of Lattice-Probability, and the workflow
  [`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) runs
  the comparator on request.  See [`Audit/README.md`](Audit/README.md).
- **Pinned toolchain.**  Lean `v4.32.0` ([`lean-toolchain`](lean-toolchain)),
  mathlib at revision `81a5d257c8e410db227a6665ed08f64fea08e997`, and
  Lattice-Probability at commit `9d44b4d4670df393bb86ac5a4e042f215001cddf`,
  recorded in [`lakefile.lean`](lakefile.lean) and
  [`lake-manifest.json`](lake-manifest.json).

Each statement file under `RWRS/Frozen/` cites the paper's TeX source
`paper/rwrs.tex` by `\label` and line range, which `tools/paper_anchors.py`
checks.

## Size

About 48,000 lines of Lean in 293 modules, of which about 37,000 lines are code
once comments and blank lines are removed, on top of the Lattice-Probability
library (about 440 modules, about 80,000 lines of code).

## Building

The project uses [`elan`](https://github.com/leanprover/elan) (the Lean
toolchain manager) and Lake.  The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), so `elan` installs the right Lean version
automatically.  The Mathlib revision and the Lattice-Probability commit are
pinned in [`lakefile.lean`](lakefile.lean) and
[`lake-manifest.json`](lake-manifest.json), and Lake fetches both.

```bash
lake exe cache get      # prebuilt Mathlib
lake build RWRS         # compile the library, about 9,000 build jobs, nearly all Mathlib's
```

```bash
lake build RWRS.Meta.AxiomsAudit   # print the axioms of the three main theorems
lake build Audit                   # the comparator challenges and solutions
lake build Audit.StatementRegression
```

To use the library, `import RWRS` pulls in the whole development; the main
results are in `import RWRS.MainTheorems`.

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).

| command | what it guarantees |
|---|---|
| `python3 tools/check_manifest.py` | every frozen block's SHA-256 matches the manifest, every file in `RWRS/Frozen/` belongs to one node, and `RWRS/` and `RWRS.lean` contain no `axiom`, `admit` or `sorryAx`, and `sorry` only in `DRAFT_SORRY` nodes (there are none) |
| `python3 tools/check_axioms.py` | Lean's `#print axioms` for every registered declaration shows no `sorryAx` and nothing beyond `propext`, `Classical.choice`, `Quot.sound` |
| `python3 tools/check_warnings.py` | `lake build RWRS` succeeds and emits no warning other than one `sorry` warning per `DRAFT_SORRY` node |
| `python3 tools/check_constants.py` | in a frozen statement with a real-valued existential constant, none of a fixed list of parameter names is bound before it, so the constant cannot depend on them; the exceptions are listed in the script with their reasons |
| `python3 tools/check_coverage.py` | every labelled theorem, lemma, proposition and corollary of `paper/rwrs.tex` is claimed by a manifest node |

Also in `tools/`: `paper_anchors.py` and `paper_citations.py` check line
anchors against the paper; `sync_docs.py` regenerates the marked blocks of this
file and of `CORRESPONDENCE.md` from the manifest (`--write` applies, the bare
command checks); `assumptions.py` regenerates `ASSUMPTIONS.md` (`--check`
compares); `certificate.py` regenerates `CERTIFICATE.md` (`--check` compares);
`freeze.py` registers or refreshes a node in the manifest.  See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for further building notes.

## Repository layout

```
RWRS/
  MainTheorems.lean   the main theorems, stated in full
  Frozen/             the certified statement surface, one frozen statement per file
  External/           the nine cited results as propositions, with the proofs of
                      the eight that are proved; ErgodicDecomposition.lean states
                      the one that is assumed
  Support/            the lemmas and constructions the frozen statements are proved
                      from, including LibraryBridge.lean (the identification with
                      Lattice-Probability)
  Meta/               AxiomsAudit.lean
  Zd/                 the specialization to ℤ^d
  Basic.lean          the graph operators, the divisible sandpile, the heat kernel
  Walk.lean           the walk, its payoff, stopping times, the walk on path space
  Scenery.lean        the i.i.d. scenery and its moments
  Setting.lean        the optimal stopping suprema, double transience, growth bounds
  Network.lean        stationary rooted networks
RWRS.lean             the root module (imports the whole library)
Audit/                the mathlib-only comparator challenges and solutions
  OptimalStopping/    Challenge.lean, Solution.lean, comparator.json (Theorem 1.1)
  Explosion/          the same for Theorem 1.2
  Stabilization/      the same for Theorem 1.3
  Support/            Vocabulary.lean, Statements.lean, Bridge.lean
  StatementRegression.lean   the local statement-identity check
  README.md, DESIGN.md, COMPARATOR_RUNS.md, check_standalone.sh
ASSUMPTIONS.md        the cited result assumed, with its Lean statement (generated)
CORRESPONDENCE.md     paper ↔ Lean, node by node
CERTIFICATE.md        generated record of the toolchain, each node's axiom closure
                      and the scope of the cited inputs proved outright
ledger/manifest.yaml  one row per registered statement: hash, paper label, state
paper/rwrs.tex        the paper, pinned by the SHA-256 in ledger/manifest.yaml
paper/CHANGES_FROM_ARXIV.md  every difference between paper/rwrs.tex and arXiv:2604.13968v1
paper/rwrs-arxiv.tex  the unmodified arXiv source; paper/arxiv/ holds its other files
tools/                the checkers and generators listed under Building
.github/workflows/    build.yml (CI) and comparator.yml (the comparator audit)
formalization.yaml    machine-readable disclosure (models, tooling, cost, status, review)
CITATION.cff          citation metadata
CONTRIBUTING.md       building notes and the elaboration policy for new files
lakefile.lean, lake-manifest.json, lean-toolchain   the pinned build
```

## How this was built

The Lean code was written mostly by Claude (Opus models of unrecorded version,
Opus 5.5 and Sonnet 5), with contributions by OpenAI's gpt-6-astra, gpt-6-luna
and gpt-5.6-luna, by GLM-5.3 and GLM-5.3-flash, and by DeepSeek-v4.1-flash,
under the close supervision of the author; models, tooling, cost and review
status are disclosed in [`formalization.yaml`](formalization.yaml), following
the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors, citation, acknowledgements

The Lean development is by **Ahmed Bou-Rabee**.  The paper it formalizes,
[arXiv:2604.13968](https://arxiv.org/abs/2604.13968), is joint work of Ahmed
Bou-Rabee, Yuval Peres and Ecaterina Sava-Huss.  To cite the formalization, use
[`CITATION.cff`](CITATION.cff).

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4), and the shared
library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability),
which supplies the probability inequalities, the heat kernel estimates and the
voltage function behind the cited results proved here; the comparator audit in
[`Audit/`](Audit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).  The paper source in `paper/` is included for
reference and is not covered by the Apache license.
