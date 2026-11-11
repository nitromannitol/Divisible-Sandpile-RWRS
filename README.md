# Divisible sandpiles via random walks in random scenery

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee, Yuval Peres and Ecaterina Sava-Huss,
> *Divisible sandpiles via random walks in random scenery*,
> [arXiv:2604.13968](https://arxiv.org/abs/2604.13968).

The paper's source is included under [`paper/`](paper/). The 3 main theorems of the paper are
proved, in the form in which its introduction states them, **for every infinite, connected,
locally finite graph of bounded degree and every law of the initial masses that satisfies the
hypotheses of the theorem**. Every other labelled theorem, lemma, proposition and corollary of
the paper is formalized as well; two of them take a cited result as a hypothesis (see
[Standing assumptions and scope](#standing-assumptions-and-scope)).

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4) and on
the shared library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability)
(`LatticeProb`), a library of lattice probability and potential theory.

[![CI](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/comparator.yml)

## What is proved

On a connected, locally finite graph, a divisible sandpile gives each vertex a real mass. A
vertex with mass above 1 topples by keeping mass 1 and sending the excess equally to its
neighbours; toppling all unstable vertices in parallel yields odometers `u_n(v)` that increase
to `u_∞(v) ∈ [0,∞]`, where `deg(v) · u_∞(v)` is the total mass emitted by `v`. The
configuration stabilizes if `u_∞(v) < ∞` for every `v`, and explodes otherwise. Let the graph
be infinite, connected and of bounded degree, with i.i.d. initial masses `σ(v)` of mean `μ`.
Theorem 1.2 of the paper says that the sandpile explodes almost surely if `μ > 1`, and if
`μ = 1` with positive finite variance or with `σ − 1` symmetric and `σ ≢ 1`. Theorem 1.3 says
that if `μ < 1` and `E[(σ⁺)^p] < ∞` for some `p > 3`, it stabilizes almost surely and
`sup_v E[u_∞(v)^q] < ∞` for every `q ∈ [1, (p−1)/2)`, and that under polynomial volume growth
of degree `d_f` a moment of order `p > d_f` suffices. Both are deduced from Theorem 1.1, an
optimal stopping result for random walk in random scenery, through a representation of the
odometer as an optimal stopping value. The model is stated precisely in
[Standing assumptions and scope](#standing-assumptions-and-scope).

The 3 main results, formalized as stated in the introduction of the paper, are collected in
[`RWRS/MainTheorems.lean`](RWRS/MainTheorems.lean). Each is proved by direct application of its
certified counterpart in `RWRS/Frozen/`, so the statements displayed there are exactly the
certified ones. None of them carries a result cited from the literature as a hypothesis.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 (label `thm:OS`) | `RWRS.optimalStopping` | explosion and stabilization of the optimal stopping values of random walk in random scenery |
| Theorem 1.2 (label `thm:explosion`) | `RWRS.explosion` | the divisible sandpile with i.i.d. masses explodes almost surely at mean above 1 and, under a variance or symmetry condition, at mean 1 |
| Theorem 1.3 (label `thm:stab`) | `RWRS.stabilization` | below mean 1, moment bounds on the odometer and almost sure stabilization |

**Theorem 1.1 (explosion and stabilization for random walk, `thm:OS`).** On an infinite
connected graph of degree at most `d`, let `ξ` be an i.i.d. scenery of law `ν` independent of
simple random walk, and `S_n = ∑_{k<n} ξ(X_k)/deg(X_k)`.

1. *Explosion.* If `E[ξ] > 0`, then `sup_n E_x[S_n | ξ] = ∞` almost surely.
2. *Critical explosion.* If `E[ξ] = 0` with positive finite variance, or with `ξ ≢ 0`
   symmetric, then `sup_τ E_x[S_τ | ξ] = ∞` almost surely over bounded stopping times, and
   `sup_n E_x[S_n | ξ] = ∞` if the graph is not doubly transient.
3. *Stabilization.* If `E[ξ] < 0` and `E[(ξ⁺)^p] < ∞` for some `p > 3`, then
   `E_x[(sup_n S_n)^q] < ∞` for every `q ∈ [1, (p−1)/2)`.

In Lean, `RWRS.optimalStopping` takes a Mathlib `SimpleGraph` with `LocallyFinite`, `Infinite`
and `Connected` hypotheses and a degree bound `RWRS.BoundedDegree G d`. The scenery has the
law `RWRS.iidLaw V ν`, the suprema (`RWRS.supMeanPayoff`, `RWRS.supStopValue`) take values in
`ℝ≥0∞`, and the finiteness of the moment in part 3 is stated as `∫⁻ … ≠ ⊤`.

**Theorem 1.2 (explosion, `thm:explosion`).** For i.i.d. masses of mean `μ`:

1. *Supercritical.* If `μ > 1`, the sandpile stabilizes with probability zero.
2. *Critical.* If `μ = 1` with positive finite variance, or with `σ − 1` symmetric and
   `σ ≢ 1`, the sandpile stabilizes with probability zero.

In Lean, `RWRS.explosion` states that the set of stabilizing configurations
`{σ | RWRS.Stabilizes G σ}` has `RWRS.iidLaw V ν`-measure `0`.

**Theorem 1.3 (stabilization, `thm:stab`).** For i.i.d. masses of mean `μ < 1`:

1. *Moment bound.* If `E[(σ⁺)^p] < ∞` for some `p > 3`, then `sup_v E[u_∞(v)^q] < ∞` for every
   `q ∈ [1, (p−1)/2)`, and the configuration stabilizes almost surely.
2. *Polynomial growth.* If `|B(o,r)| ≤ C r^{d_f}` for all `r ≥ 1`, then `E[(σ⁺)^p] < ∞` for
   some `p > d_f` suffices for almost sure stabilization.

In Lean, `RWRS.stabilization` takes `RWRS.extMean ν < 1`; the moments of the limiting odometer
`RWRS.odometerLimit G σ v` are integrals `∫⁻` in `ℝ≥0∞`, and the growth hypothesis is
`RWRS.VolumeGrowthUpper G o C d_f`.

The repository formalizes every labelled theorem, lemma, proposition and corollary of the
paper: Theorems 1.1 to 1.3, the random walk representation, the stationary and critical cases,
the sharpness constructions (the tree of pipes and the recurrent graphs on which masses with
`p < 3` explode, the moment sharpness lemma, and the locally finite tree on which every
integrable law stabilizes), and the lemmas of the later sections. The sharpness results are
the registered statements `thm:transient-nonstab`, `thm:recurrent-nonstab`,
`lem:moment-sharpness` and `ex:counterexample`.

## Corrections to the published version

The formalization follows `paper/rwrs.tex`, a corrected text of the paper: it is
[arXiv:2604.13968v1](https://arxiv.org/abs/2604.13968v1) with two mathematical corrections and
some typographical changes. [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) lists
every change against the arXiv version.

## Standing assumptions and scope

1. **Every theorem is about every graph and every law that satisfies its hypotheses.** The
   three main theorems hold for every `SimpleGraph V` that is `LocallyFinite`, `Infinite` and
   connected, with `RWRS.BoundedDegree G d` for some `d`, and for every probability measure
   `ν` on `ℝ` with `RWRS.HasExtMean ν`, in the stated regimes of the mean
   `RWRS.extMean ν`: `> 0`, `= 0` and `< 0` in Theorem 1.1, `> 1` and `= 1` in Theorem 1.2,
   `< 1` in Theorem 1.3. The statements also assume `[MeasurableSpace V]`, and
   `[MeasurableSingletonClass V]` in Theorems 1.1 and 1.3.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no new `axiom`. The axiom report of each main theorem consists of
   exactly `propext`, `Classical.choice` and `Quot.sound`. The main theorems rely on no
   unproved result: everything they use, including the facts the paper cites from the
   literature, is available in mathlib or Lattice-Probability or is proved in this repository.
3. **One cited result is assumed, outside the main theorems.** The ergodic decomposition of
   stationary random networks, one of the nine results the paper quotes from the literature, is
   **not proved here**. It is stated in Lean as a proposition in `RWRS/External/` and enters as
   an explicit hypothesis of the two statements whose proofs use it, `RWRS.Frozen.stationaryPhase`
   (`thm:stationary-phase`) and `RWRS.Frozen.zeroOneStationary` (`lem:01-stationary`); none of
   the three main theorems uses it. [`ASSUMPTIONS.md`](ASSUMPTIONS.md) gives its verbatim Lean
   statement.
4. **What is not formalized.** The open questions of Section 9, the proof ideas and related
   work of Sections 1.1 and 1.2, the `example` and `remark` environments, and the figures.
5. **Conventions that matter for reading the statements.**
   - A graph is a Mathlib `SimpleGraph` with `LocallyFinite`; infiniteness, connectedness and a
     degree bound are hypotheses of the statements that use them, as in the paper
     (`RWRS/Basic.lean`).
   - The parallel toppling procedure is iterated in closed form, and the limiting odometer
     `u_∞` is valued in `[0,∞]`, so an exploding vertex has the value `⊤` and not a junk real
     number. Quantities the paper allows to be infinite (the Green function, `sup_n S_n`, the
     two optimal stopping suprema, every moment) live in `ℝ≥0∞`, and the extended mean in
     `EReal`, with `HasExtMean` excluding the indeterminate case `E[σ⁺] = E[σ⁻] = ∞`.
   - The i.i.d. field is the product law `Measure.infinitePi` on `V → ℝ`, and the walk is the
     law of a trajectory driven by i.i.d. uniform instructions (`RWRS/Walk.lean`,
     `RWRS/Scenery.lean`); independence of walk and scenery is the product structure of their
     joint law.
   - Expectations at a bounded horizon are written with the first-step recursion of the walk,
     a finite average needing no measure; a stopping time is a function of the trajectory whose
     value at `k` is decided by its first `k+1` positions.
   - Uniform constants are bound before the quantities they must not depend on, and
     `tools/check_constants.py` checks it mechanically.
6. **Explicit versus implicit.** The Lean statements spell out what the paper leaves implicit:
   the measurable structure on the vertex set, and `RWRS.HasExtMean ν`, which says that the
   mean of the law exists in `[−∞, ∞]` (the paper writes `E[σ(v)] = μ`).
7. **Statements without a formal counterpart.** The correspondence table in
   [`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps the registered statements to Lean declarations
   node by node, records the transcription conventions, and lists the frozen statements that
   carry a hypothesis of the paper their proof does not use. The passages without a formal
   counterpart are those listed in item 4.

## Results cited from the literature

The paper quotes nine results from the literature without proof. Eight of them are proved
outright in this repository, most of them through Lattice-Probability, in the generality every
use site needs: the von Bahr–Esseen, Fuk–Nagaev and Bernstein inequalities unconditionally, the
bounded-degree heat kernel bound and heat kernel vanishing on every infinite connected graph,
the Efron–Stein inequality for a countable index set, the pointwise Carne–Varopoulos bound on
every connected, nontrivial, locally finite graph, and the bounded voltage function on every
infinite connected graph, recurrent or transient
(`RWRS.External.voltageFunction_of_connected`, node `X-008`). Each lives, proposition and
proof together, as a single `PROVED` theorem node in `RWRS/External/` (see
`tools/check_manifest.py`), and no statement carries it as a hypothesis; the theorems that need
the voltage function discharge it inside their proofs. The ninth, the ergodic decomposition of
stationary random networks, is stated in `RWRS/External/` in state `FROZEN`; see item 3 of
[Standing assumptions and scope](#standing-assumptions-and-scope).

## Registered statements

Every statement and every cited input is registered in
[`ledger/manifest.yaml`](ledger/manifest.yaml); the following summary is generated from it.

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **51 registered nodes: 50 PROVED (statements of the paper, proved and independently audited), 1 FROZEN (cited external inputs, stated as hypotheses; 0 of them with a proved companion).**

The PROVED count includes 41 paper statements and 0 companion theorems. Their proofs are machine-checked,
and their axiom closures are exactly Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, and no axiom added by this development.
Run `python3 tools/check_axioms.py` to verify the registered theorems.

Cited inputs proved outright, as ordinary proved theorem nodes: `X-001` (`RWRS.External.vonBahrEsseen`), `X-002` (`RWRS.External.fukNagaevTail`), `X-003` (`RWRS.External.bernstein`), `X-004` (`RWRS.External.heatKernelBoundedDegree_of_connected`), `X-005` (`RWRS.External.carneVaropoulos`), `X-006` (`RWRS.External.heatKernelVanishing_of_connected`), `X-007` (`RWRS.External.efronStein`), `X-008` (`RWRS.External.voltageFunction_of_connected`).
No frozen statement carries any of them as a hypothesis.

This section is generated by `python3 tools/sync_docs.py --write`.

<!-- STATUS-END -->

Every labelled statement of the paper is registered: one Lean declaration per theorem, lemma,
proposition and corollary, and one proposition per cited result. A registered statement's text
between the lines `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` is pinned by the
SHA-256 of those bytes in [`ledger/manifest.yaml`](ledger/manifest.yaml), together with the
paper `\label` and line range it transcribes; the proof after the end marker is not pinned. In
the manifest, a registered statement is `PROVED` when it is proved with an axiom closure of
exactly the three standard axioms and has passed an independent refute-first audit, `SEALED`
when it is proved but not yet audit-promoted, and `FROZEN` when it is a cited result assumed
rather than proved. Each statement file under `RWRS/Frozen/` cites the paper's TeX source
`paper/rwrs.tex` by `\label` and line range, which `tools/paper_anchors.py` checks.

## Guarantees

- **No `sorry`.** The library has none, and `tools/check_manifest.py` rejects any other than a
  registered `DRAFT_SORRY` node, of which there is none. The 3 comparator challenges under
  [`RWRSAudit/`](RWRSAudit/) each contain one intentional statement-level `sorry`, which the
  corresponding solution proves.
- **Standard axioms only.** The axiom report of each of the 3 main theorems lists exactly
  `propext`, `Classical.choice` and `Quot.sound`.
  [`RWRS/Meta/AxiomsAudit.lean`](RWRS/Meta/AxiomsAudit.lean) prints the reports, the
  continuous-integration build of that module fails on any warning, including a `sorry`
  warning, and `python3 tools/check_axioms.py` checks the axiom closure of every registered
  declaration.
- **Builds from a clean checkout.** In continuous integration, `lake build RWRS` of a fresh
  checkout completes 9,006 jobs without error, and the build fails on any warning or
  `sorry` warning.
- **Independent check of the statements.** The 3 main theorems are restated in
  [`RWRSAudit/`](RWRSAudit/) using mathlib alone, one challenge file per theorem
  ([`OptimalStopping`](RWRSAudit/OptimalStopping/Challenge.lean),
  [`Explosion`](RWRSAudit/Explosion/Challenge.lean) and
  [`Stabilization`](RWRSAudit/Stabilization/Challenge.lean)). Each challenge rebuilds the model
  from mathlib primitives (the averaging operator and Laplacian of a locally finite graph,
  parallel toppling and its odometer, the heat kernel and Green function, the walk payoff,
  bounded stopping times, the law of simple random walk on path space, the i.i.d. scenery and
  its moments, the optimal stopping suprema, double transience, volume growth). The solution
  file proves each restatement from the library through the identifications in
  `RWRSAudit/Support/`, one bridge per challenge, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
  is proved, with only the three standard axioms, through independent implementations of the
  Lean kernel. See [`RWRSAudit/README.md`](RWRSAudit/README.md) and
  [`RWRSAudit/COMPARATOR_RUNS.md`](RWRSAudit/COMPARATOR_RUNS.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0`; mathlib at revision
  `81a5d257c8e410db227a6665ed08f64fea08e997` and Lattice-Probability at commit
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`, recorded in [`lakefile.lean`](lakefile.lean) and
  [`lake-manifest.json`](lake-manifest.json) (see [Building](#building)).
- **The paper is part of the repository.** The statement map refers to the version in
  [`paper/`](paper/), pinned to the SHA-256
  `809373589ee57976f2eb57cd62a1cb1d94d8e66ac576632be65385e9a06ded6c` of `paper/rwrs.tex`.

## Size

The library contains 292 Lean files with 48,331 physical lines, on top of mathlib and
Lattice-Probability. The comparator sources (12 files, 1,813 lines) are counted separately.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get      # prebuilt mathlib
lake build RWRS         # compile the library
```

Lattice-Probability has no prebuilt cache, so the first build compiles it as well as the
library. `import RWRS` loads the whole development, and `import RWRS.MainTheorems` loads the
main theorems and what they use.

The dependencies are public repositories, pinned to exact commits in
[`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`.

To reproduce the axiom reports and build the comparator libraries:

```bash
lake build RWRS.Meta.AxiomsAudit   # print the axioms of the three main theorems
lake build RWRSAudit               # the comparator challenges and solutions
```

The checkers in `tools/` need Python 3 and PyYAML (`pip install pyyaml`).

| command | what it guarantees |
| --- | --- |
| `python3 tools/check_manifest.py` | every frozen block's SHA-256 matches the manifest, every file in `RWRS/Frozen/` belongs to one node, and `RWRS/` and `RWRS.lean` contain no `axiom`, `admit` or `sorryAx`, and `sorry` only in `DRAFT_SORRY` nodes (there are none) |
| `python3 tools/check_axioms.py` | Lean's `#print axioms` for every registered declaration shows no `sorryAx` and nothing beyond `propext`, `Classical.choice`, `Quot.sound` |
| `python3 tools/check_warnings.py` | `lake build RWRS` succeeds and emits no warning other than one `sorry` warning per `DRAFT_SORRY` node |
| `python3 tools/check_constants.py` | in a frozen statement with a real-valued existential constant, none of a fixed list of parameter names is bound before it, so the constant cannot depend on them; the exceptions are listed in the script with their reasons |
| `python3 tools/check_coverage.py` | every labelled theorem, lemma, proposition and corollary of `paper/rwrs.tex` is claimed by a manifest node |

Also in `tools/`: `paper_anchors.py` and `paper_citations.py` check line anchors against the
paper; `sync_docs.py` regenerates the marked blocks of this file and of `CORRESPONDENCE.md`
from the manifest (`--write` applies, the bare command checks); `assumptions.py` regenerates
`ASSUMPTIONS.md` (`--check` compares); `certificate.py` regenerates `CERTIFICATE.md`
(`--check` compares); `freeze.py` registers or refreshes a node in the manifest. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for further building notes.

## Running the comparators

Each comparator pair has a configuration `RWRSAudit/<Pair>/comparator.json`, for `<Pair>` one
of `OptimalStopping`, `Explosion` and `Stabilization`, that permits exactly `propext`,
`Classical.choice` and `Quot.sound` and enables the independent nanoda kernel. The comparator
checks that the solution proves the challenge statement, compares their dependency closures,
and replays the proof with the Lean and NanoDa kernels.

To run one pair locally, build `leanprover/comparator`, `lean4export`, `landrun` and
`nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml) (also recorded in
[`RWRSAudit/COMPARATOR_RUNS.md`](RWRSAudit/COMPARATOR_RUNS.md)), and from the repository root
run:

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator RWRSAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`. The comparator workflow
runs the three pairs one after the other in a single job on GitHub-hosted runners.

There are two continuous-integration workflows: **CI** builds the library and checks the axiom
audit and the frozen statements; **Comparator audit** checks all 3 challenge/solution pairs.
Both run on pushes to `main` that change Lean files, `tools/`, `paper/`, `ledger/`,
`formalization.yaml` or the build configuration, and can be started manually from the
[Actions page](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
RWRS.lean                 the root module, importing the whole library
RWRS/
  MainTheorems.lean       the main theorems, stated in full
  Frozen/                 the certified statement surface, one frozen statement per file
  External/               the nine cited results as propositions, with the proofs of the eight
                          that are proved; ErgodicDecomposition.lean states the one assumed
  Support/                the lemmas and constructions the frozen statements are proved from,
                          including LibraryBridge.lean (the identification with
                          Lattice-Probability)
  Meta/AxiomsAudit.lean   the axiom report, compiled by `lake build`, not imported by the root
  Zd/                     the specialization to ℤ^d
  Basic.lean              the graph operators, the divisible sandpile, the heat kernel
  Walk.lean               the walk, its payoff, stopping times, the walk on path space
  Scenery.lean            the i.i.d. scenery and its moments
  Setting.lean            the optimal stopping suprema, double transience, growth bounds
  Network.lean            stationary rooted networks
RWRSAudit/                the mathlib-only restatements and their solutions
  OptimalStopping/        Challenge.lean, SolutionBasic.lean, Solution.lean, comparator.json
  Explosion/              the same for Theorem 1.2
  Stabilization/          the same for Theorem 1.3
  Support/                OptimalStoppingBridge.lean, ExplosionBridge.lean, StabilizationBridge.lean
  README.md, DESIGN.md, COMPARATOR_RUNS.md, check_standalone.sh
ASSUMPTIONS.md            the cited result assumed, with its Lean statement (generated)
CORRESPONDENCE.md         paper to Lean, node by node
CERTIFICATE.md            generated record of the toolchain, each node's axiom closure and the
                          scope of the cited inputs proved outright
ledger/manifest.yaml      one row per registered statement: hash, paper label, state
paper/                    the paper: rwrs.tex, pinned by the SHA-256 in ledger/manifest.yaml;
                          rwrs-arxiv.tex, the unmodified arXiv source, with arxiv/ for its
                          other files; CHANGES_FROM_ARXIV.md, every difference between them
tools/                    the checkers and generators listed under Building
.github/workflows/        build.yml (CI) and comparator.yml (the comparator audit)
formalization.yaml        machine-readable disclosure (models, tooling, cost, status, review)
CITATION.cff              citation metadata
CONTRIBUTING.md           building notes and the elaboration policy for new files
lakefile.lean, lake-manifest.json, lean-toolchain   the pinned build
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and
DeepSeek, under the direction of the author. Every proof is checked by the Lean kernel. The
models, tooling, cost and review status are disclosed in [`formalization.yaml`](formalization.yaml),
following the [mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml)
standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**.  The paper it formalizes,
[arXiv:2604.13968](https://arxiv.org/abs/2604.13968), is joint work of Ahmed
Bou-Rabee, Yuval Peres and Ecaterina Sava-Huss.  To cite the formalization, use
[`CITATION.cff`](CITATION.cff).

This formalization is built on [Lean 4](https://lean-lang.org),
[Mathlib](https://github.com/leanprover-community/mathlib4), and the shared
library [Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability),
which supplies the probability inequalities, the heat kernel estimates and the
voltage function behind the cited results proved here; the comparator audit in
[`RWRSAudit/`](RWRSAudit/) is set up for
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## License

The Lean code in this repository is licensed under the **Apache License 2.0**
(see [`LICENSE`](LICENSE)).  The paper source in `paper/` is included for
reference and is not covered by the Apache license.
