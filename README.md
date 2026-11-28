# Divisible sandpiles via random walks in random scenery

[![CI](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee, Yuval Peres and Ecaterina Sava-Huss,
> [*Divisible sandpiles via random walks in random scenery*](https://arxiv.org/abs/2604.13968),
> arXiv:2604.13968.

Every labelled theorem, lemma, proposition and corollary of the paper is stated in Lean and proved,
with no `sorry` and only the standard axioms. The results that the paper quotes from other works
are proved in Lean as well. The three main theorems therefore hold for every infinite, connected,
locally finite graph of bounded degree and every law of the masses that satisfies their
hypotheses, with no further assumption.

## The paper

On a connected, locally finite graph, a *divisible sandpile* gives each vertex `v` a real mass
`σ(v)`. A vertex with mass above `1` is unstable; it *topples* by keeping mass `1` and sending the
excess equally to its neighbours. Toppling all unstable vertices at once, again and again, gives
the *odometer* `u_n(v)`: `deg(v) u_n(v)` is the total mass emitted by `v` in the first `n` steps.
The odometer increases to `u_∞(v) ∈ [0, ∞]`. The configuration *stabilizes* if `u_∞(v) < ∞` at
every vertex, and *explodes* otherwise.

On vertex-transitive graphs such as `ℤᵈ`, Levine, Murugan, Peres and Ugurcan showed that i.i.d.
masses of mean `μ` stabilize if `μ < 1` and explode if `μ > 1`, and also at `μ = 1` with positive
finite variance. The paper extends this phase transition to every graph of bounded degree. On such
graphs, a heavy-tailed mass can make the sandpile explode even when `μ < 1`, so a moment condition
is needed below mean one.

The proofs rest on a representation of the odometer as an optimal-stopping value. Let `X` be simple
random walk on the graph and `S_n = Σ_{k<n} ξ(X_k)/deg(X_k)` with `ξ = σ − 1`. Then
`u_∞(x) = sup_τ E_x[S_τ | σ]`, over bounded stopping times `τ` (Corollary 3.5). So the three
regimes of the sandpile become three regimes of a random walk in random scenery.

**Theorem 1.1 (explosion and stabilization for random walk).** Let `G` be an infinite, locally
finite, connected graph with degree at most `d`, let `ξ(v)` be i.i.d. and independent of the walk,
and let `S_n` be as above.

1. If `E[ξ] ∈ (0, ∞]`, then `sup_n E_x[S_n | ξ] = ∞` almost surely, for every `x`.
2. If `E[ξ] = 0` and either `Var(ξ) ∈ (0, ∞)`, or `ξ ≢ 0` is symmetric, then
   `sup_τ E_x[S_τ | ξ] = ∞` almost surely, over bounded stopping times. If `G` is not doubly
   transient, then also `sup_n E_x[S_n | ξ] = ∞` almost surely.
3. If `E[ξ] ∈ [−∞, 0)` and `E[(ξ⁺)^p] < ∞` for some `p > 3`, then `E_x[(sup_n S_n)^q] < ∞` for every
   `q ∈ [1, (p − 1)/2)`.

Here `G` is *doubly transient* if its Green function satisfies `Σ_v g(o, v)² < ∞`; for example `ℤᵈ`
is doubly transient if and only if `d ≥ 5`.

**Theorem 1.2 (explosion).** On such a graph, let the masses `σ(v)` be i.i.d. with mean `μ`.

1. If `μ ∈ (1, ∞]`, then `P(σ stabilizes) = 0`.
2. If `μ = 1` and either `Var(σ(v)) ∈ (0, ∞)`, or `σ(v) ≢ 1` and `σ(v) − 1` is symmetric, then
   `P(σ stabilizes) = 0`.

**Theorem 1.3 (stabilization).** On such a graph, let the masses be i.i.d. with mean
`μ ∈ [−∞, 1)`.

1. If `E[(σ⁺)^p] < ∞` for some `p > 3`, then `sup_v E[u_∞(v)^q] < ∞` for every `q ∈ [1, (p − 1)/2)`;
   in particular `σ` stabilizes almost surely.
2. If `|B(o, r)| ≤ C r^(d_f)` for some vertex `o`, some `C > 0`, some `d_f ≥ 1` and all `r ≥ 1`, and
   `E[(σ⁺)^p] < ∞` for some `p > d_f`, then `σ` stabilizes almost surely.

Section 8 shows that the conditions are nearly sharp. For every `p < 3` there are transient and
recurrent graphs of bounded degree on which masses of mean below one with a finite `p`-th moment
explode (Theorems 8.9 and 8.12). Bounded degree cannot be dropped: on some locally finite tree,
every integrable i.i.d. law stabilizes (Lemma 8.1).

## The main theorems in Lean

The main theorems are in [`RWRS/MainTheorems.lean`](RWRS/MainTheorems.lean). Their only
hypotheses are those of the paper.

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 | `RWRS.optimalStopping` |
| Theorem 1.2 | `RWRS.explosion` |
| Theorem 1.3 | `RWRS.stabilization` |

How to read the statements:

- The graph is a mathlib `SimpleGraph V` with `LocallyFinite`, together with `Infinite V`,
  `G.Connected` and a degree bound `RWRS.BoundedDegree G d`. The statements also assume
  `[MeasurableSpace V]`, and `[MeasurableSingletonClass V]` in Theorems 1.1 and 1.3.
- The i.i.d. field with one-site law `ν` is `RWRS.iidLaw V ν`. `RWRS.HasExtMean ν` says that the
  mean exists in `[−∞, ∞]`, excluding the case `E[σ⁺] = E[σ⁻] = ∞` as the paper does, and the mean
  is `RWRS.extMean ν`.
- Quantities that may be infinite live in `ℝ≥0∞`: the limiting odometer `RWRS.odometerLimit G σ v`,
  the suprema `RWRS.supMeanPayoff` and `RWRS.supStopValue`, and the moments, written as integrals
  `∫⁻`. A finite moment is stated as `≠ ⊤`, and `E[(σ⁺)^p] < ∞` as `RWRS.posMoment ν p ≠ ⊤`.
- Theorem 1.2 states that the set `{σ | RWRS.Stabilizes G σ}` has measure `0`. In Theorem 1.3, the
  growth hypothesis is `RWRS.VolumeGrowthUpper G o C d_f`.

## All numbered results

The table lists each numbered theorem, lemma, proposition and corollary of the paper with the Lean
declaration that proves it. The statements of the declarations in `RWRS.Frozen` are in
[`RWRS/Frozen/`](RWRS/Frozen/), one per file.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `RWRS.optimalStopping` | Explosion and stabilization of optimal stopping for random walk in random scenery. |
| Theorem 1.2 | `RWRS.explosion` | Explosion for mean above one, and at mean one under a variance or symmetry condition. |
| Theorem 1.3 | `RWRS.stabilization` | Below mean one, moment bounds on the odometer and almost sure stabilization. |
| Proposition 2.3 | `RWRS.Frozen.iidStationary` | i.i.d. marks on a stationary random rooted graph give a stationary random rooted network. |
| Theorem 2.4 | `RWRS.stationaryPhase` | On stationary random graphs, i.i.d. masses explode if `μ > 1` and stabilize if `μ < 1`. |
| Theorem 2.5 | `RWRS.Frozen.stationaryToppling` | On stationary networks, toppling preserves stationarity and the degree-weighted mass. |
| Lemma 2.6 | `RWRS.Frozen.ergodicMarked` | i.i.d. marking preserves ergodicity. |
| Lemma 2.7 | `RWRS.zeroOneStationary` | On stationary graphs, stabilization has conditional probability `0` or `1` given the invariant σ-field. |
| Lemma 3.1 | `RWRS.Frozen.recursion` | The recursion `u_{n+1}(x) = (average of u_n over the neighbours + ζ(x))⁺`. |
| Theorem 3.2 | `RWRS.Frozen.randomWalkRepresentation` | `u_n(x)` is the optimal-stopping value `sup_{τ ≤ n} E_x[S_τ]`, attained at an explicit time. |
| Proposition 3.3 | `RWRS.Frozen.finiteVolume` | Finite-volume reduction of the stopping problem. |
| Theorem 3.4 | `RWRS.Frozen.nestedVolume` | `u_∞(o)` as a supremum over finite connected sets of killed Green function sums. |
| Corollary 3.5 | `RWRS.Frozen.rwInfinite` | `u_∞(x) = sup_τ E_x[S_τ \| σ]` over bounded stopping times. |
| Proposition 4.1 | `RWRS.Frozen.zeroOneLaw` | Zero-one laws for stabilization and for explosion of the walk payoff. |
| Lemma 5.1 | `RWRS.Frozen.clockNoDominance` | No single vertex dominates the inverse-degree clock. |
| Proposition 5.2 | `RWRS.Frozen.supercritical` | Explosion when `E[ξ] > 0` and the inverse-degree clock diverges. |
| Lemma 6.1 | `RWRS.Frozen.positivePart` | `E[(Σ Z_i)⁺] ≥ c B` for bounded independent centred variables. |
| Lemma 6.2 | `RWRS.Frozen.noDominance` | No single vertex dominates the fluctuation scale `Σ_n(o)`. |
| Lemma 6.3 | `RWRS.Frozen.sensitivity` | Resampling one site changes `u_n(o)` by at most `g_n(o, v) \|ξ(v) − ξ′(v)\|`. |
| Proposition 6.4 | `RWRS.Frozen.critical` | Variance bound and explosion at mean zero when the fluctuation scale diverges. |
| Proposition 6.6 | `RWRS.Frozen.doublyTransient` | Explosion at mean zero on doubly transient graphs with a uniform local trap condition. |
| Proposition 6.7 | `RWRS.Frozen.convexityReduction` | For symmetric sceneries, explosion follows from the finite-variance case. |
| Proposition 7.1 | `RWRS.Frozen.shortClock` | If `Σ_v g(o, v) < ∞`, the stopping value has finite mean. |
| Lemma 7.2 | `RWRS.Frozen.localTimeMoments` | Moment bounds on local times under a spectral dimension bound. |
| Lemma 7.3 | `RWRS.Frozen.fukNagaev` | Tail inequalities for finite sums of independent centred variables. |
| Lemma 7.4 | `RWRS.Frozen.dyadic` | Dyadic reduction of the moments of `sup_n S_n`. |
| Lemma 7.5 | `RWRS.Frozen.goodWalkBounds` | The event `max_v L_N(v) ≤ N^(α+δ)` is likely, and moment bounds on the blocks `Y_k`. |
| Proposition 7.6 | `RWRS.Frozen.subcritical` | Moment bounds below mean one under a spectral dimension bound. |
| Proposition 7.8 | `RWRS.Frozen.polyGrowth` | Stabilization on graphs with polynomial growth and sub-Gaussian displacement. |
| Lemma 8.1 | `RWRS.Frozen.unboundedDegreeTree` | A locally finite tree on which every integrable i.i.d. law stabilizes. |
| Lemma 8.2 | `RWRS.Frozen.momentSharpness` | Under heat kernel bounds, violating the moment condition makes `E[u_∞(o)]` infinite. |
| Lemma 8.3 | `RWRS.Frozen.finitePerturbation` | A single extra mass stabilizes if and only if the walk is transient. |
| Lemma 8.5 | `RWRS.Frozen.coboundary` | `σ = 1 − Δf` with `f ≥ 0` gives `u_∞ ≤ f`. |
| Proposition 8.8 | `RWRS.Frozen.combEstimates` | Electrical estimates on tree-of-pipes combs. |
| Theorem 8.9 | `RWRS.Frozen.transientNonstabilization` | For `p < 3`, a transient graph on which masses of mean below one with finite `p`-th moment explode. |
| Lemma 8.10 | `RWRS.Frozen.transientGoodPipes` | Almost surely, some pipe of every large level is good. |
| Theorem 8.12 | `RWRS.Frozen.recurrentNonstabilization` | The same for recurrent graphs of growth `d_f ∈ (max(p, 2), 3)`. |
| Lemma 8.13 | `RWRS.Frozen.gadgetGeometry` | The geometry of the gadgets of Theorem 8.12. |
| Corollary 8.14 | `RWRS.Frozen.recLocal` | Exponential growth of the local contribution. |
| Proposition 8.15 | `RWRS.Frozen.recVolumeGrowth` | Volume growth of the graph of Theorem 8.12. |
| Lemma 8.16 | `RWRS.Frozen.recGoodEvents` | The good events `E_k` are independent with probability at least `η`. |

[`CORRESPONDENCE.md`](CORRESPONDENCE.md) maps each label of the paper to its Lean declaration and
records the transcription conventions.

## Corrections

The Lean statements follow [`paper/rwrs.tex`](paper/rwrs.tex), the text of
[arXiv:2604.13968v1](https://arxiv.org/abs/2604.13968v1) with two mathematical corrections and some
typographical changes. [`paper/CHANGES_FROM_ARXIV.md`](paper/CHANGES_FROM_ARXIV.md) lists every
change with its reason.

- Both mathematical corrections concern the deduction of Theorem 1.3(ii), after Theorem 1.3 and
  after Proposition 7.8. The arXiv text says that hypothesis (H3) of Proposition 7.8 holds on every
  graph of bounded degree, which is false; the corrected text derives, from the Carne–Varopoulos
  bound, the one consequence of (H3) at `o` that the proof uses.
- Neither changes the statement of a theorem, proposition or lemma.

The unmodified arXiv source is [`paper/rwrs-arxiv.tex`](paper/rwrs-arxiv.tex), with its other files
in [`paper/arxiv/`](paper/arxiv/).

## Scope

- **Stationary graphs.** The statements of Theorem 2.4 and Lemma 2.7 in `RWRS/Frozen/` take the
  ergodic decomposition of stationary random networks as a hypothesis. It is proved, as
  `RWRS.External.ergodicDecomposition`, and the table gives the forms without it. The proof adds a
  step that the source omits;
  [`CORRESPONDENCE.md`](CORRESPONDENCE.md#proof-deviations) describes it.
- **The model.** The parallel toppling procedure is iterated in closed form. The i.i.d. field is
  the product law `Measure.infinitePi` on `V → ℝ`. The walk is the law of a trajectory driven by
  i.i.d. uniform choices, and the independence of walk and scenery is the product structure of
  their joint law.
- **Stopping times.** Expectations at a bounded horizon are written with the first-step recursion of
  the walk. A stopping time is a function of the trajectory whose value at `k` is decided by its
  first `k + 1` positions.
- **Unused hypotheses.** A few statements keep a hypothesis of the paper that their proofs do not
  use; [`CORRESPONDENCE.md`](CORRESPONDENCE.md#statements-whose-hypotheses-the-proof-does-not-use)
  lists them.
- **Not formalized.** The open questions of Section 9, the proof ideas and related work of
  Sections 1.1 and 1.2, the examples and remarks, and the figures.

## Checking the proofs

- **No `sorry`.** The library has none, and `tools/check_manifest.py` rejects any `sorry`, `admit`,
  `axiom` or `sorryAx` in `RWRS/`. Each of the three comparator challenges under
  [`RWRSAudit/`](RWRSAudit/) contains one intentional `sorry` at the statement, which the matching
  solution proves.
- **Standard axioms only.** [`RWRS/Meta/AxiomsAudit.lean`](RWRS/Meta/AxiomsAudit.lean) prints the
  axioms of the main theorems and of Theorem 2.4 and Lemma 2.7, and `python3 tools/check_axioms.py`
  checks the axiom closure of every registered declaration: exactly `propext`,
  `Classical.choice` and `Quot.sound`.
- **Pinned statements.** Each statement of the paper is registered in
  [`ledger/manifest.yaml`](ledger/manifest.yaml), with the SHA-256 of its Lean text and the label
  and line range it transcribes; `tools/check_manifest.py` checks the hashes.
  [`CERTIFICATE.md`](CERTIFICATE.md) records the build and the axiom closure of each statement.
- **Independent check of the statements.** Each main theorem has a comparator pair in
  [`RWRSAudit/`](RWRSAudit/). Each `Challenge.lean` imports mathlib alone and rebuilds the model it
  uses, from the graph Laplacian and parallel toppling to the law of the walk and the i.i.d.
  scenery. [leanprover/comparator](https://github.com/leanprover/comparator) checks that the
  solution proves it with only the three standard axioms, through the Lean kernel and the
  independent nanoda kernel. See [`RWRSAudit/README.md`](RWRSAudit/README.md) and
  [`RWRSAudit/COMPARATOR_RUNS.md`](RWRSAudit/COMPARATOR_RUNS.md).
- **Continuous integration.** The **CI** workflow ([`build.yml`](.github/workflows/build.yml))
  builds the library, rejecting any warning, builds the axiom audit and checks the statement
  hashes. The **Comparator audit** workflow ([`comparator.yml`](.github/workflows/comparator.yml))
  runs the three pairs. Both run on pushes to `main` that change Lean files, `tools/`, `paper/`,
  `ledger/`, `formalization.yaml` or the build configuration, and can be started manually from the
  [Actions page](https://github.com/nitromannitol/Divisible-Sandpile-RWRS/actions).

<!-- STATUS-BEGIN (generated by tools/sync_docs.py) -->

Status: **51 registered nodes: 50 PROVED (statements of the paper, proved and independently audited), 1 FROZEN (cited external inputs, stated as hypotheses; 0 of them with a proved companion, 1 proved by a separate theorem).**

The PROVED count includes 41 paper statements and 0 companion theorems. Their proofs are machine-checked,
and their axiom closures are exactly Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, and no axiom added by this development.
Run `python3 tools/check_axioms.py` to verify the registered theorems.

Cited inputs proved by a separate theorem: `X-009` (`RWRS.External.ergodicDecomposition` in `RWRS/Support/ErgodicDecomposition.lean`).
The frozen statements that carry them are restated without them by applying
that theorem.

Cited inputs proved outright, as ordinary proved theorem nodes: `X-001` (`RWRS.External.vonBahrEsseen`), `X-002` (`RWRS.External.fukNagaevTail`), `X-003` (`RWRS.External.bernstein`), `X-004` (`RWRS.External.heatKernelBoundedDegree_of_connected`), `X-005` (`RWRS.External.carneVaropoulos`), `X-006` (`RWRS.External.heatKernelVanishing_of_connected`), `X-007` (`RWRS.External.efronStein`), `X-008` (`RWRS.External.voltageFunction_of_connected`).
No frozen statement carries any of them as a hypothesis.

This section is generated by `python3 tools/sync_docs.py --write`.

<!-- STATUS-END -->

`RWRS.lean` and `RWRS/` contain 358 Lean files with 52,210 lines, built on mathlib and
Lattice-Probability. The comparator sources are 12 files with 1,813 lines.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get      # prebuilt mathlib
lake build RWRS         # compile the library
```

Lattice-Probability has no prebuilt cache, so the first build compiles it as well as the
library. `import RWRS` loads the whole development, and `import RWRS.MainTheorems` loads the
main theorems and what they use. The dependencies are public repositories, pinned to exact commits
in [`lake-manifest.json`](lake-manifest.json):

- mathlib: `https://github.com/leanprover-community/mathlib4` at
  `81a5d257c8e410db227a6665ed08f64fea08e997`;
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `9d44b4d4670df393bb86ac5a4e042f215001cddf`.

To reproduce the axiom reports, build the comparator pairs and run the checkers (Python 3 and
PyYAML, `pip install pyyaml`):

```bash
lake build RWRS.Meta.AxiomsAudit   # the axioms of the main theorems
lake build RWRSAudit               # the comparator challenges and solutions
python3 tools/check_manifest.py    # statement hashes; no sorry, admit or axiom
python3 tools/check_axioms.py      # the axiom closure of every registered declaration
python3 tools/check_warnings.py    # the build emits no warning
python3 tools/check_constants.py   # existential constants are not bound after the parameters
python3 tools/check_coverage.py    # every labelled result of the paper is registered
```

`tools/` also holds `paper_anchors.py` and `paper_citations.py`, which check the line anchors
against the paper, and the generators `sync_docs.py`, `assumptions.py`, `certificate.py` and
`freeze.py`. See [`CONTRIBUTING.md`](CONTRIBUTING.md) for further notes.

## Running the comparators

Each pair has a configuration `RWRSAudit/<Pair>/comparator.json`, for `<Pair>` one of
`OptimalStopping`, `Explosion` and `Stabilization`, that permits exactly `propext`,
`Classical.choice` and `Quot.sound` and enables the nanoda kernel. Build `leanprover/comparator`,
`lean4export`, `landrun` and `nanoda_lib` at the revisions pinned in
[`.github/workflows/comparator.yml`](.github/workflows/comparator.yml), then run from the repository
root

```bash
COMPARATOR_LANDRUN=<landrun> COMPARATOR_LEAN4EXPORT=<lean4export> COMPARATOR_NANODA=<nanoda_bin> \
  lake env <comparator>/.lake/build/bin/comparator RWRSAudit/<Pair>/comparator.json
```

A pair passes when the comparator prints `Your solution is okay!`.

## Repository layout

```text
RWRS.lean                 the root module
RWRS/
  MainTheorems.lean       the main theorems, stated in full
  StationaryTheorems.lean Theorem 2.4 and Lemma 2.7 without the decomposition hypothesis
  Frozen/                 the statements of the paper, one per file
  External/               the results quoted from other works, with their proofs
  Support/                the lemmas and constructions used by the proofs
  Meta/AxiomsAudit.lean   the axiom reports
  Zd/                     the specialization to ℤᵈ
  Basic.lean, Walk.lean, Scenery.lean, Setting.lean, Network.lean
                          the sandpile, the walk, the scenery, the stopping problems, networks
RWRSAudit/                the mathlib-only comparator pairs, with README.md and COMPARATOR_RUNS.md
ledger/manifest.yaml      one row per registered statement: hash, paper label, state
paper/                    rwrs.tex (corrected), rwrs-arxiv.tex, CHANGES_FROM_ARXIV.md
tools/                    the checkers and generators listed under Building
CORRESPONDENCE.md         paper and Lean, statement by statement
CERTIFICATE.md            generated record of the build and each statement's axiom closure
formalization.yaml        the disclosure of models, tooling, cost, status and review
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
