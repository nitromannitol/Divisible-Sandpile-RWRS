import Mathlib

/-!
# Theorem 1.1 (`thm:OS`): comparator challenge

Mathlib-only comparator challenge for Theorem 1.1 (`thm:OS`) of Bou-Rabee, Peres and Sava-Huss,
*Divisible sandpiles via random walks in random scenery* (arXiv:2604.13968).  The certified
statement is `RWRS.Frozen.optimalStopping`, restated in `RWRS/MainTheorems.lean` as
`RWRS.optimalStopping`.  Content: for simple random walk `X` on an infinite, connected graph of
degree at most `d` and an i.i.d. scenery `ξ` of law `ν`, independent of the walk, with
`S_n = ∑_{k<n} ξ(X_k)/deg(X_k)`: if `E[ξ] > 0` then `sup_n E_x[S_n | ξ] = ∞` almost surely; if
`E[ξ] = 0` with positive finite variance, or with `ξ ≢ 0` symmetric, then
`sup_τ E_x[S_τ | ξ] = ∞` almost surely over bounded stopping times, and `sup_n E_x[S_n | ξ] = ∞`
if the graph is not doubly transient; if `E[ξ] < 0` and `E[(ξ⁺)^p] < ∞` for some `p > 3`, then
`E_x[(sup_n S_n)^q] < ∞` for every `q ∈ [1, (p-1)/2)`.

Only Mathlib is imported.  The vocabulary between `VOCABULARY-BEGIN` and
`VOCABULARY-END` rebuilds, from Mathlib primitives, every definition needed to
read the theorem: the averaging operator and the Laplacian of a locally finite
graph, the parallel toppling procedure and its odometer, the heat kernel and
the Green function, the walk payoff and bounded stopping times, the law of the
simple random walk on path space, the i.i.d. scenery and its moments, the
optimal stopping suprema, double transience, a degree bound, volume growth,
and the cited results.  It is a statement-level copy of the repository
definitions (see `Audit/README.md` for the provenance table) and is
byte-identical in all three challenges.  The sole intentional `sorry` is the
proof of the final theorem.

## Cited results

The paper uses results from the literature without proof.  The bounded
voltage function of Lyons–Peres, Proposition 2.1 and equation (2.4), is proved
inside the repository on every infinite connected graph, recurrent or transient
(`RWRS.External.voltageFunction_of_connected`), and is used only inside the
proof, so it is not a hypothesis of this theorem.

## Presentation deltas

None at the level of the displayed statement: the theorem below is the
statement of `RWRS.optimalStopping` with every repository name replaced by its
vocabulary copy.  Relative to the frozen statement `RWRS.Frozen.optimalStopping`, it omits
the hypotheses for the von Bahr–Esseen and Fuk–Nagaev inequalities and the bounded-degree
heat kernel bound, which the repository proves and
`RWRS/MainTheorems.lean` discharges; that is a strengthening.
-/

-- VOCABULARY-BEGIN
namespace RWRSAudit

open MeasureTheory
open scoped ENNReal

variable {V : Type*}

/-! ## 1. The graph operators and the divisible sandpile (`rwrs.tex:94-110`) -/

/-- The one-step averaging operator `(P f)(x) = deg(x)⁻¹ ∑_{y ∼ x} f(y)`. -/
noncomputable def walkOp (G : SimpleGraph V) [G.LocallyFinite] (f : V → ℝ) (x : V) : ℝ :=
  (∑ y ∈ G.neighborFinset x, f y) / G.degree x

/-- The discrete Laplacian `Δf(x) = ∑_{y ∼ x} (f(y) - f(x))`. -/
noncomputable def laplacian (G : SimpleGraph V) [G.LocallyFinite] (f : V → ℝ) (x : V) : ℝ :=
  ∑ y ∈ G.neighborFinset x, (f y - f x)

/-- The closed ball `B(x,r) = {v : dist(v,x) ≤ r}`. -/
def closedBall (G : SimpleGraph V) (x : V) (r : ℕ) : Set V := {v | G.edist v x ≤ r}

/-- The mass emitted by `v` in one round of parallel toppling,
`(σ(v) - 1)⁺ / deg(v)`. -/
noncomputable def emission (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (v : V) : ℝ :=
  max (σ v - 1) 0 / G.degree v

/-- One round of parallel toppling, `eq:sigma-update`. -/
noncomputable def topple (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (v : V) : ℝ :=
  min (σ v) 1 + ∑ w ∈ G.neighborFinset v, emission G σ w

/-- The configuration `σ_n` after `n` rounds of parallel toppling. -/
noncomputable def config (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (n : ℕ) : V → ℝ :=
  (topple G)^[n] σ

/-- The odometer `u_n(v) = ∑_{k<n} (σ_k(v) - 1)⁺/deg(v)` of `eq:u-update`. -/
noncomputable def odometer (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (n : ℕ) (v : V) : ℝ :=
  ∑ k ∈ Finset.range n, emission G (config G σ k) v

/-- The limiting odometer `u_∞(v) ∈ [0,∞]`. -/
noncomputable def odometerLimit (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) (v : V) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (odometer G σ n v)

/-- The configuration `σ` stabilizes: `u_∞(v) < ∞` for every vertex. -/
def Stabilizes (G : SimpleGraph V) [G.LocallyFinite] (σ : V → ℝ) : Prop :=
  ∀ v : V, odometerLimit G σ v ≠ ⊤

/-! ## 2. The heat kernel and the Green function (`rwrs.tex:196-215`) -/

open scoped Classical in
/-- The `k`-step transition probability `p_k(x,y) = P_x(X_k = y)`. -/
noncomputable def heat (G : SimpleGraph V) [G.LocallyFinite] : ℕ → V → V → ℝ
  | 0 => fun x y => if x = y then 1 else 0
  | k + 1 => fun x y => walkOp G (fun z => heat G k z y) x

/-- The Green function `g(x,v)` of `eq:green-def`, valued in `[0,∞]`. -/
noncomputable def green (G : SimpleGraph V) [G.LocallyFinite] (x v : V) : ℝ≥0∞ :=
  (∑' k : ℕ, ENNReal.ofReal (heat G k x v)) / (G.degree v : ℝ≥0∞)

/-! ## 3. The walk, its payoff and bounded stopping times (`rwrs.tex:94-101`) -/

/-- `cons x X` prepends the position `x` to the trajectory `X`. -/
def cons (x : V) (X : ℕ → V) : ℕ → V
  | 0 => x
  | k + 1 => X k

/-- `walkExp G n x F = E_x[F(X)]`, for a functional `F` of the trajectory that
is determined by the first `n+1` positions.  It is the first-step average of
the walk, iterated `n` times. -/
noncomputable def walkExp (G : SimpleGraph V) [G.LocallyFinite] :
    ℕ → V → ((ℕ → V) → ℝ) → ℝ
  | 0, x, F => F (fun _ => x)
  | n + 1, x, F =>
      (∑ y ∈ G.neighborFinset x, walkExp G n y (fun X => F (cons x X))) / G.degree x

/-- `τ` is a stopping time for the natural filtration of the walk: whether it
takes the value `k` is decided by the positions up to time `k`. -/
def IsStopping (τ : (ℕ → V) → ℕ) : Prop :=
  ∀ (k : ℕ) (X Y : ℕ → V), (∀ j ≤ k, X j = Y j) → τ X = k → τ Y = k

/-- The walk payoff `S_n = ∑_{k<n} ξ(X_k)/deg(X_k)` of `thm:OS`. -/
noncomputable def payoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ)
    (X : ℕ → V) : ℝ :=
  ∑ k ∈ Finset.range n, ξ (X k) / G.degree (X k)

/-- The set of expected payoffs `E_x[S_τ]` over stopping times bounded by `n`. -/
noncomputable def stopValues (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ)
    (x : V) : Set ℝ :=
  {a | ∃ τ : (ℕ → V) → ℕ, IsStopping τ ∧ (∀ X, τ X ≤ n) ∧
    a = walkExp G n x (fun X => payoff G ξ (τ X) X)}

/-! ## 4. The walk on path space -/

/-- The uniform law on `[0,1)`, the law of one instruction. -/
noncomputable def stepLaw : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

/-- The law of the instruction sequence that drives the walk. -/
noncomputable def driverLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => stepLaw

/-- The neighbour of `x` selected by the instruction `u ∈ [0,1)`. -/
noncomputable def stepTo (G : SimpleGraph V) [G.LocallyFinite] (x : V) (u : ℝ) : V :=
  ((G.neighborFinset x).toList).getD ⌊(G.degree x : ℝ) * u⌋₊ x

/-- The trajectory started at `x` and driven by the instructions `ω`. -/
noncomputable def walkPath (G : SimpleGraph V) [G.LocallyFinite] (x : V) (ω : ℕ → ℝ) : ℕ → V
  | 0 => x
  | k + 1 => stepTo G (walkPath G x ω k) (ω k)

/-- The law `P_x` of the simple random walk started at `x`, on path space. -/
noncomputable def walkLaw (G : SimpleGraph V) [G.LocallyFinite] [MeasurableSpace V] (x : V) :
    Measure (ℕ → V) :=
  driverLaw.map (walkPath G x)

/-- `sup_n S_n`, in `[0,∞]`; the supremum is at least `S_0 = 0`. -/
noncomputable def supPayoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (X : ℕ → V) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (payoff G ξ n X)

/-! ## 5. The i.i.d. scenery and its moments (`ssec:notation`) -/

/-- The law of an i.i.d. field indexed by `V` with common marginal `ν`. -/
noncomputable def iidLaw (V : Type*) (ν : Measure ℝ) : Measure (V → ℝ) :=
  Measure.infinitePi fun _ : V => ν

/-- `E[σ⁺]`, in `[0,∞]`. -/
noncomputable def posPart (ν : Measure ℝ) : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal z ∂ν

/-- `E[σ⁻]`, in `[0,∞]`. -/
noncomputable def negPart (ν : Measure ℝ) : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (-z) ∂ν

/-- The extended expectation `E[σ] ∈ [-∞,∞]` of `ssec:notation`. -/
noncomputable def extMean (ν : Measure ℝ) : EReal := (posPart ν : EReal) - (negPart ν : EReal)

/-- The convention of `ssec:notation`: the indeterminate case
`E[σ⁺] = E[σ⁻] = ∞` is excluded. -/
def HasExtMean (ν : Measure ℝ) : Prop := posPart ν ≠ ⊤ ∨ negPart ν ≠ ⊤

/-- `E[(σ⁺)^p]`, in `[0,∞]`. -/
noncomputable def posMoment (ν : Measure ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (max z 0 ^ p) ∂ν

/-- The law `ν` is symmetric about `0`. -/
def IsSymmetric (ν : Measure ℝ) : Prop := ν.map (fun z => -z) = ν

/-- The variance of the marginal, in `[0,∞]`. -/
noncomputable def evar (ν : Measure ℝ) : ℝ≥0∞ := ProbabilityTheory.evariance id ν

/-! ## 6. The optimal stopping problem and the graph hypotheses -/

/-- `E_x[S_n | ξ]`, the expected payoff at the deterministic time `n`. -/
noncomputable def meanPayoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (n : ℕ) (x : V) :
    ℝ :=
  walkExp G n x (payoff G ξ n)

/-- `sup_n E_x[S_n | ξ]`, in `[0,∞]`. -/
noncomputable def supMeanPayoff (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (x : V) :
    ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (meanPayoff G ξ n x)

/-- `sup_τ E_x[S_τ | ξ]` over bounded stopping times, in `[0,∞]`. -/
noncomputable def supStopValue (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (x : V) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (a : ℝ) (_ : a ∈ stopValues G ξ n x), ENNReal.ofReal a

/-- The joint law of the i.i.d. scenery with marginal `ν` and of the walk
started at `x`; the product records that the walk is independent of the
scenery. -/
noncomputable def jointLaw (G : SimpleGraph V) [G.LocallyFinite] [MeasurableSpace V]
    (ν : Measure ℝ) (x : V) : Measure ((V → ℝ) × (ℕ → V)) :=
  (iidLaw V ν).prod (walkLaw G x)

/-- `G` is doubly transient: `∑_v g(o,v)^2 < ∞` for every `o`. -/
def DoublyTransient (G : SimpleGraph V) [G.LocallyFinite] : Prop :=
  ∀ o : V, (∑' v : V, green G o v ^ 2) ≠ ⊤

/-- The degree of `G` is bounded by `d`. -/
def BoundedDegree (G : SimpleGraph V) [G.LocallyFinite] (d : ℕ) : Prop :=
  ∀ v : V, G.degree v ≤ d

/-- The volume growth hypothesis `|B(o,r)| ≤ C r^{d_f}` for all `r ≥ 1`. -/
def VolumeGrowthUpper (G : SimpleGraph V) (o : V) (C d_f : ℝ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → (closedBall G o r).encard ≤ ENNReal.ofReal (C * (r : ℝ) ^ d_f)

/-! ## 7. The cited results -/

namespace External

/-- The pointwise Carne--Varopoulos bound for simple random walk on a connected,
nontrivial, locally finite graph with measurable singletons, assumed.  Sources:
Carne (1985), Varopoulos (1985), Lyons--Peres, Theorem 13.4 (`rwrs.tex:143-149`). -/
def CarneVaropoulos {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    [MeasurableSpace V] : Prop :=
  MeasurableSingletonClass V → Nontrivial V → G.Connected →
    ∀ (x y : V) (n : ℕ), 1 ≤ n →
      walkLaw G x {X : ℕ → V | X n = y} ≤
        ENNReal.ofReal (2 * Real.sqrt ((G.degree y : ℝ) / G.degree x) *
          Real.exp (-((G.dist x y : ℝ) ^ 2) / (2 * n)))

end External

end RWRSAudit
-- VOCABULARY-END

namespace RWRSAudit

open MeasureTheory
open scoped ENNReal

universe u

/-- Theorem 1.1 (`thm:OS`). -/
theorem optimalStopping {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : HasExtMean ν) :
    (0 < extMean ν →
      ∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ x = ⊤) ∧
    (extMean ν = 0 →
      ((0 < evar ν ∧ evar ν < ⊤) ∨ (ν ≠ Measure.dirac 0 ∧ IsSymmetric ν)) →
      (∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supStopValue G ξ x = ⊤) ∧
      (¬ DoublyTransient G →
        ∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ x = ⊤)) ∧
    (extMean ν < 0 → ∀ p : ℝ, 3 < p → posMoment ν p ≠ ⊤ →
      ∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 → ∀ x : V,
        (∫⁻ z, supPayoff G z.1 z.2 ^ q ∂(jointLaw G ν x)) ≠ ⊤) := by
  sorry

end RWRSAudit
