/-
The `ℤ^d` specializations of the random walk representation, in the vocabulary
of the two dependent formalizations.

`zdOdometer η` is the odometer written in the scenery, `u_{n+1} = (η + Pu_n)⁺`,
which is the parking formalization's `u` and the percolation formalization's
`odometerOf`.  `zdStopValues`, `zdStoppingValue` and `zdOptimalStop` are the
optimal stopping vocabulary of those formalizations, written with the shared
library's walk law on path space and its notion of a stopping time.

`parkingStopping` is the statement quoted there as `lem:stopping`, and
`sandpileOptimalStopping` is the one quoted as `thm:RW`.  Both are the general
graph theorem `RWRS.Frozen.randomWalkRepresentation` read on the lattice,
through the identification of the two forms of the walk expectation.
-/
import RWRS.Support.ZdBridge
import RWRS.Frozen.RandomWalkRepresentation

open MeasureTheory LatticeProb

namespace RWRS.Zd

variable {d : ℕ}

/-- The odometer written in the scenery, `u_0 = 0`, `u_{n+1} = (η + P u_n)⁺`. -/
noncomputable def zdOdometer (η : Site d → ℝ) : ℕ → Site d → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max 0 (η x + LatticeProb.walkOp (zdOdometer η n) x)

/-- The configuration whose scenery is `η`: `σ = 2dη + 1`. -/
noncomputable def config (η : Site d → ℝ) : Site d → ℝ := fun z => 2 * d * η z + 1

theorem scenery_config [NeZero d] (η : Site d → ℝ) (x : Site d) :
    RWRS.scenery (lattice d) (config η) x = η x := by
  have hd : ((2 * d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  rw [RWRS.scenery, config, degree_eq]
  field_simp
  push_cast
  ring

theorem excess_config [NeZero d] (η : Site d → ℝ) :
    RWRS.excess (config η) = fun z => 2 * d * η z := by
  funext z
  simp [RWRS.excess, config]

theorem zdOdometer_eq [NeZero d] (η : Site d → ℝ) :
    ∀ (n : ℕ) (x : Site d), RWRS.odometer (lattice d) (config η) n x = zdOdometer η n x := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
      intro x
      have hfun : RWRS.odometer (lattice d) (config η) n = zdOdometer η n := funext ih
      rw [RWRS.Frozen.recursion (latticeConnected d) _ n x, walkOp_eq, scenery_config,
        hfun, zdOdometer]
      simp only []
      rw [max_comm, add_comm]

/-- `S_n = ∑_{k<n} ζ(X_k)`, the scenery sum along the trajectory. -/
noncomputable def sceneryPartialSum (ζ : Site d → ℝ) (n : ℕ) (X : ℕ → Site d) : ℝ :=
  ∑ k ∈ Finset.range n, ζ (X k)

/-- The set of expected payoffs over stopping times bounded by `n`, as the
dependent formalizations write it. -/
noncomputable def zdStopValues (ζ : Site d → ℝ) (n : ℕ) (x : Site d) : Set ℝ :=
  {a | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
    a = ∫ X, sceneryPartialSum ζ (τ X) X ∂(siteWalkLaw d x)}

/-- `v_n(x) = sup_{τ ≤ n} E_x[S_τ]`. -/
noncomputable def zdStoppingValue (ζ : Site d → ℝ) (n : ℕ) (x : Site d) : ℝ :=
  sSup (zdStopValues ζ n x)

/-- `τ_n^* = min{0 ≤ k ≤ n : v_{n-k}(X_k) = 0}`. -/
noncomputable def zdOptimalStop (ζ : Site d → ℝ) (n : ℕ) (X : ℕ → Site d) : ℕ :=
  sInf {k : ℕ | k ≤ n ∧ zdStoppingValue ζ (n - k) (X k) = 0}

theorem payoff_eq [NeZero d] (ζ : Site d → ℝ) (n : ℕ) (X : ℕ → Site d) :
    RWRS.payoff (lattice d) (RWRS.excess (config ζ)) n X = sceneryPartialSum ζ n X := by
  rw [excess_config, RWRS.payoff, sceneryPartialSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [degree_eq]
  have hd : ((2 * d : ℕ) : ℝ) ≠ 0 := by
    have : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
    positivity
  field_simp
  push_cast
  ring

theorem payoff_dependsUpTo [NeZero d] (ζ : Site d → ℝ) (n : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : RWRS.IsStopping τ) (hle : ∀ X, τ X ≤ n) :
    ∀ X Y : ℕ → Site d, (∀ j ≤ n, X j = Y j) →
      RWRS.payoff (lattice d) (RWRS.excess (config ζ)) (τ X) X
        = RWRS.payoff (lattice d) (RWRS.excess (config ζ)) (τ Y) Y := by
  intro X Y hXY
  have hτXY : τ X = τ Y := (hτ (τ X) X Y (fun j hj => hXY j (le_trans hj (hle X))) rfl).symm
  rw [hτXY, RWRS.payoff, RWRS.payoff]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hXY k (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) (hle Y)))]

theorem walkExp_eq_integral [NeZero d]
    (ζ : Site d → ℝ) (n : ℕ) (x : Site d) {τ : (ℕ → Site d) → ℕ}
    (hτ : RWRS.IsStopping τ) (hle : ∀ X, τ X ≤ n) :
    RWRS.walkExp (lattice d) n x
        (fun X => RWRS.payoff (lattice d) (RWRS.excess (config ζ)) (τ X) X)
      = ∫ X, sceneryPartialSum ζ (τ X) X ∂(siteWalkLaw d x) := by
  have hdep := payoff_dependsUpTo ζ n hτ hle
  rw [RWRS.Support.walkExp_eq_integral_siteWalkLaw d n x _
    (LatticeProb.measurable_of_dependsUpTo hdep) hdep]
  exact integral_congr_ae (Filter.Eventually.of_forall fun X => payoff_eq ζ (τ X) X)

theorem stopValues_eq [NeZero d]
    (ζ : Site d → ℝ) (n : ℕ) (x : Site d) :
    RWRS.stopValues (lattice d) (RWRS.excess (config ζ)) n x = zdStopValues ζ n x := by
  ext a
  constructor
  · rintro ⟨τ, hτ, hle, rfl⟩
    exact ⟨τ, hτ, hle, walkExp_eq_integral ζ n x hτ hle⟩
  · rintro ⟨τ, hτ, hle, rfl⟩
    exact ⟨τ, hτ, hle, (walkExp_eq_integral ζ n x hτ hle).symm⟩

/-- The statement the parking formalization quotes as `lem:stopping`. -/
theorem parkingStopping (d : ℕ) (hd : 1 ≤ d) (η : Site d → ℝ) (n : ℕ) (x : Site d) :
    IsLUB (zdStopValues η n x) (zdOdometer η n x) := by
  haveI : NeZero d := ⟨by omega⟩
  rw [← stopValues_eq, ← zdOdometer_eq]
  exact (RWRS.Frozen.randomWalkRepresentation (latticeConnected d) (config η) n x).1

/-- The statement the percolation formalization quotes as `thm:RW`. -/
theorem sandpileOptimalStopping (d : ℕ) (hd : 1 ≤ d) (ζ : Site d → ℝ) (n : ℕ) (x : Site d) :
    zdOdometer ζ n x = zdStoppingValue ζ n x ∧
      zdStoppingValue ζ n x
        = ∫ X, sceneryPartialSum ζ (zdOptimalStop ζ n X) X ∂(siteWalkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  have hval : ∀ (m : ℕ) (z : Site d),
      zdStoppingValue ζ m z = RWRS.value (lattice d) (RWRS.excess (config ζ)) m z := by
    intro m z
    rw [zdStoppingValue, RWRS.value, stopValues_eq]
  have hstop : ∀ (m : ℕ) (X : ℕ → Site d),
      zdOptimalStop ζ m X = RWRS.optimalStop (lattice d) (RWRS.excess (config ζ)) m X := by
    intro m X
    rw [zdOptimalStop, RWRS.optimalStop]
    congr 1
    ext k
    simp only [Set.mem_setOf_eq, hval]
  have hrep := RWRS.Frozen.randomWalkRepresentation (latticeConnected d) (config ζ) n x
  have hsup : RWRS.value (lattice d) (RWRS.excess (config ζ)) n x
      = RWRS.odometer (lattice d) (config ζ) n x :=
    hrep.1.csSup_eq ⟨0, RWRS.Support.zero_mem_stopValues (latticeConnected d) _ n x⟩
  refine ⟨?_, ?_⟩
  · rw [hval, hsup, zdOdometer_eq]
  · rw [hval, hsup]
    simp only [hstop]
    rw [hrep.2]
    exact walkExp_eq_integral ζ n x
      (RWRS.Support.isStopping_optimalStop (latticeConnected d) (config ζ) n)
      (RWRS.Support.optimalStop_le (latticeConnected d) (config ζ) n)

end RWRS.Zd
