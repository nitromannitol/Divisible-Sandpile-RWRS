/-
The two elementary clauses of `prop:finite-vol`.

The stopping values bounded by the exit time of a finite set are bounded above,
because the payoff moves by at most `stepBound` per step inside the set and the
exit time is integrable; and the value is at least `0`, because stopping at once
is admissible.  Together these give the finiteness of `v_K` and the vanishing of
`v_K(o)` off the active set.
-/
import RWRS.Support.NestedLower

namespace RWRS.Support

open MeasureTheory LatticeProb.Graph
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

omit [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- Stopping at once is admissible, and its value is `0`. -/
theorem zero_mem_stopValuesExit (ξ : V → ℝ) (C : Set V) (x : V) :
    (0 : ℝ) ∈ RWRS.stopValuesExit G ξ C x := by
  refine ⟨fun _ => 0, fun k X Y _ hk => hk, fun X => by simp, ?_⟩
  simp [RWRS.payoff]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The walk is inside `C` before its exit time. -/
theorem mem_of_lt_exitTime {C : Set V} {X : ℕ → V} {k : ℕ}
    (hk : (k : ℕ∞) < LatticeProb.Graph.exitTime C X) : X k ∈ C := by
  have hmem : X ∈ stayIn C k := by
    rw [stayIn_eq_lt_exitTime]
    exact hk
  exact hmem k le_rfl

/-- **The stopping values bounded by the exit time of a finite set are bounded
above.**  This is the finiteness of `v_K` in `prop:finite-vol`. -/
theorem bddAbove_stopValuesExit (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ)
    (K : Finset V) (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (x : V) : BddAbove (RWRS.stopValuesExit G ξ (K : Set V) x) := by
  classical
  set μ : Measure (ℕ → V) := RWRS.walkLaw G x with hμ
  set bnd : ℝ := ∫ X, stepBound G ξ K
      * (((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ) : ℝ) ∂μ with hbnd
  have hbddInt : Integrable
      (fun X => stepBound G ξ K
        * (((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ) : ℝ)) μ := by
    have := LatticeProb.Graph.integrable_exitNat hdeg K hesc x
    rw [← walkLaw_eq_lib x] at this
    exact this.const_mul _
  have hfin := LatticeProb.Graph.ae_exitTime_ne_top hdeg K hesc x
  rw [← walkLaw_eq_lib x] at hfin
  refine ⟨bnd, ?_⟩
  rintro a ⟨τ, -, hτle, rfl⟩
  have hdom : (fun X => ‖RWRS.payoff G ξ (τ X) X‖) ≤ᵐ[μ]
      fun X => stepBound G ξ K
        * (((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ) : ℝ) := by
    filter_upwards [hfin] with X hX
    have hmem : ∀ k, k < τ X → X k ∈ K := by
      intro k hk
      refine mem_of_lt_exitTime (C := (K : Set V)) ?_
      exact lt_of_lt_of_le (by exact_mod_cast hk) (hτle X)
    have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := K) (n := τ X) (X := X) hmem
    have h2 : ((τ X : ℕ) : ℝ)
        ≤ (((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ) : ℝ) := by
      have : (τ X : ℕ∞) ≤ ((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ∞) := by
        rw [ENat.coe_toNat hX]
        exact hτle X
      exact_mod_cast this
    have h3 : (0 : ℝ) ≤ stepBound G ξ K := stepBound_nonneg ξ K
    rw [Real.norm_eq_abs]
    nlinarith
  calc (∫ X, RWRS.payoff G ξ (τ X) X ∂μ)
      ≤ ‖∫ X, RWRS.payoff G ξ (τ X) X ∂μ‖ := le_abs_self _
    _ ≤ ∫ X, ‖RWRS.payoff G ξ (τ X) X‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ bnd := integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun X => norm_nonneg _) hbddInt hdom

/-- The value bounded by the exit time of a finite set is nonnegative. -/
theorem zero_le_valueExit (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ)
    (K : Finset V) (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (x : V) : 0 ≤ RWRS.valueExit G ξ (K : Set V) x :=
  le_csSup (bddAbove_stopValuesExit hdeg ξ K hesc x) (zero_mem_stopValuesExit ξ _ x)

/-- **The value vanishes off the active set.**  This is the second clause of
`prop:finite-vol`. -/
theorem valueExit_eq_zero_of_not_mem_activeSet (hdeg : ∀ v : V, 0 < G.degree v)
    (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    {o : V} (hoK : o ∈ K) (ho : o ∉ RWRS.activeSet G ξ (K : Set V)) :
    RWRS.valueExit G ξ (K : Set V) o = 0 := by
  have hge := zero_le_valueExit hdeg ξ K hesc o
  have hle : ¬ (0 < RWRS.valueExit G ξ (K : Set V) o) := by
    intro hpos
    exact ho ⟨by exact_mod_cast hoK, hpos⟩
  linarith [not_lt.1 hle]

end RWRS.Support
