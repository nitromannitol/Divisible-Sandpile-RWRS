import RWRS.Support.DTCappedRule
import RWRS.Support.DTRuleBound
import RWRS.Support.DTRuleFubini

/-!
# Fubini for the capped rule

The payoff-plus-potential at the capped rule of Step 1 can be averaged over
the scenery before or after the walk expectation: the integrand is dominated
by the absolute scenery on `K`, which is integrable.
-/

namespace RWRS.Support

open MeasureTheory

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The payoff at the capped rule is dominated by the scenery on `K`.** -/
theorem abs_payoff_trapRuleCapped_le (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V)
    (N : ℕ) (ε : ℝ) (hdeg : ∀ v ∈ K, 0 < G.degree v) (ξ : V → ℝ) (X : ℕ → V) :
    |RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X|
      ≤ (N : ℝ) * ∑ v ∈ K, |ξ v| := by
  have hmem : ∀ k, k < trapRuleCapped G r C ℓ K N ε ξ X → X k ∈ K :=
    fun k hk => mem_of_lt_trapRuleCapped r C ℓ K N ε ξ X hk
  have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := K)
    (n := trapRuleCapped G r C ℓ K N ε ξ X) (hmem := hmem)
  have hτN : (trapRuleCapped G r C ℓ K N ε ξ X : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast trapRuleCapped_le r C ℓ K N ε ξ X
  have h2 : (trapRuleCapped G r C ℓ K N ε ξ X : ℝ) * stepBound G ξ K
      ≤ (N : ℝ) * stepBound G ξ K :=
    mul_le_mul_of_nonneg_right hτN (stepBound_nonneg ξ K)
  have h3 : stepBound G ξ K ≤ ∑ v ∈ K, |ξ v| := by
    unfold stepBound
    refine Finset.sum_le_sum fun v hv => ?_
    rw [abs_div]
    have hdeg' : |(G.degree v : ℝ)| = G.degree v :=
      abs_of_pos (by exact_mod_cast hdeg v hv)
    rw [hdeg']
    exact div_le_self (abs_nonneg _) (by exact_mod_cast (Nat.succ_le_of_lt (hdeg v hv)))
  exact le_trans h1 (le_trans h2 (mul_le_mul_of_nonneg_left h3 (by positivity)))

variable [Infinite V]

/-- **Fubini for the capped rule.** -/
theorem integral_rulePayoffCapped_add_trapPotential (hG : G.Connected)
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ) (ε : ℝ) (o : V)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hdeg : ∀ v ∈ K, 0 < G.degree v)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hint : Integrable (fun z : ℝ => |z|) ν) :
    ∫ ξ, RWRS.walkExp G N o (fun X =>
        RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
          + trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))) ∂(iidLaw V ν)
      = RWRS.walkExp G N o (fun X => ∫ ξ,
          RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
            + trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X)) ∂(iidLaw V ν)) := by
  set c : ℝ := (N : ℝ) + ∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v with hc
  have hmeas : ∀ X : ℕ → V, Measurable fun ξ : V → ℝ =>
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
        + trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X)) :=
    fun X => (measurable_payoff_trapRuleCapped r C ℓ K N ε X).add
      (measurable_trapPotential_trapRuleCapped r C ℓ K N ε X)
  have hbd : ∀ (ξ : V → ℝ) (X : ℕ → V),
      |RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
        + trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))| ≤ c * ∑ v ∈ K, |ξ v| := by
    intro ξ X
    have h1 := abs_payoff_trapRuleCapped_le r C ℓ K N ε hdeg ξ X
    have h2 := abs_trapPotential_le K hesc hdeg ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
    have h3 : |RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
        + trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))|
        ≤ |RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X|
          + |trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))| := abs_add_le _ _
    have h4 : |RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X|
        + |trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))|
        ≤ (N : ℝ) * ∑ v ∈ K, |ξ v|
          + (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v) * ∑ v ∈ K, |ξ v| :=
      add_le_add h1 h2
    refine le_trans (le_trans h3 h4) ?_
    have h5 : (N : ℝ) * ∑ v ∈ K, |ξ v|
        + (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v) * ∑ v ∈ K, |ξ v|
        = c * ∑ v ∈ K, |ξ v| := by
      simp only [hc]
      ring
    exact h5 ▸ le_rfl
  have hB : Integrable (fun ξ : V → ℝ => c * ∑ v ∈ K, |ξ v|) (iidLaw V ν) := by
    have hint' : Integrable (fun ξ : V → ℝ => ∑ v ∈ K, |ξ v|) (iidLaw V ν) := by
      have h := integrable_weighted_sum K (fun _ => (1 : ℝ)) hint
      exact Integrable.congr h (Filter.Eventually.of_forall fun ξ => by simp)
    exact hint'.const_mul c
  exact integral_walkExp hG hB N o _ hmeas hbd



end RWRS.Support