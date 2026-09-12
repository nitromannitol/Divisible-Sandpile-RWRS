/-
Domination bounds for the payoff collected by the Step-1 rule and for the
killed potential, in terms of the scenery on the finite set `K`.
-/
import RWRS.Support.DTStages
import RWRS.Support.NestedLower
import RWRS.Support.DTPotential
import RWRS.Support.GreenUnique
import RWRS.Support.KilledGreen

open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The payoff collected by the rule is dominated by the scenery on `K`.**
The walk is inside `K` before the rule fires, so every collected term is a
scenery value at a site of `K`, and the degrees are at least one. -/
theorem abs_payoff_trapRule_le (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ)
    (ε : ℝ) (hdeg : ∀ v ∈ K, 0 < G.degree v) (ξ : V → ℝ) (X : ℕ → V) :
    |RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X| ≤ (N : ℝ) * ∑ v ∈ K, |ξ v| := by
  have hmem : ∀ k, k < trapRule G r C K N ε ξ X → X k ∈ K :=
    fun k hk => mem_of_lt_trapRule r C K N ε ξ X hk
  have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := K) (n := trapRule G r C K N ε ξ X) (hmem := hmem)
  have hτN : (trapRule G r C K N ε ξ X : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast trapRule_le r C K N ε ξ X
  have h2 : (trapRule G r C K N ε ξ X : ℝ) * stepBound G ξ K
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


/-- **The trap potential is dominated by the scenery on `K`.**  The killed
Green function is largest at its source, so the potential at any position is
bounded by the diagonal values times the absolute scenery on `K`. -/
theorem abs_trapPotential_le (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hdeg : ∀ v ∈ K, 0 < G.degree v) (ξ : V → ℝ) (y : V) :
    |trapPotential G K ξ y|
      ≤ (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v) * ∑ v ∈ K, |ξ v| := by
  calc |trapPotential G K ξ y|
      ≤ ∑ v ∈ K, |ξ v * RWRS.killedGreenReal G (K : Set V) v y| := by
        simp only [trapPotential]
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v ∈ K, |ξ v| * RWRS.killedGreenReal G (K : Set V) v v := by
        refine Finset.sum_le_sum fun v hv => ?_
        rw [abs_mul, abs_of_nonneg (killedGreenReal_nonneg_of_escape K hesc v y)]
        exact mul_le_mul_of_nonneg_left (killedGreenReal_le_source K hesc hdeg hv y)
          (abs_nonneg _)
    _ ≤ (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v) * ∑ v ∈ K, |ξ v| := by
        refine le_trans (Finset.sum_le_sum fun v hv =>
          mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (f := fun w => |ξ w|) (fun w _ => abs_nonneg _) hv)
            (killedGreenReal_nonneg_of_escape K hesc v v)) ?_
        rw [← Finset.mul_sum]
        exact le_of_eq (mul_comm _ _)


end RWRS.Support
