import RWRS.Support.DTRuleMeas
import RWRS.Support.DTRuleBound
import RWRS.Support.DTFubini
import RWRS.Support.Critical
import RWRS.Scenery

/-!
# The Fubini exchange for the trap rule

The scenery average of the walk expectation of the payoff collected by the
trap rule plus the trap potential exchanges the two integrals.  The
dominating function is the scenery on the finite set `K`, which is
integrable under the scenery law.
-/

open MeasureTheory ProbabilityTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **Finite variance gives an integrable absolute first moment.** -/
theorem integrable_abs_id_of_evar (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsq : evar ν < ⊤) : Integrable (fun z : ℝ => |z|) ν := by
  have hm : AEStronglyMeasurable (fun z : ℝ => z) ν := measurable_id.aestronglyMeasurable
  have hlp : MemLp (fun z : ℝ => z) 2 ν := by
    rw [← evariance_lt_top_iff_memLp hm]
    exact hsq
  have hint : Integrable (fun z : ℝ => z) ν := hlp.integrable one_le_two
  have : Integrable (fun z : ℝ => |id z|) ν := hint.abs
  simpa [Function.id_def] using this

/-- **The Fubini exchange for the rule payoff.**  Averaging the walk
expectation of the payoff collected by the trap rule plus the trap
potential over the scenery exchanges the two integrals: the bound is the
scenery on `K`, which is integrable. -/
theorem integral_rulePayoff_add_trapPotential [Infinite V] (hG : G.Connected)
    (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ) (ε : ℝ) (o : V)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hdeg : ∀ v ∈ K, 0 < G.degree v)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hint : Integrable (fun z : ℝ => |z|) ν) :
    ∫ ξ, RWRS.walkExp G N o (fun X =>
        RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X
          + trapPotential G K ξ (X (trapRule G r C K N ε ξ X))) ∂(iidLaw V ν)
      = RWRS.walkExp G N o (fun X => ∫ ξ,
          RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X
            + trapPotential G K ξ (X (trapRule G r C K N ε ξ X)) ∂(iidLaw V ν)) := by
  set c : ℝ := (N : ℝ) + ∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v with hc
  have hmeas : ∀ X : ℕ → V, Measurable fun ξ : V → ℝ =>
      RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X
        + trapPotential G K ξ (X (trapRule G r C K N ε ξ X)) :=
    fun X => (measurable_payoff_trapRule r C K N ε X).add
      (measurable_trapPotential_rule r C K N ε X)
  have hbd : ∀ (ξ : V → ℝ) (X : ℕ → V),
      |RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X
        + trapPotential G K ξ (X (trapRule G r C K N ε ξ X))| ≤ c * ∑ v ∈ K, |ξ v| := by
    intro ξ X
    have h1 := abs_payoff_trapRule_le r C K N ε hdeg ξ X
    have h2 := abs_trapPotential_le K hesc hdeg ξ (X (trapRule G r C K N ε ξ X))
    have h3 : |RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X
        + trapPotential G K ξ (X (trapRule G r C K N ε ξ X))|
        ≤ |RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X|
          + |trapPotential G K ξ (X (trapRule G r C K N ε ξ X))| := abs_add_le _ _
    have h4 : |RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X|
        + |trapPotential G K ξ (X (trapRule G r C K N ε ξ X))|
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