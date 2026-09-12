import RWRS.Support.DTPotential
import RWRS.Support.DTCappedRule
import RWRS.Support.DTUnconstrained
import RWRS.Support.DTStageIntegral
import RWRS.Scenery

open scoped Classical
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The trap potential is integrable in the scenery.**  For an i.i.d.
scenery with integrable one-site law, the killed potential at any site is
an integrable function of the scenery. -/
theorem integrable_trapPotential (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℝ => z) ν)
    (K : Finset V) (x : V) :
    Integrable (fun ξ : V → ℝ => trapPotential G K ξ x) (RWRS.iidLaw V ν) := by
  unfold trapPotential
  refine integrable_finsetSum _ fun v _ => ?_
  exact (MeasurePreserving.integrable_comp_of_integrable
    (measurePreserving_eval_infinitePi (fun _ : V => ν) v) hint).mul_const _

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The capped-rule integrand is integrable in the scenery.**  Since the
rule time is capped by `N`, the site it reads lies among finitely many
trajectory sites, so the trap potential there is integrable. -/
theorem integrable_trapPotential_cappedRule (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable (fun z : ℝ => z) ν)
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ) (ε : ℝ)
    (X : ℕ → V) :
    Integrable (fun ξ : V → ℝ =>
      trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X)))
      (RWRS.iidLaw V ν) := by
  have hle : ∀ ξ : V → ℝ, trapRuleCapped G r C ℓ K N ε ξ X ≤ N :=
    fun ξ => trapRuleCapped_le r C ℓ K N ε ξ X
  have hsum : ∀ ξ : V → ℝ, trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
      = ∑ n ∈ Finset.range (N + 1),
          ({ξ' : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ' X = n}).indicator
            (fun ξ' => trapPotential G K ξ' (X n)) ξ := by
    intro ξ
    rw [Finset.sum_eq_single (trapRuleCapped G r C ℓ K N ε ξ X)]
    · simp
    · intro n _ hn
      exact Set.indicator_of_notMem (fun h => hn h.symm)
        (fun ξ' => trapPotential G K ξ' (X n))
    · intro h
      exact (h (Finset.mem_range_succ_iff.mpr (hle ξ))).elim
  have hmeas : ∀ n ∈ Finset.range (N + 1),
      MeasurableSet {ξ' : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ' X = n} := by
    intro n _
    by_cases hn : n = 0
    · subst hn
      have : {ξ' : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ' X = 0}
          = {ξ' : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ' X ≤ 0} := by
        ext ξ'; simp only [Set.mem_setOf_eq]; omega
      rw [this]; exact measurableSet_trapRuleCapped_le r C ℓ K N ε X 0
    · have : {ξ' : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ' X = n}
          = {ξ' : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ' X ≤ n}
              ∩ {ξ' : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ' X ≤ n - 1}ᶜ := by
        ext ξ'; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_setOf_eq]; omega
      rw [this]
      exact (measurableSet_trapRuleCapped_le r C ℓ K N ε X n).inter
        (MeasurableSet.compl (measurableSet_trapRuleCapped_le r C ℓ K N ε X (n - 1)))
  rw [funext hsum]
  exact integrable_finsetSum _ fun n hn =>
    (integrable_trapPotential ν hint K (X n)).indicator (hmeas n hn)

end RWRS.Support
