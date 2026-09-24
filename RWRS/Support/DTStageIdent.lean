import RWRS.Support.DTStageFire
import RWRS.Support.DTStageIntegral

open scoped Classical
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **On a hit event the capped rule reads the scenery at the stage time.**
The indicator of the stage-`i` hit event times the trap potential at the
capped rule equals the same indicator times the trap potential at the
stage-`i` time, for every usable stage `i`. -/
theorem indicator_trapPotential_rule_eq_stage (r : ℕ) (C : V → Finset V)
    (ℓ : ℕ) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ) (X : ℕ → V)
    {i : ℕ} (hi : i < stageCnt G r C ℓ K N X) (ξ : V → ℝ) :
    (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i).indicator
      (fun ξ' => trapPotential G K ξ' (X (trapRuleCapped G r C ℓ K N ε ξ' X))) ξ
      = (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i).indicator
      (fun ξ' => trapPotential G K ξ' (X ((uncTime G r C X i).toNat))) ξ := by
  by_cases hmem : ξ ∈ hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
      trapRuleCapped_eq_stageTime_of_hitEvent r C ℓ K hN ε X hi ξ hmem]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

end RWRS.Support
