import RWRS.Support.DTStagePartition
import RWRS.Support.DTStageIdent

open scoped Classical
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **On a stage hit event the capped rule reads the scenery at the stage
time, so the hit-integral may be taken at the stage time.** -/
theorem integral_hit_rule_eq_stage (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (X : ℕ → V) {i : ℕ} (hi : i < stageCnt G r C ℓ K N X) :
    ∫ ξ : V → ℝ, (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i).indicator
        (fun ξ' => trapPotential G K ξ' (X (trapRuleCapped G r C ℓ K N ε ξ' X))) ξ
        ∂(RWRS.iidLaw V ν)
      = ∫ ξ : V → ℝ, (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i).indicator
        (fun ξ' => trapPotential G K ξ' (X ((uncTime G r C X i).toNat))) ξ
        ∂(RWRS.iidLaw V ν) :=
  integral_congr_ae (Filter.Eventually.of_forall
    (fun ξ => indicator_trapPotential_rule_eq_stage r C ℓ K hN ε X hi ξ))

end RWRS.Support
