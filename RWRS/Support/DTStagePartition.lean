import RWRS.Support.DTStageIntegrable
import RWRS.Support.DTStageIntegral
import RWRS.Support.DTCappedRule
import RWRS.Support.DTUnconstrained

open scoped Classical
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The per-trajectory integral splits over the stage hit events.**
For a fixed trajectory, the scenery-integral of the trap potential at
the capped rule is the sum over the first `n` stage hit events plus the
no-hit event of those `n` stages. -/
theorem integral_trapPotential_cappedRule_partition (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable (fun z : ℝ => z) ν)
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ) (ε : ℝ)
    (X : ℕ → V) (n : ℕ) :
    ∫ ξ : V → ℝ, trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
        ∂(RWRS.iidLaw V ν)
      = ∑ i ∈ Finset.range n, ∫ ξ : V → ℝ,
          (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i).indicator
            (fun ξ' => trapPotential G K ξ' (X (trapRuleCapped G r C ℓ K N ε ξ' X)))
            ξ ∂(RWRS.iidLaw V ν)
        + ∫ ξ : V → ℝ,
          ({ξ : V → ℝ | ∀ j < n, ξ ∉ trapEvent (C (X ((uncTime G r C X j).toNat))) ε}).indicator
            (fun ξ' => trapPotential G K ξ' (X (trapRuleCapped G r C ℓ K N ε ξ' X)))
            ξ ∂(RWRS.iidLaw V ν) := by
  exact integral_partition_hitEvent_add_noHit (fun j => C (X ((uncTime G r C X j).toNat))) ε n _
    (integrable_trapPotential_cappedRule ν hint r C ℓ K N ε X)

end RWRS.Support
