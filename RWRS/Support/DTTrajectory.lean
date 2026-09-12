/-
The per-trajectory conditional estimate of Step 1.

For a fixed trajectory that leaves `K` before the horizon, the scenery integral
of the trap potential at the capped rule splits over the hit events of the
usable stages; each of them contributes at most `-8m` from its own block and the
bias `B₀` from the earlier ones, and the failure case contributes nothing.
-/
import RWRS.Support.DTStageBound
import RWRS.Support.DTStagePartition
import RWRS.Support.DTStageHitRew
import RWRS.Support.DTNoHitZero
import RWRS.Support.DTStageSites
import RWRS.Support.DTWalkBlocks

open scoped Classical
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The per-trajectory conditional estimate.**  For a fixed trajectory that
leaves `K` before the horizon, the scenery integral of the trap potential at the
capped rule is at most the sum of the per-stage bias bounds over the usable
stages. -/
theorem integral_trapPotential_cappedRule_le (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (h0 : RWRS.extMean ν = 0)
    (hint : Integrable (fun z : ℝ => z) ν)
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (X : ℕ → V) (m : ℝ)
    (hCball : ∀ y : V, ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r)
    (hCself : ∀ y : V, y ∈ C y)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hescC : ∀ y x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C y : Set V))
    (hΘ : ∀ y : V, ENNReal.ofReal (8 * m / ε) ≤ RWRS.thetaExit G (C y : Set V) y)
    (hdeg : ∀ w : V, 0 < G.degree w) (hε : 0 < ε) (hm : 0 ≤ m) {q : ℝ} (hq : 0 < q)
    (hcompl : ∀ y : V, ENNReal.ofReal q
      ≤ RWRS.iidLaw V ν ((trapEvent (C y) ε)ᶜ))
    (hexit : ∃ n, n < N ∧ X n ∉ K) :
    ∫ ξ : V → ℝ, trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
        ∂(RWRS.iidLaw V ν)
      ≤ ∑ i ∈ Finset.range (stageCnt G r C ℓ K N X),
            ((-8 * m) * ((RWRS.iidLaw V ν
              (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal)
              + (∫ z, |z| ∂ν) * ((RWRS.iidLaw V ν
                (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal / q)) := by
  rw [integral_trapPotential_cappedRule_partition ν hint r C ℓ K N ε X
    (stageCnt G r C ℓ K N X)]
  have hzero : ∫ ξ : V → ℝ,
      ({ξ : V → ℝ | ∀ j < stageCnt G r C ℓ K N X,
        ξ ∉ trapEvent (C (X ((uncTime G r C X j).toNat))) ε}).indicator
        (fun ξ' => trapPotential G K ξ' (X (trapRuleCapped G r C ℓ K N ε ξ' X))) ξ
        ∂(RWRS.iidLaw V ν) = 0 := by
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun ξ => ?_)
    by_cases hmem : ξ ∈ {ξ : V → ℝ | ∀ j < stageCnt G r C ℓ K N X,
        ξ ∉ trapEvent (C (X ((uncTime G r C X j).toNat))) ε}
    · rw [Set.indicator_of_mem hmem]
      exact trapPotential_trapRuleCapped_eq_zero_of_noHit r C ℓ K hN ε X hescK hexit ξ hmem
    · exact Set.indicator_of_notMem hmem _
  rw [hzero, add_zero]
  refine Finset.sum_le_sum fun i hi => ?_
  have hilt : i < stageCnt G r C ℓ K N X := Finset.mem_range.mp hi
  have hok : StageOK G r C K N X i := (stageOK_of_lt_stageCnt r C ℓ K N X hilt).2
  have hfin : uncTime G r C X i ≠ ⊤ := ne_top_of_lt hok.1
  have hadm : RWRS.Support.Admissible G r
      (stageSitesBelow (fun j => C (X ((uncTime G r C X j).toNat))) i)
      (X ((uncTime G r C X i).toNat)) :=
    admissible_stageSitesBelow G r C X i hfin
  rw [integral_hit_rule_eq_stage ν r C ℓ K hN ε X hilt]
  refine integral_hit_stage_le ν h0 hint r C K ε X i m
    (disjoint_walkBlocks r C K hCball hCself X ℓ hilt)
    hescK (hescC (X ((uncTime G r C X i).toNat)))
    (fun j hj => by
      exact_mod_cast Finset.coe_subset.mpr
        (Finset.Subset.trans (uncBlock_subset_used_of_le G r C X hj) hok.2.2))
    (hΘ (X ((uncTime G r C X i).toNat))) hdeg hε hm hq
    (fun j _ => hcompl (X ((uncTime G r C X j).toNat)))
    (green_ne_top_of_admissible r _ _ hadm) hadm
    (fun j hj => walkBlock_subset_stageSitesBelow r C X i j hj)

end RWRS.Support
