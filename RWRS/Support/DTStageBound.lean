import RWRS.Support.DTStageHitRew
import RWRS.Support.DTBias

open scoped Classical
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The per-stage conditional bias bound at the stage site.**  Combining the
hit-integral rewrite with the conditional bias estimate, the scenery-integral
of the trap potential at the stage site over the stage-`i` hit event is at
most `-8m` times the hit probability plus the `B₀` bias term. -/
theorem integral_hit_stage_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h0 : RWRS.extMean ν = 0) (hint : Integrable (fun z : ℝ => z) ν)
    (r : ℕ) (C : V → Finset V) (K : Finset V) (ε : ℝ)
    (X : ℕ → V) (i : ℕ) (m : ℝ)
    (hdisj : ∀ a ≤ i, ∀ b ≤ i, a ≠ b →
      Disjoint ((C (X ((uncTime G r C X a).toNat)) : Set V))
               ((C (X ((uncTime G r C X b).toNat)) : Set V)))
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q),
      q ∉ (C (X ((uncTime G r C X i).toNat)) : Set V))
    (hCK : ∀ j ≤ i, (C (X ((uncTime G r C X j).toNat)) : Set V) ⊆ (K : Set V))
    (hΘ : ENNReal.ofReal (8 * m / ε) ≤
      RWRS.thetaExit G (C (X ((uncTime G r C X i).toNat)) : Set V) (X ((uncTime G r C X i).toNat)))
    (hdeg : ∀ w : V, 0 < G.degree w) (hε : 0 < ε) (hm : 0 ≤ m) {q : ℝ} (hq : 0 < q)
    (hcompl : ∀ j < i, ENNReal.ofReal q
      ≤ RWRS.iidLaw V ν ((trapEvent (C (X ((uncTime G r C X j).toNat))) ε)ᶜ))
    (hgreen : ∀ v ∈ (stageSitesBelow (fun j => C (X ((uncTime G r C X j).toNat))) i : Finset V),
      (RWRS.green G v (X ((uncTime G r C X i).toNat))) ≠ ⊤)
    (hadm : RWRS.Support.Admissible G r
      (stageSitesBelow (fun j => C (X ((uncTime G r C X j).toNat))) i)
      (X ((uncTime G r C X i).toNat)))
    (hCF : ∀ j < i, C (X ((uncTime G r C X j).toNat))
      ⊆ stageSitesBelow (fun j => C (X ((uncTime G r C X j).toNat))) i) :
    ∫ ξ : V → ℝ, (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i).indicator
        (fun ξ' => trapPotential G K ξ' (X ((uncTime G r C X i).toNat))) ξ
        ∂(RWRS.iidLaw V ν)
      ≤ (-8 * m) * ((RWRS.iidLaw V ν
          (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal)
        + (∫ z, |z| ∂ν) * ((RWRS.iidLaw V ν
          (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i)).toReal / q) := by
  have hb := integral_conditionalBias_le ν h0 hint K
    (fun j => C (X ((uncTime G r C X j).toNat))) ε i
    (X ((uncTime G r C X i).toNat)) m r hdisj hescK hescC hCK hΘ hdeg hε hm hq hcompl
    hgreen hadm hCF
  have hiden : ∀ ξ : V → ℝ,
      trapPotential G K ξ (X ((uncTime G r C X i).toNat)) *
        (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i).indicator
          (fun _ => (1 : ℝ)) ξ
      = (hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i).indicator
        (fun ξ' => trapPotential G K ξ' (X ((uncTime G r C X i).toNat))) ξ := by
    intro ξ
    by_cases hξ : ξ ∈ hitEvent (fun j => C (X ((uncTime G r C X j).toNat))) ε i
    · simp [hξ]
    · simp [hξ]
  rw [integral_congr_ae (Filter.Eventually.of_forall hiden)] at hb
  exact hb

end RWRS.Support
