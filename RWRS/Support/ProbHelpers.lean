import RWRS.Support.CombOdometer
import RWRS.Support.Measurability
import RWRS.Support.WeakLaw

namespace RWRS.Support

open MeasureTheory Filter
open scoped ENNReal

/-- A set carrying almost every point has probability one. -/
theorem prob_eq_one_of_ae_mem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s : Set Ω} (h : ∀ᵐ x ∂P, x ∈ s) : P s = 1 := by
  have hc : P sᶜ = 0 := h
  refine le_antisymm prob_le_one ?_
  calc (1 : ℝ≥0∞) = P Set.univ := (measure_univ).symm
    _ = P (s ∪ sᶜ) := by rw [Set.union_compl_self]
    _ ≤ P s + P sᶜ := measure_union_le _ _
    _ = P s := by rw [hc, add_zero]

/-- Every coordinate of an i.i.d. field almost surely lies where the marginal
does. -/
theorem ae_all_mem {ι : Type*} [Countable ι] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {s : Set ℝ} (hs : MeasurableSet s) (h : ∀ᵐ z ∂ν, z ∈ s) :
    ∀ᵐ ξ ∂(RWRS.iidLaw ι ν), ∀ v : ι, ξ v ∈ s := by
  rw [MeasureTheory.ae_all_iff]
  intro v
  rw [← map_eval_iidLaw (V := ι) ν v] at h
  exact (ae_map_iff (measurable_pi_apply v).aemeasurable
    (show MeasurableSet {z : ℝ | z ∈ s} from hs)).1 h

end RWRS.Support
