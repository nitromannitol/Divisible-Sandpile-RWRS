/-
The hit events of the stages and the no-hit event carry the whole scenery mass,
so the total hit probability is one minus the failure probability.
-/
import RWRS.Support.DTStageIntegral

open scoped Classical
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} [DecidableEq V] [MeasurableSpace V]

omit [DecidableEq V] [MeasurableSpace V] in
/-- **The hit events and the no-hit event have total mass one.** -/
theorem sum_measure_hitEvent_add_noHit (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ]
    (C : ℕ → Finset V) (ε : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (μ (hitEvent C ε i)).toReal)
      + (μ {ξ : V → ℝ | ∀ j < n, ξ ∉ trapEvent (C j) ε}).toReal = 1 := by
  have hind : ∀ s : Set (V → ℝ), MeasurableSet s →
      ∫ ξ, s.indicator (fun _ => (1 : ℝ)) ξ ∂μ = (μ s).toReal := by
    intro s hs
    rw [MeasureTheory.integral_indicator_const (1 : ℝ) hs]
    simp only [smul_eq_mul, mul_one]
    rfl
  have h := integral_partition_hitEvent_add_noHit C ε n (μ := μ) (fun _ => (1 : ℝ))
    (integrable_const 1)
  have hu : ∫ _ξ : V → ℝ, (1 : ℝ) ∂μ = 1 := by
    rw [integral_const]
    simp
  rw [hu, hind _ (measurableSet_noHit C ε n),
    Finset.sum_congr rfl (fun i _ => hind _ (measurableSet_hitEvent C ε i))] at h
  linarith

end RWRS.Support
