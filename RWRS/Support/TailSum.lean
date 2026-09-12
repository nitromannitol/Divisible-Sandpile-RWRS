/-
The tail sum of a `[0,∞]`-valued variable is below its mean.

`Z ≥ ∑_t 1{t+1 ≤ Z}` pointwise, because when the `n`-th indicator is on so is
every earlier one and the partial sum is exactly `n+1`.  Integrating turns a
divergent tail sum into an infinite mean, which is how `lem:moment-sharpness`
reads its lower bounds on `P(u_∞(o) > t)`.
-/
import RWRS.Support.LocalTimeCount
import RWRS.Scenery

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

theorem sum_range_indicator_le (z : ℝ≥0∞) :
    ∀ n : ℕ, (∑ t ∈ Finset.range n, (if (t : ℝ≥0∞) + 1 ≤ z then (1 : ℝ≥0∞) else 0)) ≤ z := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : (n : ℝ≥0∞) + 1 ≤ z
      · rw [if_pos h]
        have hall : ∀ t ∈ Finset.range n,
            (if (t : ℝ≥0∞) + 1 ≤ z then (1 : ℝ≥0∞) else 0) = 1 := by
          intro t ht
          refine if_pos (le_trans ?_ h)
          have hle : (t : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
            exact_mod_cast Nat.cast_le.2 (le_of_lt (Finset.mem_range.1 ht))
          gcongr
        rw [Finset.sum_congr rfl hall, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one]
        exact h
      · rw [if_neg h, add_zero]
        exact ih

theorem tsum_indicator_le (z : ℝ≥0∞) :
    (∑' t : ℕ, (if (t : ℝ≥0∞) + 1 ≤ z then (1 : ℝ≥0∞) else 0)) ≤ z := by
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le (sum_range_indicator_le z)

/-- **The tail sum is below the mean.** -/
theorem tsum_meas_le_lintegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → ℝ≥0∞) (hZ : Measurable Z) :
    (∑' t : ℕ, P {ω | (t : ℝ≥0∞) + 1 ≤ Z ω}) ≤ ∫⁻ ω, Z ω ∂P := by
  classical
  have hset : ∀ t : ℕ, MeasurableSet {ω | (t : ℝ≥0∞) + 1 ≤ Z ω} :=
    fun t => measurableSet_le measurable_const hZ
  have hstep : ∀ t : ℕ, P {ω | (t : ℝ≥0∞) + 1 ≤ Z ω}
      = ∫⁻ ω, (if (t : ℝ≥0∞) + 1 ≤ Z ω then (1 : ℝ≥0∞) else 0) ∂P := by
    intro t
    have hfun : (fun ω => if (t : ℝ≥0∞) + 1 ≤ Z ω then (1 : ℝ≥0∞) else 0)
        = Set.indicator {ω | (t : ℝ≥0∞) + 1 ≤ Z ω} (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      by_cases h : (t : ℝ≥0∞) + 1 ≤ Z ω <;> simp [Set.indicator, h]
    rw [hfun, MeasureTheory.lintegral_indicator (hset t),
      MeasureTheory.setLIntegral_const, one_mul]
  rw [tsum_congr hstep, ← MeasureTheory.lintegral_tsum]
  · exact MeasureTheory.lintegral_mono fun ω => tsum_indicator_le (Z ω)
  · intro t
    exact (Measurable.ite (hset t) measurable_const measurable_const).aemeasurable

end RWRS.Support
