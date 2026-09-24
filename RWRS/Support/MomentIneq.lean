/-
Markov's and Chebyshev's inequalities against a Bochner integral.

The lower integral of a nonnegative measurable function bounds the measure of a
level set; `ofReal_integral_eq_lintegral_ofReal` turns that lower integral into
the Bochner integral, which is the form the background control of
`lem:moment-sharpness` uses.
-/
import RWRS.Support.Critical
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Markov's inequality.** -/
theorem meas_ge_le_abs_integral {P : Measure Ω} [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY : Measurable Y) (hint : Integrable Y P) {s : ℝ} (hs : 0 < s) :
    P {ω | s ≤ |Y ω|} ≤ ENNReal.ofReal ((∫ ω, |Y ω| ∂P) / s) := by
  have hYa : Measurable fun ω => |Y ω| := by fun_prop
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal |Y ω|) P :=
    hYa.ennreal_ofReal.aemeasurable
  have hmk := MeasureTheory.mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal s)
  have hsub : {ω | s ≤ |Y ω|} ⊆ {ω | ENNReal.ofReal s ≤ ENNReal.ofReal |Y ω|} :=
    fun ω hω => ENNReal.ofReal_le_ofReal hω
  have hmono := measure_mono (μ := P) hsub
  have hlint : ∫⁻ ω, ENNReal.ofReal |Y ω| ∂P = ENNReal.ofReal (∫ ω, |Y ω| ∂P) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.abs
      (Filter.Eventually.of_forall fun ω => abs_nonneg _)).symm
  rw [ENNReal.ofReal_div_of_pos hs,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp [ENNReal.ofReal_eq_zero]; linarith))
      (Or.inl ENNReal.ofReal_ne_top)]
  calc P {ω | s ≤ |Y ω|} * ENNReal.ofReal s
      = ENNReal.ofReal s * P {ω | s ≤ |Y ω|} := mul_comm _ _
    _ ≤ ENNReal.ofReal s * P {ω | ENNReal.ofReal s ≤ ENNReal.ofReal |Y ω|} :=
        mul_le_mul_right hmono _
    _ ≤ ∫⁻ ω, ENNReal.ofReal |Y ω| ∂P := hmk
    _ = ENNReal.ofReal (∫ ω, |Y ω| ∂P) := hlint

/-- **Chebyshev's inequality.** -/
theorem meas_ge_le_sq_integral {P : Measure Ω} [IsProbabilityMeasure P] (Y : Ω → ℝ)
    (hY : Measurable Y) (hint : Integrable (fun ω => Y ω ^ 2) P) {s : ℝ} (hs : 0 < s) :
    P {ω | s ≤ |Y ω|} ≤ ENNReal.ofReal ((∫ ω, Y ω ^ 2 ∂P) / s ^ 2) := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hYsq : Measurable fun ω => Y ω ^ 2 := by fun_prop
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (Y ω ^ 2)) P :=
    hYsq.ennreal_ofReal.aemeasurable
  have hmk := MeasureTheory.mul_meas_ge_le_lintegral₀ hmeas (ENNReal.ofReal (s ^ 2))
  have hsub : {ω | s ≤ |Y ω|}
      ⊆ {ω | ENNReal.ofReal (s ^ 2) ≤ ENNReal.ofReal (Y ω ^ 2)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    refine ENNReal.ofReal_le_ofReal ?_
    have habs : |Y ω| ^ 2 = Y ω ^ 2 := sq_abs (Y ω)
    have hmono : s ^ 2 ≤ |Y ω| ^ 2 := by nlinarith [abs_nonneg (Y ω), hs.le, hω]
    linarith [habs, hmono]
  have hmono := measure_mono (μ := P) hsub
  have hlint : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P = ENNReal.ofReal (∫ ω, Y ω ^ 2 ∂P) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)).symm
  rw [ENNReal.ofReal_div_of_pos hs2,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp [ENNReal.ofReal_eq_zero]; linarith))
      (Or.inl ENNReal.ofReal_ne_top)]
  calc P {ω | s ≤ |Y ω|} * ENNReal.ofReal (s ^ 2)
      = ENNReal.ofReal (s ^ 2) * P {ω | s ≤ |Y ω|} := mul_comm _ _
    _ ≤ ENNReal.ofReal (s ^ 2) * P {ω | ENNReal.ofReal (s ^ 2) ≤ ENNReal.ofReal (Y ω ^ 2)} :=
        mul_le_mul_right hmono _
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂P := hmk
    _ = ENNReal.ofReal (∫ ω, Y ω ^ 2 ∂P) := hlint

end RWRS.Support
