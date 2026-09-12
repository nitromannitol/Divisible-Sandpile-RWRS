/-
The displacement exponent of Step 3 of `prop:poly-growth`.

`rwrs.tex:1289` applies hypothesis `H3` at time `N` and radius `R_N`, where the
exponent of the bound is `(R_N^{d_w}/N)^{1/(d_w-1)}`.  What the step needs of
the radius is exactly that this exponent be at least a prescribed quantity, and
that is what solving `R \geq (N(a+1)^{d_w-1})^{1/d_w}` for the exponent gives.
The radius itself is chosen in `SubPolyExit`.
-/
import RWRS.Support.SubPolyGood

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The displacement exponent at a radius large enough.** -/
theorem exit_exponent_bound {d_w N R a : ℝ} (hdw : 2 ≤ d_w) (ha : 0 ≤ a) (hN : 0 < N)
    (hR : (N * (a + 1) ^ (d_w - 1)) ^ (1 / d_w) ≤ R) :
    a + 1 ≤ (R ^ d_w / N) ^ (1 / (d_w - 1)) := by
  have hdw0 : (0:ℝ) < d_w := by linarith
  have hdw1 : (0:ℝ) < d_w - 1 := by linarith
  have ha1 : (0:ℝ) < a + 1 := by linarith
  have hApos : (0:ℝ) < N * (a + 1) ^ (d_w - 1) := by
    have hp : (0:ℝ) < (a + 1) ^ (d_w - 1) := Real.rpow_pos_of_pos ha1 _
    positivity
  have hstep : N * (a + 1) ^ (d_w - 1) ≤ R ^ d_w := by
    have h1 : ((N * (a + 1) ^ (d_w - 1)) ^ (1 / d_w)) ^ d_w ≤ R ^ d_w :=
      Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hApos _)) hR hdw0.le
    rwa [← Real.rpow_mul hApos.le, one_div, inv_mul_cancel₀ (ne_of_gt hdw0),
      Real.rpow_one] at h1
  have hdiv : (a + 1) ^ (d_w - 1) ≤ R ^ d_w / N := by
    rw [le_div_iff₀ hN]
    linarith [hstep]
  have hmono : ((a + 1) ^ (d_w - 1)) ^ (1 / (d_w - 1)) ≤ (R ^ d_w / N) ^ (1 / (d_w - 1)) :=
    Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos ha1 _)) hdiv (by positivity)
  rwa [← Real.rpow_mul ha1.le, mul_one_div, div_self (ne_of_gt hdw1), Real.rpow_one] at hmono

end RWRS.Support
