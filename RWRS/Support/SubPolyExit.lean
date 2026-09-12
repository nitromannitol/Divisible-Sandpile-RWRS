/-
The radius of Step 3 of `prop:poly-growth`.

`rwrs.tex:1289` takes `R_N = C_0N^{1/d_w}(\log N)^{(d_w-1)/d_w}`, the critical
scale, and chooses `C_0` large enough that hypothesis `H3` makes the
displacement failure `O(N^{-r})` for the single exponent `r` the proof needs.
Taking the radius slightly ABOVE the critical scale, `R_N = ⌈N^{1/d_w+s}⌉` for a
small `s>0`, replaces that polynomial by a stretched exponential
`exp(-c_{\mathrm{disp}}N^{sd_w/(d_w-1)})`, which is summable against every
polynomial at once, and removes the logarithm from the level the trajectory
meets: `R_N^β ≤ 2^βN^{β(1/d_w+s)}`.  The extra `βs` in the exponent is absorbed
by the strict inequality `β/d_w < d_s/2-δ`.
-/
import RWRS.Support.SubPolyStep

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The radius of Step 3: just above the critical scale `N^{1/d_w}`. -/
noncomputable def polyR (d_w s : ℝ) (N : ℕ) : ℕ := ⌈(N : ℝ) ^ (1 / d_w + s)⌉₊

theorem one_le_rpow_natCast {e : ℝ} (he : 0 ≤ e) {N : ℕ} (hN : 1 ≤ N) :
    (1:ℝ) ≤ (N : ℝ) ^ e := by
  have hN1 : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc (1:ℝ) = (1:ℝ) ^ e := (Real.one_rpow e).symm
    _ ≤ (N : ℝ) ^ e := Real.rpow_le_rpow (by norm_num) hN1 he

theorem one_le_polyR {d_w s : ℝ} (hdw : 2 ≤ d_w) (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ polyR d_w s N := by
  have he : (0:ℝ) ≤ 1 / d_w + s := by positivity
  have h1 : (1:ℝ) ≤ (N : ℝ) ^ (1 / d_w + s) := one_le_rpow_natCast he hN
  exact Nat.ceil_pos.2 (lt_of_lt_of_le zero_lt_one h1)

theorem polyR_le {d_w s : ℝ} (hdw : 2 ≤ d_w) (hs : 0 < s) {N : ℕ} (hN : 1 ≤ N) :
    (polyR d_w s N : ℝ) ≤ 2 * (N : ℝ) ^ (1 / d_w + s) := by
  have he : (0:ℝ) ≤ 1 / d_w + s := by positivity
  have h1 : (1:ℝ) ≤ (N : ℝ) ^ (1 / d_w + s) := one_le_rpow_natCast he hN
  have h2 : (polyR d_w s N : ℝ) < (N : ℝ) ^ (1 / d_w + s) + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  linarith

/-- Exit estimates at one origin, at every scale strictly above the walk
scale. The constants may depend on the origin and the excess exponent. -/
def PolynomialExitBoundAt [MeasurableSpace V] (G : SimpleGraph V) [G.LocallyFinite]
    (o : V) (d_w : ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
    RWRS.walkLaw G o {X : ℕ → V |
        RWRS.exitTime (RWRS.closedBall G o (polyR d_w s N)) X ≤ (N : ℕ∞)} ≤
      ENNReal.ofReal (C * Real.exp (-(c * (N : ℝ) ^ (s * d_w / (d_w - 1)))))

/-- **The displacement failure at the radius of Step 3 is a stretched
exponential.** -/
theorem walkLaw_exit_polyR_le [MeasurableSpace V] {d_w C_disp c_disp s : ℝ}
    (hH3 : RWRS.WalkDimensionBound G d_w C_disp c_disp) (hdw : 2 ≤ d_w) (hC : 0 ≤ C_disp)
    (hc : 0 < c_disp) (hs : 0 < s) (o : V) {N : ℕ} (hN : 1 ≤ N) :
    RWRS.walkLaw G o {X : ℕ → V |
        RWRS.exitTime (RWRS.closedBall G o (polyR d_w s N)) X ≤ (N : ℕ∞)}
      ≤ ENNReal.ofReal (C_disp * Real.exp (-(c_disp * (N : ℝ) ^ (s * d_w / (d_w - 1))))) := by
  have hdw0 : (0:ℝ) < d_w := by linarith
  have hdw1 : (0:ℝ) < d_w - 1 := by linarith
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hR1 : 1 ≤ polyR d_w s N := one_le_polyR hdw hs hN
  set θd : ℝ := s * d_w / (d_w - 1) with hθd
  have hθd0 : (0:ℝ) < θd := by rw [hθd]; positivity
  have ha1 : (1:ℝ) ≤ (N : ℝ) ^ θd := one_le_rpow_natCast hθd0.le hN
  have hbase : ((N : ℝ) * ((N : ℝ) ^ θd) ^ (d_w - 1)) ^ (1 / d_w)
      ≤ (polyR d_w s N : ℝ) := by
    have he1 : ((N : ℝ) ^ θd) ^ (d_w - 1) = (N : ℝ) ^ (s * d_w) := by
      rw [← Real.rpow_mul hNpos.le, hθd]
      congr 1
      field_simp
    have he2 : (N : ℝ) * (N : ℝ) ^ (s * d_w) = (N : ℝ) ^ (1 + s * d_w) := by
      rw [Real.rpow_add hNpos, Real.rpow_one]
    have he3 : ((N : ℝ) ^ (1 + s * d_w)) ^ (1 / d_w) = (N : ℝ) ^ (1 / d_w + s) := by
      rw [← Real.rpow_mul hNpos.le]
      congr 1
      field_simp
    rw [he1, he2, he3]
    exact Nat.le_ceil _
  have hexp := exit_exponent_bound (d_w := d_w) (N := (N : ℝ))
    (R := (polyR d_w s N : ℝ)) (a := (N : ℝ) ^ θd - 1) hdw (by linarith) hNpos
    (by simpa using hbase)
  refine le_trans (hH3 o N (polyR d_w s N) hN hR1) (ENNReal.ofReal_le_ofReal ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
  have hstep : (N : ℝ) ^ θd
      ≤ (((polyR d_w s N : ℝ)) ^ d_w / (N : ℝ)) ^ (1 / (d_w - 1)) := by
    simpa using hexp
  nlinarith [hstep, hc]

/-- Uniform walk-dimension control supplies polynomial-radius control at each
origin. -/
theorem polynomialExitBoundAt_of_walkDimensionBound [MeasurableSpace V]
    {d_w C_disp c_disp : ℝ} (hH3 : RWRS.WalkDimensionBound G d_w C_disp c_disp)
    (hdw : 2 ≤ d_w) (hC : 0 < C_disp) (hc : 0 < c_disp) (o : V) :
    PolynomialExitBoundAt G o d_w := by
  intro s hs
  exact ⟨C_disp, c_disp, hC, hc, fun _ hN =>
    walkLaw_exit_polyR_le hH3 hdw hC.le hc hs o hN⟩

end RWRS.Support
