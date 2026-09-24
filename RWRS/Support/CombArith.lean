/-
The arithmetic behind the comb estimates of `prop:comb-estimates`.

Under `eq:comb-B-cond` the pipe lengths satisfy `2 ≤ L_j` for `j ≥ 1` (because
`B^α ≥ 4`), `L_{j+1} ≤ (B-1) L_j` (because `2B^α ≤ B-1`), and the ratio
`2B/(B^α)^2 = 2B^{1-2α}` is less than one, which is what makes the level sums of
part (c) a convergent geometric series.  The growth constant is
`λ = B^{2α-1}/4 = (B^α)^2/(4B)`.
-/
import RWRS.Support.Gadget

namespace RWRS.Support

variable {B : ℕ} {α : ℝ}

/-- Every pipe of positive level has at least two edges. -/
theorem two_le_combLen (hc : CombCond B α) {j : ℕ} (hj : 1 ≤ j) : 2 ≤ combLen B α j := by
  have h1 := combLen_ge hc hj
  have h2 := base_pow_ge hc hj
  have : (2 : ℝ) ≤ (combLen B α j : ℝ) := by linarith
  exact_mod_cast this

theorem four_le_combLen (hc : CombCond B α) {j : ℕ} (hj : 1 ≤ j) : 4 ≤ combLen B α j := by
  rw [combLen]
  refine Nat.le_floor ?_
  push_cast
  rw [← base_pow hc j]
  exact base_pow_ge hc hj

theorem one_le_combLen (hc : CombCond B α) (j : ℕ) : 1 ≤ combLen B α j := combLen_pos' hc j

theorem one_le_combLen_real (hc : CombCond B α) (j : ℕ) : (1 : ℝ) ≤ (combLen B α j : ℝ) := by
  exact_mod_cast one_le_combLen hc j

/-- `L_{j+1} ≤ (B-1) L_j`, the inequality that makes the parallel combination of
the `B-1` side stubs cheaper than one more pipe. -/
theorem combLen_succ_le_mul (hc : CombCond B α) {j : ℕ} (hj : 1 ≤ j) :
    (combLen B α (j + 1) : ℝ) ≤ ((B : ℝ) - 1) * (combLen B α j : ℝ) := by
  have hup := combLen_le hc (j + 1)
  have hlow := combLen_ge hc hj
  have hbpos := base_pos hc
  have hBc := hc.2.2.2.2.1
  have hLj : (0 : ℝ) ≤ (combLen B α j : ℝ) := Nat.cast_nonneg _
  have hstep : ((B : ℝ) ^ α) ^ (j + 1) ≤ 2 * (B : ℝ) ^ α * (combLen B α j : ℝ) := by
    rw [pow_succ]
    nlinarith
  nlinarith

theorem two_combLen_one_le (hc : CombCond B α) :
    2 * (combLen B α 1 : ℝ) ≤ (B : ℝ) - 1 := by
  have hup := combLen_le hc 1
  have hBc := hc.2.2.2.2.1
  rw [pow_one] at hup
  linarith

/-! ### The geometric ratio -/

theorem combRatio_eq (hc : CombCond B α) :
    2 * (B : ℝ) / ((B : ℝ) ^ α) ^ 2 = 2 * (B : ℝ) ^ (1 - 2 * α) := by
  have hBpos := cast_B_pos hc
  have h1 : ((B : ℝ) ^ α) ^ 2 = (B : ℝ) ^ (2 * α) := by
    rw [← Real.rpow_natCast ((B : ℝ) ^ α) 2, ← Real.rpow_mul hBpos.le]
    ring_nf
  have h2 : (B : ℝ) ^ (1 - 2 * α) = (B : ℝ) / (B : ℝ) ^ (2 * α) := by
    rw [Real.rpow_sub hBpos, Real.rpow_one]
  rw [h1, h2]
  have : (B : ℝ) ^ (2 * α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hBpos _)
  field_simp

theorem combRatio_pos (hc : CombCond B α) : 0 < 2 * (B : ℝ) / ((B : ℝ) ^ α) ^ 2 := by
  have hBpos := cast_B_pos hc
  have hbpos := base_pos hc
  positivity

theorem combRatio_lt_one (hc : CombCond B α) : 2 * (B : ℝ) / ((B : ℝ) ^ α) ^ 2 < 1 := by
  rw [combRatio_eq hc]
  exact hc.2.2.2.2.2.1

/-- A finite geometric sum is bounded by its infinite value. -/
theorem sum_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ k ∈ Finset.range m, r ^ k ≤ 1 / (1 - r) := by
  have hne : r ≠ 1 := ne_of_lt hr1
  rw [geom_sum_eq hne]
  have hpos : 0 < 1 - r := by linarith
  have hne' : r - 1 ≠ 0 := by intro h; apply hne; linarith
  have hrn : (0 : ℝ) ≤ r ^ m := pow_nonneg hr0 m
  have key : (r ^ m - 1) / (r - 1) = (1 - r ^ m) / (1 - r) := by
    field_simp
    ring
  rw [key]
  gcongr
  nlinarith

/-! ### The level ratio of the squared pipe lengths -/

theorem combLen_sq_ratio (hc : CombCond B α) {j m : ℕ} (hm : 1 ≤ m) (hjm : j ≤ m) :
    (combLen B α j : ℝ) ^ 2 * (((B : ℝ) ^ α) ^ 2) ^ (m - j)
      ≤ 4 * (combLen B α m : ℝ) ^ 2 := by
  have hup := combLen_le hc j
  have hlow := combLen_ge hc hm
  have hbpos := base_pos hc
  have hLj : (0 : ℝ) ≤ (combLen B α j : ℝ) := Nat.cast_nonneg _
  have hpow : (0 : ℝ) < ((B : ℝ) ^ α) ^ j := pow_pos hbpos j
  have hkey : (combLen B α j : ℝ) ^ 2 * (((B : ℝ) ^ α) ^ 2) ^ (m - j)
      ≤ (((B : ℝ) ^ α) ^ j) ^ 2 * (((B : ℝ) ^ α) ^ 2) ^ (m - j) := by
    have hnn : (0 : ℝ) ≤ (((B : ℝ) ^ α) ^ 2) ^ (m - j) := by positivity
    have hsq : (combLen B α j : ℝ) ^ 2 ≤ (((B : ℝ) ^ α) ^ j) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq hnn
  have hcollapse : (((B : ℝ) ^ α) ^ j) ^ 2 * (((B : ℝ) ^ α) ^ 2) ^ (m - j)
      = (((B : ℝ) ^ α) ^ m) ^ 2 := by
    rw [← pow_mul ((B : ℝ) ^ α) j 2, ← pow_mul ((B : ℝ) ^ α) 2 (m - j), ← pow_add,
      ← pow_mul ((B : ℝ) ^ α) m 2]
    congr 1
    omega
  rw [hcollapse] at hkey
  nlinarith [pow_pos hbpos m]

/-! ### The growth constant -/

theorem combLambda_eq (hc : CombCond B α) :
    combLambda B α = ((B : ℝ) ^ α) ^ 2 / (4 * (B : ℝ)) := by
  have hBpos := cast_B_pos hc
  have h1 : ((B : ℝ) ^ α) ^ 2 = (B : ℝ) ^ (2 * α) := by
    rw [← Real.rpow_natCast ((B : ℝ) ^ α) 2, ← Real.rpow_mul hBpos.le]
    ring_nf
  have h2 : (B : ℝ) ^ (2 * α - 1) = (B : ℝ) ^ (2 * α) / (B : ℝ) := by
    rw [Real.rpow_sub hBpos, Real.rpow_one]
  rw [combLambda, h1, h2]
  field_simp

end RWRS.Support
