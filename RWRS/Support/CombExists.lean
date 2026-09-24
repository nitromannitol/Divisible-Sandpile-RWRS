import RWRS.Support.PipeTree
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace RWRS.Support

open Filter

theorem eventually_le_rpow_natCast {c : ℝ} (hc : 0 < c) (M : ℝ) :
    ∀ᶠ B : ℕ in atTop, M ≤ (B : ℝ) ^ c := by
  have h : Tendsto (fun B : ℕ => (B : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop M

/-- **The conditions `eq:comb-B-cond` are met for every `α ∈ (1/2,1)` by all
large `B`.** -/
theorem exists_combCond {α : ℝ} (hα1 : 1 / 2 < α) (hα2 : α < 1) :
    ∃ B : ℕ, RWRS.CombCond B α := by
  have hαpos : (0 : ℝ) < α := by linarith
  have h1 := eventually_le_rpow_natCast hαpos 4
  have h2 := eventually_le_rpow_natCast (by linarith : (0 : ℝ) < 1 - α) 4
  have h3 := eventually_le_rpow_natCast (by linarith : (0 : ℝ) < 2 * α - 1) 5
  obtain ⟨B, hB2, hb1, hb2, hb3⟩ :=
    ((eventually_ge_atTop 2).and (h1.and (h2.and h3))).exists
  refine ⟨B, hB2, hα1, hα2, hb1, ?_, ?_, ?_⟩
  · have hBR : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
    have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
    have hprod : (B : ℝ) ^ α * (B : ℝ) ^ (1 - α) = (B : ℝ) := by
      rw [← Real.rpow_add hBpos]
      norm_num
    have hpos : (0 : ℝ) < (B : ℝ) ^ α := Real.rpow_pos_of_pos hBpos α
    nlinarith [hb2, hprod, hpos, hBR]
  · have hBR : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB2
    have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
    have hneg : (B : ℝ) ^ (1 - 2 * α) = ((B : ℝ) ^ (2 * α - 1))⁻¹ := by
      rw [show (1 : ℝ) - 2 * α = -(2 * α - 1) by ring, Real.rpow_neg hBpos.le]
    rw [hneg]
    have hp : (0 : ℝ) < (B : ℝ) ^ (2 * α - 1) := Real.rpow_pos_of_pos hBpos _
    have hipos : (0 : ℝ) < ((B : ℝ) ^ (2 * α - 1))⁻¹ := inv_pos.2 hp
    have hmul : ((B : ℝ) ^ (2 * α - 1))⁻¹ * ((B : ℝ) ^ (2 * α - 1)) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hp)
    nlinarith [mul_nonneg hipos.le (by linarith : (0 : ℝ) ≤ (B : ℝ) ^ (2 * α - 1) - 5)]
  · linarith

/-- The parameters of `sec:transient-nonstab`: `max(p,1) < q < 3` and
`1/2 < α < min(1, 1/(q-1))`. -/
theorem exists_params (p : ℝ) (hp3 : p < 3) :
    ∃ q α : ℝ, p < q ∧ 1 < q ∧ q < 3 ∧ 1 / 2 < α ∧ α < 1 ∧ α < 1 / (q - 1) := by
  refine ⟨(max p 1 + 3) / 2, (1 / 2 + min 1 (1 / ((max p 1 + 3) / 2 - 1))) / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : p ≤ max p 1 := le_max_left _ _
    linarith
  · have : (1 : ℝ) ≤ max p 1 := le_max_right _ _
    linarith
  · have : max p 1 < 3 := max_lt hp3 (by norm_num)
    linarith
  all_goals (
    have h1 : (1 : ℝ) ≤ max p 1 := le_max_right _ _
    have h3 : max p 1 < 3 := max_lt hp3 (by norm_num)
    have hqm : (max p 1 + 3) / 2 - 1 > 0 := by linarith
    have hqm2 : (max p 1 + 3) / 2 - 1 < 2 := by linarith
    have hinv : 1 / 2 < 1 / ((max p 1 + 3) / 2 - 1) := by
      rw [div_lt_div_iff₀ (by norm_num) hqm]
      linarith
    have hmin : 1 / 2 < min 1 (1 / ((max p 1 + 3) / 2 - 1)) := lt_min (by norm_num) hinv
    have hmin1 : min 1 (1 / ((max p 1 + 3) / 2 - 1)) ≤ 1 := min_le_left _ _
    have hmin2 : min 1 (1 / ((max p 1 + 3) / 2 - 1)) ≤ 1 / ((max p 1 + 3) / 2 - 1) :=
      min_le_right _ _
    linarith)


end RWRS.Support
