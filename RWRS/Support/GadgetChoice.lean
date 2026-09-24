import RWRS.Support.CombExists
import RWRS.Support.GadgetBall
import RWRS.Support.CombArith

namespace RWRS.Support

open Filter

variable {B : ℕ} {α : ℝ}

theorem le_gadgetRadius (hc : CombCond B α) (M : ℕ) :
    M ≤ gadgetRadius (combLen B α) M := by
  have h : ∀ j ∈ Finset.Icc 1 M, 1 ≤ combLen B α j := fun j _ => one_le_combLen hc j
  calc M = ∑ _j ∈ Finset.Icc 1 M, 1 := by simp
    _ ≤ ∑ j ∈ Finset.Icc 1 M, combLen B α j := Finset.sum_le_sum h
    _ = gadgetRadius (combLen B α) M := rfl

theorem tendsto_gadgetRadius (hc : CombCond B α) :
    Tendsto (fun M : ℕ => (gadgetRadius (combLen B α) M : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun M => ?_) tendsto_natCast_atTop_atTop
  exact_mod_cast le_gadgetRadius hc M

theorem tendsto_gadgetRadius_rpow (hc : CombCond B α) {c : ℝ} (hcpos : 0 < c) :
    Tendsto (fun M : ℕ => (gadgetRadius (combLen B α) M : ℝ) ^ c) atTop atTop :=
  (tendsto_rpow_atTop hcpos).comp (tendsto_gadgetRadius hc)

/-- **The three conditions `eq:rec-cond-sep`, `eq:rec-cond-vol` and
`eq:rec-cond-div` are met by all large depths.**  Every one of them asks a
positive power of `R_m` to dominate a quantity already fixed, and
`ρ(d_f+1) < δ` is what makes the last one a genuine domination. -/
theorem exists_next_gadget (hc : CombCond B α) {d_f ρ δ c_loc : ℝ}
    (hdf : 0 < d_f) (hρ : 0 < ρ) (hcloc : 0 < c_loc)
    (hρδ : ρ * (d_f + 1) < δ) (M0 : ℕ) (S : ℝ) (k : ℕ) :
    ∃ M : ℕ, M0 < M ∧
      ⌈(gadgetRadius (combLen B α) M0 : ℝ) ^ ρ⌉₊ + gadgetRadius (combLen B α) M0
        < ⌈(gadgetRadius (combLen B α) M : ℝ) ^ ρ⌉₊ ∧
      S ≤ (⌈(gadgetRadius (combLen B α) M : ℝ) ^ ρ⌉₊ : ℝ) ^ d_f ∧
      ((⌈(gadgetRadius (combLen B α) M : ℝ) ^ ρ⌉₊ : ℝ) + 1) ^ (d_f + 1) * (k : ℝ)
        ≤ c_loc * (gadgetRadius (combLen B α) M : ℝ) ^ δ := by
  set R : ℕ → ℝ := fun M => (gadgetRadius (combLen B α) M : ℝ) with hRdef
  have hRtend : Tendsto R atTop atTop := tendsto_gadgetRadius hc
  have hgap : 0 < δ - ρ * (d_f + 1) := by linarith
  -- the four eventual conditions
  have e0 : ∀ᶠ M : ℕ in atTop, M0 < M := eventually_gt_atTop M0
  have e1 : ∀ᶠ M : ℕ in atTop, (1 : ℝ) ≤ R M := hRtend.eventually_ge_atTop 1
  have e2 : ∀ᶠ M : ℕ in atTop,
      ((⌈(R M0 : ℝ) ^ ρ⌉₊ + gadgetRadius (combLen B α) M0 : ℕ) : ℝ) < R M ^ ρ :=
    (tendsto_gadgetRadius_rpow hc hρ).eventually_gt_atTop _
  have e3 : ∀ᶠ M : ℕ in atTop, S ≤ R M ^ (ρ * d_f) :=
    (tendsto_gadgetRadius_rpow hc (by positivity)).eventually_ge_atTop S
  have e4 : ∀ᶠ M : ℕ in atTop,
      (3 : ℝ) ^ (d_f + 1) * (k : ℝ) / c_loc ≤ R M ^ (δ - ρ * (d_f + 1)) :=
    (tendsto_gadgetRadius_rpow hc hgap).eventually_ge_atTop _
  obtain ⟨M, hM0, hM1, hM2, hM3, hM4⟩ := (e0.and (e1.and (e2.and (e3.and e4)))).exists
  have hRpos : (0 : ℝ) < R M := by linarith
  have hRρ : (1 : ℝ) ≤ R M ^ ρ := Real.one_le_rpow hM1 hρ.le
  have hceil_le : (⌈R M ^ ρ⌉₊ : ℝ) ≤ R M ^ ρ + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hle_ceil : R M ^ ρ ≤ (⌈R M ^ ρ⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨M, hM0, ?_, ?_, ?_⟩
  · have : ((⌈(R M0 : ℝ) ^ ρ⌉₊ + gadgetRadius (combLen B α) M0 : ℕ) : ℝ)
        < (⌈R M ^ ρ⌉₊ : ℝ) := lt_of_lt_of_le hM2 hle_ceil
    exact_mod_cast this
  · refine le_trans hM3 ?_
    rw [Real.rpow_mul hRpos.le]
    exact Real.rpow_le_rpow (by positivity) hle_ceil hdf.le
  · have hbase : (⌈R M ^ ρ⌉₊ : ℝ) + 1 ≤ 3 * R M ^ ρ := by linarith
    have hstep : ((⌈R M ^ ρ⌉₊ : ℝ) + 1) ^ (d_f + 1) ≤ (3 * R M ^ ρ) ^ (d_f + 1) :=
      Real.rpow_le_rpow (by positivity) hbase (by linarith)
    have hsplit : (3 * R M ^ ρ) ^ (d_f + 1)
        = (3 : ℝ) ^ (d_f + 1) * R M ^ (ρ * (d_f + 1)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hRpos.le]
    have hδ : R M ^ δ = R M ^ (ρ * (d_f + 1)) * R M ^ (δ - ρ * (d_f + 1)) := by
      rw [← Real.rpow_add hRpos]
      ring_nf
    have hpowpos : (0 : ℝ) < R M ^ (ρ * (d_f + 1)) := Real.rpow_pos_of_pos hRpos _
    have hkey : (3 : ℝ) ^ (d_f + 1) * (k : ℝ) ≤ c_loc * R M ^ (δ - ρ * (d_f + 1)) := by
      rw [div_le_iff₀ hcloc] at hM4
      linarith
    calc ((⌈R M ^ ρ⌉₊ : ℝ) + 1) ^ (d_f + 1) * (k : ℝ)
        ≤ (3 * R M ^ ρ) ^ (d_f + 1) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hstep (Nat.cast_nonneg k)
      _ = R M ^ (ρ * (d_f + 1)) * ((3 : ℝ) ^ (d_f + 1) * (k : ℝ)) := by rw [hsplit]; ring
      _ ≤ R M ^ (ρ * (d_f + 1)) * (c_loc * R M ^ (δ - ρ * (d_f + 1))) :=
          mul_le_mul_of_nonneg_left hkey hpowpos.le
      _ = c_loc * R M ^ δ := by rw [hδ]; ring

end RWRS.Support
