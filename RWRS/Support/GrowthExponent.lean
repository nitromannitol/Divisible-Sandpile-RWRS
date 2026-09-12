/-
The growth exponent as a limsup.

`thm:recurrent-nonstab` asserts that the limsup of `log|B(o,r)| / log r` is
exactly `d_f`.  What that needs of the graph is only the two bounds the volume
proposition supplies: a power upper bound at every radius, and a power lower
bound along a subsequence.  The upper bound gives `log|B| / log r ≤
log C / log r + d_f`, whose limit is `d_f`; the lower bound gives
`log c / log r_k + d_f ≤ log|B(o,r_k)| / log r_k`, whose left side tends to
`d_f`, so the limsup is at least `d_f - ε` for every `ε`.
-/
import RWRS.Support.RayVolume

namespace RWRS.Support

open Filter

theorem tendsto_log_natCast : Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem tendsto_const_div_log (a : ℝ) :
    Tendsto (fun R : ℕ => a / Real.log R) atTop (nhds 0) := by
  have h := tendsto_log_natCast.inv_tendsto_atTop
  have h2 : Tendsto (fun R : ℕ => a * (Real.log R)⁻¹) atTop (nhds (a * 0)) :=
    h.const_mul a
  rw [mul_zero] at h2
  exact h2.congr fun R => by rw [div_eq_mul_inv]

/-- **The growth exponent read off a power upper bound and a power lower bound
along a subsequence.** -/
theorem limsup_log_card (C c d : ℝ) (hC : 0 < C) (hc : 0 < c)
    (f : ℕ → ℕ) (hf1 : ∀ R : ℕ, 1 ≤ f R)
    (hup : ∀ R : ℕ, 1 ≤ R → (f R : ℝ) ≤ C * (R : ℝ) ^ d)
    (r : ℕ → ℕ) (hr : StrictMono r)
    (hlow : ∀ k, c * ((r k : ℝ)) ^ d ≤ (f (r k) : ℝ)) :
    limsup (fun R : ℕ => Real.log (f R) / Real.log R) atTop = d := by
  set g : ℕ → ℝ := fun R => Real.log (f R) / Real.log R with hg
  have hlogpos : ∀ R : ℕ, 2 ≤ R → 0 < Real.log R := by
    intro R hR
    refine Real.log_pos ?_
    exact_mod_cast hR
  -- the pointwise upper bound
  have hub : ∀ R : ℕ, 2 ≤ R → g R ≤ Real.log C / Real.log R + d := by
    intro R hR
    have hlR := hlogpos R hR
    have hRpos : (0 : ℝ) < (R : ℝ) := by positivity
    have hfpos : (0 : ℝ) < (f R : ℝ) := by exact_mod_cast hf1 R
    have hle : Real.log (f R) ≤ Real.log C + d * Real.log R := by
      have h1 : Real.log ((f R : ℝ)) ≤ Real.log (C * (R : ℝ) ^ d) :=
        Real.log_le_log hfpos (hup R (by omega))
      rwa [Real.log_mul (ne_of_gt hC) (by positivity), Real.log_rpow hRpos] at h1
    rw [hg, div_le_iff₀ hlR]
    have hcong : (Real.log C / Real.log R + d) * Real.log R
        = Real.log C + d * Real.log R := by
      field_simp
    rw [hcong]
    exact hle
  -- the pointwise lower bound along the subsequence
  have hlb : ∀ k : ℕ, 2 ≤ r k → Real.log c / Real.log (r k) + d ≤ g (r k) := by
    intro k hR
    have hlR := hlogpos (r k) hR
    have hRpos : (0 : ℝ) < ((r k : ℕ) : ℝ) := by positivity
    have hle : Real.log c + d * Real.log (r k) ≤ Real.log (f (r k)) := by
      have h1 : Real.log (c * ((r k : ℕ) : ℝ) ^ d) ≤ Real.log ((f (r k) : ℝ)) :=
        Real.log_le_log (by positivity) (hlow k)
      rwa [Real.log_mul (ne_of_gt hc) (by positivity), Real.log_rpow hRpos] at h1
    rw [hg, le_div_iff₀ hlR]
    have hcong : (Real.log c / Real.log (r k) + d) * Real.log (r k)
        = Real.log c + d * Real.log (r k) := by
      field_simp
    rw [hcong]
    exact hle
  have hCtend : Tendsto (fun R : ℕ => Real.log C / Real.log R + d) atTop (nhds d) := by
    have := (tendsto_const_div_log (Real.log C)).add_const d
    simpa using this
  have hbdd : IsBoundedUnder (· ≤ ·) atTop g := by
    refine ⟨|Real.log C| / Real.log 2 + d, ?_⟩
    rw [eventually_map]
    filter_upwards [eventually_ge_atTop 2] with R hR
    refine le_trans (hub R hR) ?_
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlR : Real.log 2 ≤ Real.log R :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hR)
    have hlRpos : (0 : ℝ) < Real.log R := by linarith
    have hmain : Real.log C / Real.log R ≤ |Real.log C| / Real.log 2 := by
      rcases le_or_gt 0 (Real.log C) with h | h
      · rw [abs_of_nonneg h]
        gcongr
      · have h1 : Real.log C / Real.log R ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg h.le hlRpos.le
        have h2 : (0 : ℝ) ≤ |Real.log C| / Real.log 2 := by positivity
        linarith
    linarith
  have hcob : IsCoboundedUnder (· ≤ ·) atTop g := by
    refine ⟨0, fun b hb => ?_⟩
    rw [eventually_map] at hb
    obtain ⟨R, hR1, hR2⟩ := (hb.and (eventually_ge_atTop 2)).exists
    refine le_trans ?_ hR1
    rw [hg]
    refine div_nonneg (Real.log_nonneg ?_) (hlogpos R hR2).le
    exact_mod_cast hf1 R
  refine le_antisymm ?_ ?_
  · refine le_trans (limsup_le_limsup ?_ hcob hCtend.isBoundedUnder_le) ?_
    · filter_upwards [eventually_ge_atTop 2] with R hR
      exact hub R hR
    · exact le_of_eq hCtend.limsup_eq
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hctend : Tendsto (fun k : ℕ => Real.log c / Real.log (r k) + d) atTop (nhds d) := by
      have h1 : Tendsto r atTop atTop := hr.tendsto_atTop
      have h2 := ((tendsto_const_div_log (Real.log c)).add_const d).comp h1
      rw [zero_add] at h2
      exact h2
    have hfreq : ∃ᶠ R : ℕ in atTop, d - ε ≤ g R := by
      rw [frequently_atTop]
      intro N
      obtain ⟨k, hk1, hk2, hk3⟩ :=
        ((hctend.eventually_const_le (show d - ε < d by linarith)).and
          ((eventually_ge_atTop N).and (eventually_ge_atTop 2))).exists
      refine ⟨r k, ?_, ?_⟩
      · exact le_trans hk2 (hr.le_apply)
      · exact le_trans hk1 (hlb k (le_trans hk3 hr.le_apply))
    have := le_limsup_of_frequently_le hfreq hbdd
    linarith

end RWRS.Support
