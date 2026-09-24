/-
The parameter arithmetic of `prop:poly-growth`.

Three elementary estimates carry the exponent bookkeeping of Steps 3 to 5.  A
power against a stretched exponential is below a negative power, which is what
makes the good-walk contribution of `eq:poly-Bernstein` summable in the scale.
The scale itself is below every positive power of the block length, which is how
the logarithms of the radius and of the pigeonhole are absorbed into an
arbitrarily small extra exponent, exactly as `clockH_le_rpow` absorbs the
logarithm of the critical spectral dimension in `prop:subcritical`.  Markov's
inequality for the positive-part moment and the grouping of a sum over the
vertices along the fibres of an integer-valued map are what Step 1 needs.
-/
import RWRS.Support.SubPolyChain
import RWRS.Support.SubTail

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- **A power against a stretched exponential is below a negative power.** -/
theorem rpow_mul_exp_neg_le {A c θ : ℝ} (hc : 0 < c) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      x ^ A * Real.exp (-(c * x ^ θ)) ≤ C * x ^ (-(1:ℝ)) := by
  obtain ⟨n, hn⟩ := exists_nat_ge ((A + 1) / θ)
  have hnθ : A + 1 ≤ (n : ℝ) * θ := by
    rw [div_le_iff₀ hθ] at hn
    linarith
  refine ⟨(Nat.factorial n : ℝ) / c ^ n, by positivity, fun x hx => ?_⟩
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hxθ : (0:ℝ) < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hcx : (0:ℝ) < c * x ^ θ := by positivity
  have h1 : Real.exp (-(c * x ^ θ)) ≤ (Nat.factorial n : ℝ) / (c * x ^ θ) ^ n :=
    exp_neg_le_factorial_div_pow n hcx
  have h2 : (c * x ^ θ) ^ n = c ^ n * x ^ ((n : ℝ) * θ) := by
    rw [mul_pow, ← Real.rpow_natCast (x ^ θ) n, ← Real.rpow_mul hx0.le]
    ring_nf
  rw [h2] at h1
  have hA0 : (0:ℝ) ≤ x ^ A := Real.rpow_nonneg hx0.le A
  have h3 : x ^ A * Real.exp (-(c * x ^ θ))
      ≤ x ^ A * ((Nat.factorial n : ℝ) / (c ^ n * x ^ ((n : ℝ) * θ))) :=
    mul_le_mul_of_nonneg_left h1 hA0
  have hden : (0:ℝ) < c ^ n * x ^ ((n : ℝ) * θ) := by positivity
  have h4 : x ^ A * ((Nat.factorial n : ℝ) / (c ^ n * x ^ ((n : ℝ) * θ)))
      = ((Nat.factorial n : ℝ) / c ^ n) * x ^ (A - (n : ℝ) * θ) := by
    rw [Real.rpow_sub hx0]
    field_simp
  have h5 : x ^ (A - (n : ℝ) * θ) ≤ x ^ (-(1:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have h6 : (0:ℝ) ≤ (Nat.factorial n : ℝ) / c ^ n := by positivity
  calc x ^ A * Real.exp (-(c * x ^ θ))
      ≤ x ^ A * ((Nat.factorial n : ℝ) / (c ^ n * x ^ ((n : ℝ) * θ))) := h3
    _ = ((Nat.factorial n : ℝ) / c ^ n) * x ^ (A - (n : ℝ) * θ) := h4
    _ ≤ ((Nat.factorial n : ℝ) / c ^ n) * x ^ (-(1:ℝ)) := mul_le_mul_of_nonneg_left h5 h6

/-- **The scale is below every positive power of the block length.** -/
theorem succ_le_rpow {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, (k : ℝ) + 1 ≤ C * ((2:ℝ) ^ (k + 1)) ^ s := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / (s * Real.log 2), by positivity, fun k => ?_⟩
  have hx1 : (1:ℝ) ≤ (2:ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hlog : Real.log ((2:ℝ) ^ (k + 1)) = ((k : ℝ) + 1) * Real.log 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  have hmain : Real.log ((2:ℝ) ^ (k + 1)) ≤ ((2:ℝ) ^ (k + 1)) ^ s / s :=
    log_le_rpow_div hx1 hs
  rw [hlog] at hmain
  have hpos : (0:ℝ) < ((2:ℝ) ^ (k + 1)) ^ s := Real.rpow_pos_of_pos (by positivity) s
  have h7 : s * (((k : ℝ) + 1) * Real.log 2) ≤ s * (((2:ℝ) ^ (k + 1)) ^ s / s) :=
    mul_le_mul_of_nonneg_left hmain hs.le
  have h8 : s * (((2:ℝ) ^ (k + 1)) ^ s / s) = ((2:ℝ) ^ (k + 1)) ^ s := by
    field_simp
  rw [h8] at h7
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity : (0:ℝ) < s * Real.log 2)]
  nlinarith [h7]

/-- **Markov's inequality for the positive-part moment.** -/
theorem meas_Ioi_le_posMoment (ν : Measure ℝ) {s p : ℝ} (hs : 0 < s) (hp : 0 < p) :
    ν (Set.Ioi s) ≤ RWRS.posMoment ν p / ENNReal.ofReal (s ^ p) := by
  have hsp : (0:ℝ) < s ^ p := Real.rpow_pos_of_pos hs p
  have hmeas : Measurable fun z : ℝ => ENNReal.ofReal (max z 0 ^ p) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.max measurable_const).pow_const p)
  have hsub : Set.Ioi s ⊆ {z : ℝ | ENNReal.ofReal (s ^ p) ≤ ENNReal.ofReal (max z 0 ^ p)} := by
    intro z hz
    have hz' : s < z := hz
    have hle : s ≤ max z 0 := le_trans hz'.le (le_max_left z 0)
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hs.le hle hp.le)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  rw [RWRS.posMoment]
  exact MeasureTheory.meas_ge_le_lintegral_div hmeas.aemeasurable
    (ENNReal.ofReal_pos.2 hsp).ne' ENNReal.ofReal_ne_top

/-- **A sum over the vertices, grouped along the fibres of an integer-valued
map.** -/
theorem tsum_le_fiber_card {V : Type*} (g : V → ℝ≥0∞) (f : V → ℕ) (c B : ℕ → ℝ≥0∞)
    (hg : ∀ v : V, g v ≤ c (f v))
    (hcard : ∀ i : ℕ, ((f ⁻¹' {i}).encard : ℝ≥0∞) ≤ B i) :
    ∑' v : V, g v ≤ ∑' i : ℕ, B i * c i := by
  rw [← ENNReal.tsum_fiberwise g f]
  refine ENNReal.tsum_le_tsum fun i => ?_
  have hstep : ∑' v : (f ⁻¹' {i} : Set V), g (v : V) ≤ ∑' _v : (f ⁻¹' {i} : Set V), c i := by
    refine ENNReal.tsum_le_tsum fun v => ?_
    have hv : f (v : V) = i := Set.mem_singleton_iff.1 (Set.mem_preimage.1 v.2)
    have hgv := hg (v : V)
    rw [hv] at hgv
    exact hgv
  refine le_trans hstep ?_
  rw [ENNReal.tsum_set_const]
  exact mul_le_mul' (hcard i) le_rfl

end RWRS.Support
