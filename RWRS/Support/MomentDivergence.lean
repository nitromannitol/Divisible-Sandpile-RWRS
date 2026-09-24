/-
Step 5 of `lem:moment-sharpness`: an infinite moment makes the weighted tail sum
diverge.

The paper compares the sum with an integral and substitutes.  Here the same
thing is done by one pointwise inequality: for `z` above a threshold, every
`t` up to `T = ⌊(z/K)^{1/α}⌋` has `K t^α ≤ z`, and the sum of `t^c` over those
`t` is at least a constant times `T^{c+1}`, which is a constant times `z^{(c+1)/α}`.
Integrating that inequality bounds the moment by the tail sum, so an infinite
moment forces an infinite sum.
-/
import RWRS.Support.LocalTimeCount
import RWRS.Scenery

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

/-- **The pointwise comparison.**  Above the threshold `K·2^α` the `r`-th power
is at most a constant times the sum of `t^c` over the `t` with `K t^α ≤ z`. -/
theorem rpow_le_sum_of_tail {c α K : ℝ} (hc : 0 ≤ c) (hα : 0 < α) (hK : 0 < K)
    {z : ℝ} (hz : K * (2 : ℝ) ^ α ≤ z) :
    z ^ ((c + 1) / α)
      ≤ K ^ ((c + 1) / α) * 2 ^ (c + 1) * (c + 1)
        * ∑ i ∈ Finset.Icc 1 ⌊(z / K) ^ (1 / α)⌋₊, (i : ℝ) ^ c := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ α := Real.one_le_rpow (by norm_num) hα.le
  have hzpos : (0 : ℝ) < z := lt_of_lt_of_le (by positivity) hz
  set x : ℝ := (z / K) ^ (1 / α) with hxdef
  have hxK : (z / K) = x ^ α := by
    rw [hxdef, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hα.ne',
      Real.rpow_one]
  have hx2 : (2 : ℝ) ≤ x := by
    have hz' : (2 : ℝ) ^ α ≤ z / K := by
      rw [le_div_iff₀ hK, mul_comm]
      exact hz
    have := Real.rpow_le_rpow (by positivity) hz' (by positivity : (0:ℝ) ≤ 1 / α)
    rw [← Real.rpow_mul (by norm_num), mul_one_div, div_self hα.ne', Real.rpow_one] at this
    exact this
  set T : ℕ := ⌊x⌋₊ with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    exact (Nat.one_le_floor_iff x).2 (by linarith)
  have hTx : (T : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxT : x ≤ 2 * (T : ℝ) := by
    have := Nat.lt_floor_add_one x
    rw [← hTdef] at this
    have hT1R : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
    linarith
  -- the sum of the powers
  have hsum := pow_le_mul_sum_pow (p := c + 1) (by linarith) T
  simp only [add_sub_cancel_right] at hsum
  -- assemble
  have hzr : z ^ ((c + 1) / α) = K ^ ((c + 1) / α) * x ^ (c + 1) := by
    have hzK : z = K * (z / K) := by field_simp
    rw [hzK, hxK, Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul (by positivity)]
    congr 2
    field_simp
  have hxle : x ^ (c + 1) ≤ (2 * (T : ℝ)) ^ (c + 1) :=
    Real.rpow_le_rpow (by linarith) hxT (by linarith)
  have hsplit : (2 * (T : ℝ)) ^ (c + 1) = 2 ^ (c + 1) * (T : ℝ) ^ (c + 1) :=
    Real.mul_rpow (by norm_num) (Nat.cast_nonneg T)
  have hKr : (0 : ℝ) < K ^ ((c + 1) / α) := Real.rpow_pos_of_pos hK _
  have h2r : (0 : ℝ) < (2 : ℝ) ^ (c + 1) := Real.rpow_pos_of_pos (by norm_num) _
  rw [hzr]
  calc K ^ ((c + 1) / α) * x ^ (c + 1)
      ≤ K ^ ((c + 1) / α) * (2 ^ (c + 1) * (T : ℝ) ^ (c + 1)) := by
        rw [← hsplit]
        exact mul_le_mul_of_nonneg_left hxle hKr.le
    _ ≤ K ^ ((c + 1) / α)
          * (2 ^ (c + 1) * ((c + 1) * ∑ i ∈ Finset.Icc 1 T, (i : ℝ) ^ c)) := by
        refine mul_le_mul_of_nonneg_left ?_ hKr.le
        exact mul_le_mul_of_nonneg_left hsum h2r.le
    _ = K ^ ((c + 1) / α) * 2 ^ (c + 1) * (c + 1) * ∑ i ∈ Finset.Icc 1 T, (i : ℝ) ^ c := by
        ring

/-- **An infinite moment makes the weighted tail sum diverge.** -/
theorem tsum_tail_eq_top {ν : Measure ℝ} [IsProbabilityMeasure ν] {c α K : ℝ}
    (hc : 0 ≤ c) (hα : 0 < α) (hK : 0 < K)
    (hmom : RWRS.posMoment ν ((c + 1) / α) = ⊤) :
    (∑' t : ℕ, ENNReal.ofReal ((t : ℝ) ^ c) * ν {z : ℝ | K * (t : ℝ) ^ α ≤ z}) = ⊤ := by
  classical
  set r : ℝ := (c + 1) / α with hrdef
  have hr0 : (0 : ℝ) < r := by rw [hrdef]; positivity
  set C : ℝ := K ^ r * 2 ^ (c + 1) * (c + 1) with hCdef
  have hCpos : (0 : ℝ) < C := by
    rw [hCdef]
    have : (0 : ℝ) < K ^ r := Real.rpow_pos_of_pos hK r
    have : (0 : ℝ) < (2 : ℝ) ^ (c + 1) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  set B : ℝ := (K * (2 : ℝ) ^ α) ^ r with hBdef
  set g : ℕ → ℝ → ℝ≥0∞ :=
    fun t z => ENNReal.ofReal ((t : ℝ) ^ c) * (if K * (t : ℝ) ^ α ≤ z then 1 else 0) with hgdef
  have hsm : ∀ t : ℕ, MeasurableSet {z : ℝ | K * (t : ℝ) ^ α ≤ z} :=
    fun t => measurableSet_le measurable_const measurable_id
  have hind : ∀ t : ℕ,
      (fun z : ℝ => if K * (t : ℝ) ^ α ≤ z then (1 : ℝ≥0∞) else 0)
        = Set.indicator {z : ℝ | K * (t : ℝ) ^ α ≤ z} (fun _ => (1 : ℝ≥0∞)) := by
    intro t
    funext z
    by_cases h : K * (t : ℝ) ^ α ≤ z <;> simp [Set.indicator, h]
  have hindm : ∀ t : ℕ,
      Measurable (fun z : ℝ => if K * (t : ℝ) ^ α ≤ z then (1 : ℝ≥0∞) else 0) :=
    fun t => Measurable.ite (hsm t) measurable_const measurable_const
  have hmeas : ∀ t : ℕ, Measurable (g t) := by
    intro t
    rw [hgdef]
    exact (hindm t).const_mul _
  have hint : ∀ t : ℕ, ∫⁻ z, g t z ∂ν
      = ENNReal.ofReal ((t : ℝ) ^ c) * ν {z : ℝ | K * (t : ℝ) ^ α ≤ z} := by
    intro t
    rw [hgdef]
    simp only
    rw [MeasureTheory.lintegral_const_mul _ (hindm t), hind t,
      MeasureTheory.lintegral_indicator (hsm t),
      MeasureTheory.setLIntegral_const, one_mul]
  -- the pointwise bound
  have hpt : ∀ z : ℝ, ENNReal.ofReal ((max z 0) ^ r)
      ≤ ENNReal.ofReal B + ENNReal.ofReal C * ∑' t : ℕ, g t z := by
    intro z
    rcases lt_or_ge z (K * (2 : ℝ) ^ α) with hz | hz
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_) le_self_add
      refine Real.rpow_le_rpow (le_max_right _ _) ?_ hr0.le
      refine max_le hz.le ?_
      have : (0 : ℝ) < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    · have hzpos : (0 : ℝ) < z := by
        have : (0 : ℝ) < K * (2 : ℝ) ^ α := by
          have : (0 : ℝ) < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
          positivity
        linarith
      have hmaxz : max z 0 = z := max_eq_left hzpos.le
      set T : ℕ := ⌊(z / K) ^ (1 / α)⌋₊ with hTdef
      have hmain := rpow_le_sum_of_tail hc hα hK hz
      rw [← hrdef, ← hTdef] at hmain
      have hind : ∀ i ∈ Finset.Icc 1 T, g i z = ENNReal.ofReal ((i : ℝ) ^ c) := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        have hile : (i : ℝ) ≤ (T : ℝ) := by exact_mod_cast hi.2
        have hTx : (T : ℝ) ≤ (z / K) ^ (1 / α) := by
          rw [hTdef]
          exact Nat.floor_le (by positivity)
        have hpow : K * (i : ℝ) ^ α ≤ z := by
          have hxK : ((z / K) ^ (1 / α)) ^ α = z / K := by
            rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hα.ne',
              Real.rpow_one]
          have h1 : (i : ℝ) ^ α ≤ ((z / K) ^ (1 / α)) ^ α :=
            Real.rpow_le_rpow (Nat.cast_nonneg i) (le_trans hile hTx) hα.le
          rw [hxK] at h1
          calc K * (i : ℝ) ^ α ≤ K * (z / K) := mul_le_mul_of_nonneg_left h1 hK.le
            _ = z := by field_simp
        rw [hgdef]
        simp only [if_pos hpow, mul_one]
      have hfin : ∑ i ∈ Finset.Icc 1 T, ENNReal.ofReal ((i : ℝ) ^ c)
          ≤ ∑' t : ℕ, g t z := by
        rw [← Finset.sum_congr rfl hind]
        exact ENNReal.sum_le_tsum _
      have hcast : ENNReal.ofReal (∑ i ∈ Finset.Icc 1 T, (i : ℝ) ^ c)
          = ∑ i ∈ Finset.Icc 1 T, ENNReal.ofReal ((i : ℝ) ^ c) :=
        ENNReal.ofReal_sum_of_nonneg fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) c
      rw [hmaxz]
      refine le_trans (ENNReal.ofReal_le_ofReal hmain) ?_
      rw [← hCdef, ENNReal.ofReal_mul hCpos.le, hcast]
      exact le_trans (mul_le_mul_right hfin _) le_add_self
  -- integrate
  by_contra hfin
  refine absurd hmom ?_
  have hle : RWRS.posMoment ν r
      ≤ ENNReal.ofReal B + ENNReal.ofReal C
        * ∑' t : ℕ, ENNReal.ofReal ((t : ℝ) ^ c) * ν {z : ℝ | K * (t : ℝ) ^ α ≤ z} := by
    rw [RWRS.posMoment]
    refine le_trans (MeasureTheory.lintegral_mono hpt) ?_
    rw [MeasureTheory.lintegral_add_left measurable_const,
      MeasureTheory.lintegral_const, measure_univ, mul_one]
    gcongr
    rw [MeasureTheory.lintegral_const_mul _
      (Measurable.tsum fun t => hmeas t)]
    refine mul_le_mul_right (le_of_eq ?_) _
    rw [MeasureTheory.lintegral_tsum fun t => (hmeas t).aemeasurable]
    exact tsum_congr hint
  refine ne_top_of_le_ne_top ?_ hle
  exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin⟩

end RWRS.Support
