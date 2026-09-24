/-
Part (c) of `lem:good-walk`: Hölder combines the two previous parts.

The block variable restricted to the bad-walk event is a product of the block
variable and an indicator, so Hölder's inequality with the exponents `p/q` and
`p/(p-q)` bounds its integral by the `q/p`-th power of the `p`-th moment times
the `(p-q)/p`-th power of the probability of the bad event.  Both factors are
powers of `N = 2^{k+1}`, and the exponent of the second one is as negative as
one likes once `r` is large, so the product decays faster than `2^{-3k}`.
-/
import RWRS.Support.GoodWalkMoment

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- A set of trajectories has the same probability under the joint law and under
the law of the walk. -/
theorem jointLaw_walk_set [Infinite V] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (x : V) {S : Set (ℕ → V)} (_hS : MeasurableSet S) :
    RWRS.jointLaw G ν x {z : (V → ℝ) × (ℕ → V) | z.2 ∈ S} = RWRS.walkLaw G x S := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by rw [walkLaw_eq_lib]; infer_instance
  have hset : {z : (V → ℝ) × (ℕ → V) | z.2 ∈ S} = (Set.univ : Set (V → ℝ)) ×ˢ S := by
    ext z; simp
  rw [RWRS.jointLaw, hset, MeasureTheory.Measure.prod_prod, measure_univ, one_mul]

/-- The two exponents of the Hölder step are conjugate. -/
theorem holderConjugate_of_lt {p q : ℝ} (hq : 1 ≤ q) (hqp : q < p) :
    (p / q).HolderConjugate (p / (p - q)) := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hq) hqp.le
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have ha : (0 : ℝ) < q / p := by positivity
  have hb : (0 : ℝ) < (p - q) / p := by
    have : (0 : ℝ) < p - q := by linarith
    positivity
  have hab : q / p + (p - q) / p = 1 := by field_simp; ring
  have h := Real.holderConjugate_one_div ha hb hab
  have h1 : (1 : ℝ) / (q / p) = p / q := by field_simp
  have h2 : (1 : ℝ) / ((p - q) / p) = p / (p - q) := by field_simp
  rwa [h1, h2] at h

/-- **The Hölder step.** -/
theorem lintegral_indicator_dyadicY_le [Infinite V] (_hG : G.Connected) {d : ℕ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {m : ℝ} {p q : ℝ} (hq : 1 ≤ q) (hqp : q < p)
    {α δ : ℝ} (x : V) (k : ℕ) :
    (∫⁻ z : (V → ℝ) × (ℕ → V), Set.indicator (RWRS.goodWalk (V := V) α δ k)ᶜ
        (fun X => ENNReal.ofReal (RWRS.dyadicY G z.1 m d k X ^ q)) z.2
        ∂(RWRS.jointLaw G ν x))
      ≤ (∫⁻ z : (V → ℝ) × (ℕ → V), ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ p)
            ∂(RWRS.jointLaw G ν x)) ^ (q / p)
        * (RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ) ^ ((p - q) / p) := by
  classical
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hq) hqp.le
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hpq0 : (0 : ℝ) < p - q := by linarith
  set f : (V → ℝ) × (ℕ → V) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q) with hf
  set g : (V → ℝ) × (ℕ → V) → ℝ≥0∞ :=
    fun z => Set.indicator (RWRS.goodWalk (V := V) α δ k)ᶜ (fun _ => (1 : ℝ≥0∞)) z.2 with hg
  have hAc : MeasurableSet (RWRS.goodWalk (V := V) α δ k)ᶜ :=
    (measurableSet_goodWalk (V := V) α δ k).compl
  have hfm : Measurable f := measurable_dyadicY_rpow m d k hq0.le
  have hgm : Measurable g := by
    refine Measurable.indicator measurable_const hAc |>.comp measurable_snd
  have hsplit : ∀ z : (V → ℝ) × (ℕ → V),
      Set.indicator (RWRS.goodWalk (V := V) α δ k)ᶜ
        (fun X => ENNReal.ofReal (RWRS.dyadicY G z.1 m d k X ^ q)) z.2 = (f * g) z := by
    intro z
    by_cases hz : z.2 ∈ (RWRS.goodWalk (V := V) α δ k)ᶜ
    · rw [Set.indicator_of_mem hz]
      simp only [Pi.mul_apply, hf, hg, Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz]
      simp only [Pi.mul_apply, hg, Set.indicator_of_notMem hz, mul_zero]
  rw [MeasureTheory.lintegral_congr hsplit]
  refine le_trans (ENNReal.lintegral_mul_le_Lp_mul_Lq _ (holderConjugate_of_lt hq hqp)
    hfm.aemeasurable hgm.aemeasurable) (le_of_eq ?_)
  have hfp : ∀ z, f z ^ (p / q) = ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ p) := by
    intro z
    have hYnn : (0 : ℝ) ≤ RWRS.dyadicY G z.1 m d k z.2 := le_max_right _ _
    rw [hf]
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hYnn q) (by positivity),
      ← Real.rpow_mul hYnn]
    congr 2
    field_simp
  have hgp : ∀ z, g z ^ (p / (p - q)) = g z := by
    intro z
    rw [hg]
    simp only
    by_cases hz : z.2 ∈ (RWRS.goodWalk (V := V) α δ k)ᶜ
    · rw [Set.indicator_of_mem hz, ENNReal.one_rpow]
    · rw [Set.indicator_of_notMem hz, ENNReal.zero_rpow_of_pos (by positivity)]
  have hgeq : g = (Prod.snd ⁻¹' (RWRS.goodWalk (V := V) α δ k)ᶜ).indicator
      (fun _ : (V → ℝ) × (ℕ → V) => (1 : ℝ≥0∞)) := by
    funext z
    rw [hg]
    simp only [Set.indicator, Set.mem_preimage]
  have hgint : ∫⁻ z : (V → ℝ) × (ℕ → V), g z ∂(RWRS.jointLaw G ν x)
      = RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ := by
    rw [hgeq, MeasureTheory.lintegral_indicator (measurable_snd hAc),
      MeasureTheory.setLIntegral_const, one_mul]
    exact jointLaw_walk_set ν x hAc
  rw [MeasureTheory.lintegral_congr hfp, MeasureTheory.lintegral_congr hgp, hgint]
  congr 1
  · congr 1
    field_simp
  · congr 1
    field_simp

/-! ### From a power bound on the bad event to exponential decay -/

/-- The logarithm is below every positive power, up to a constant. -/
theorem one_add_log_le_rpow {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    1 + Real.log x ≤ (1 + 1 / ε) * x ^ ε := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hxe : (1 : ℝ) ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hxepos : (0 : ℝ) < x ^ ε := lt_of_lt_of_le zero_lt_one hxe
  have hlog := Real.log_le_sub_one_of_pos hxepos
  rw [Real.log_rpow hx0] at hlog
  have hlogx : Real.log x ≤ (x ^ ε - 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hdiv : (x ^ ε - 1) / ε ≤ x ^ ε / ε := by
    refine div_le_div_of_nonneg_right (by linarith) hε.le
  have : Real.log x ≤ x ^ ε / ε := le_trans hlogx hdiv
  have hfin : (1 : ℝ) + x ^ ε / ε ≤ (1 + 1 / ε) * x ^ ε := by
    have : (1 + 1 / ε) * x ^ ε = x ^ ε + x ^ ε / ε := by field_simp
    rw [this]
    linarith
  linarith

/-- A negative power of the dyadic scale decays exponentially. -/
theorem rpow_two_pow_le {c : ℝ} (hc : c ≤ -3) (k : ℕ) :
    ((2 : ℝ) ^ (k + 1)) ^ c ≤ (2 : ℝ) ^ (-(3 : ℝ) * k) := by
  have h2 : (1 : ℝ) ≤ 2 := by norm_num
  have hpow : ((2 : ℝ) ^ (k + 1)) ^ c = (2 : ℝ) ^ (((k : ℝ) + 1) * c) := by
    rw [show ((2 : ℝ) ^ (k + 1)) = (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ)) from
      (Real.rpow_natCast 2 (k + 1)).symm, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  rw [hpow]
  refine Real.rpow_le_rpow_of_exponent_le h2 ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [hc, hk]

/-- **Part (c) from a power bound on the bad event.** -/
theorem lintegral_indicator_decay [Infinite V] (hG : G.Connected) {d : ℕ}
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {m p q : ℝ} (hq : 1 ≤ q) (hqp : q < p)
    {α δ : ℝ} {Cb : ℝ} (hCb : 0 < Cb)
    (hb : ∀ (x : V) (k : ℕ),
      (∫⁻ z : (V → ℝ) × (ℕ → V), ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ p)
          ∂(RWRS.jointLaw G ν x))
        ≤ ENNReal.ofReal (Cb * ((2 : ℝ) ^ (k + 1)) ^ p))
    {Ka ea : ℝ} (hKa : 0 < Ka)
    (ha : ∀ (x : V) (k : ℕ), RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ
      ≤ ENNReal.ofReal (Ka * ((2 : ℝ) ^ (k + 1)) ^ ea))
    (hexp : q + ea * ((p - q) / p) ≤ -3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : V) (k : ℕ),
      (∫⁻ z : (V → ℝ) × (ℕ → V), Set.indicator (RWRS.goodWalk (V := V) α δ k)ᶜ
          (fun X => ENNReal.ofReal (RWRS.dyadicY G z.1 m d k X ^ q)) z.2
          ∂(RWRS.jointLaw G ν x))
        ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(3 : ℝ) * k)) := by
  classical
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hq) hqp.le
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  set t : ℝ := q / p with ht
  set s : ℝ := (p - q) / p with hs
  have ht0 : (0 : ℝ) < t := by rw [ht]; positivity
  have hs0 : (0 : ℝ) < s := by
    rw [hs]
    have : (0 : ℝ) < p - q := by linarith
    positivity
  refine ⟨Cb ^ t * Ka ^ s, by positivity, fun x k => ?_⟩
  have hNpos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hCbN : (0 : ℝ) ≤ Cb * ((2 : ℝ) ^ (k + 1)) ^ p := by positivity
  have hKaN : (0 : ℝ) ≤ Ka * ((2 : ℝ) ^ (k + 1)) ^ ea := by positivity
  refine le_trans (lintegral_indicator_dyadicY_le hG ν hq hqp (α := α) (δ := δ) x k) ?_
  have hstep : (∫⁻ z : (V → ℝ) × (ℕ → V), ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ p)
        ∂(RWRS.jointLaw G ν x)) ^ t
      * (RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ) ^ s
      ≤ ENNReal.ofReal (Cb * ((2 : ℝ) ^ (k + 1)) ^ p) ^ t
        * ENNReal.ofReal (Ka * ((2 : ℝ) ^ (k + 1)) ^ ea) ^ s :=
    mul_le_mul' (ENNReal.rpow_le_rpow (hb x k) ht0.le)
      (ENNReal.rpow_le_rpow (ha x k) hs0.le)
  refine le_trans hstep ?_
  rw [ENNReal.ofReal_rpow_of_nonneg hCbN ht0.le, ENNReal.ofReal_rpow_of_nonneg hKaN hs0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hCbN t)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexpand : (Cb * ((2 : ℝ) ^ (k + 1)) ^ p) ^ t * (Ka * ((2 : ℝ) ^ (k + 1)) ^ ea) ^ s
      = (Cb ^ t * Ka ^ s) * ((2 : ℝ) ^ (k + 1)) ^ (q + ea * s) := by
    rw [Real.mul_rpow hCb.le (Real.rpow_nonneg hNpos.le p),
      Real.mul_rpow hKa.le (Real.rpow_nonneg hNpos.le ea),
      ← Real.rpow_mul hNpos.le, ← Real.rpow_mul hNpos.le]
    have hpt : p * t = q := by rw [ht]; field_simp
    rw [hpt, Real.rpow_add hNpos]
    ring
  rw [hexpand]
  have hCnn : (0 : ℝ) ≤ Cb ^ t * Ka ^ s := by positivity
  exact mul_le_mul_of_nonneg_left (rpow_two_pow_le hexp k) hCnn

/-- The logarithmic factor at the critical exponent is absorbed into a small
power of the dyadic scale. -/
theorem log_power_bound {ε : ℝ} (hε : 0 < ε) {Cr : ℝ} (hCr : 0 ≤ Cr) {r : ℕ} (hr : 1 ≤ r)
    (b : ℝ) (k : ℕ) :
    Cr * ((2 : ℝ) ^ (k + 1)) ^ b * (1 + Real.log ((2 : ℝ) ^ (k + 1))) ^ (r - 1)
      ≤ (Cr * (1 + 1 / ε) ^ (r - 1))
        * ((2 : ℝ) ^ (k + 1)) ^ (b + ε * ((r : ℝ) - 1)) := by
  have hNpos : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hN1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
  have hlognn : (0 : ℝ) ≤ 1 + Real.log ((2 : ℝ) ^ (k + 1)) := by
    have := Real.log_nonneg hN1
    linarith
  have h1 := one_add_log_le_rpow hε hN1
  have h2 : (1 + Real.log ((2 : ℝ) ^ (k + 1))) ^ (r - 1)
      ≤ ((1 + 1 / ε) * ((2 : ℝ) ^ (k + 1)) ^ ε) ^ (r - 1) :=
    pow_le_pow_left₀ hlognn h1 (r - 1)
  have hcast : (((r - 1 : ℕ) : ℝ)) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr]
    norm_num
  have h4 : (((2 : ℝ) ^ (k + 1)) ^ ε) ^ (r - 1)
      = ((2 : ℝ) ^ (k + 1)) ^ (ε * ((r : ℝ) - 1)) := by
    rw [← Real.rpow_natCast (((2 : ℝ) ^ (k + 1)) ^ ε) (r - 1), ← Real.rpow_mul hNpos.le, hcast]
  have h3 : ((1 + 1 / ε) * ((2 : ℝ) ^ (k + 1)) ^ ε) ^ (r - 1)
      = (1 + 1 / ε) ^ (r - 1) * ((2 : ℝ) ^ (k + 1)) ^ (ε * ((r : ℝ) - 1)) := by
    rw [mul_pow, h4]
  rw [h3] at h2
  have hbase : (0 : ℝ) ≤ Cr * ((2 : ℝ) ^ (k + 1)) ^ b := by positivity
  have hmul := mul_le_mul_of_nonneg_left h2 hbase
  refine le_trans hmul (le_of_eq ?_)
  rw [Real.rpow_add hNpos]
  ring

end RWRS.Support
