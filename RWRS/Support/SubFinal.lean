/-
The choice of the parameters of `prop:subcritical`, and the truncation.

`rwrs.tex:1168`: "Replacing `ξ(v)` by `max(ξ(v),-M)` increases `ζ` pointwise ...
for large `M` the truncated mean is still negative.  We may therefore assume
`E[ξ] > -∞` and `E[|ξ|^p] < ∞`."  The exponent `q < (p-1)(d_s/2 ∧ 1)` fixes the
slack `η` in the clock bound, the good-walk exponent `δ`, and the order `2n` of
the polynomial replacing the Gaussian remainder.
-/
import RWRS.Support.SubSeries
import RWRS.Support.SubTrunc
import RWRS.Frozen.FukNagaev
import RWRS.Support.SubStop
import RWRS.External.BernsteinProved

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- A finite `p`-th absolute moment with `p ≥ 2` makes the centred square
integrable. -/
theorem integrable_sq_sub {ν : Measure ℝ} [IsProbabilityMeasure ν] {m p : ℝ}
    (hp : 2 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤) :
    Integrable (fun z : ℝ => (z - m) ^ 2) ν := by
  have hdom : ∀ z : ℝ, ‖(z - m) ^ 2‖ ≤ (2 + 2 * m ^ 2) + 2 * |z| ^ p := by
    intro z
    have h1 : |z| ^ (2:ℝ) ≤ 1 + |z| ^ p := by
      rcases le_or_gt |z| 1 with h | h
      · have h0 : |z| ^ (2:ℝ) ≤ 1 := by
          calc |z| ^ (2:ℝ) ≤ (1:ℝ) ^ (2:ℝ) := Real.rpow_le_rpow (abs_nonneg z) h (by norm_num)
            _ = 1 := Real.one_rpow _
        have h2 : (0:ℝ) ≤ |z| ^ p := Real.rpow_nonneg (abs_nonneg z) p
        linarith
      · have h2 : |z| ^ (2:ℝ) ≤ |z| ^ p := Real.rpow_le_rpow_of_exponent_le h.le hp
        linarith
    have h2 : |z| ^ (2:ℝ) = z ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (z + m), h1, h2]
  have hmeas : AEStronglyMeasurable (fun z : ℝ => |z| ^ p) ν := by
    have : Measurable fun z : ℝ => |z| ^ p := (measurable_id.abs).pow_const p
    exact this.aestronglyMeasurable
  have hI : Integrable (fun z : ℝ => |z| ^ p) ν := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      fun z => Real.rpow_nonneg (abs_nonneg z) p)]
    exact lt_of_le_of_ne le_top hmom
  have hgint : Integrable (fun z : ℝ => (2 + 2 * m ^ 2) + 2 * |z| ^ p) ν :=
    (integrable_const _).add (hI.const_mul 2)
  refine Integrable.mono' hgint ?_ (Filter.Eventually.of_forall hdom)
  fun_prop

/-- **Part 1 of `prop:subcritical`**, for one exponent `q`: the `q`-th moment of
`sup_n S_n` is finite, uniformly in the starting vertex. -/
theorem lintegral_supPayoff_rpow_ne_top [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (hG : G.Connected)
    (hVBE : RWRS.External.VonBahrEsseen) (hFNt : RWRS.External.FukNagaevTail)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d) {d_s A : ℝ} (hds : 0 < d_s)
    (hsp : RWRS.SpectralDimensionBound G d_s A)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : RWRS.extMean ν < 0)
    {p q : ℝ} (hp : 1 + 2 / d_s < p) (hmom : RWRS.posMoment ν p ≠ ⊤)
    (hq1 : 1 ≤ q) (hqθ : q < (p - 1) * min (d_s / 2) 1) :
    (⨆ x : V, ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x)) ≠ ⊤ := by
  classical
  have hq0 : (0:ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hdeg : ∀ v : V, 1 ≤ G.degree v := fun v => degree_pos hG v
  have hd : 0 < d := by
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    exact lt_of_lt_of_le (degree_pos hG v) (hbd v)
  set θ : ℝ := min (d_s / 2) 1 with hθdef
  have hθ0 : (0:ℝ) < θ := lt_min (by linarith) zero_lt_one
  have hθ1 : θ ≤ 1 := min_le_right _ _
  have hpgt1 : (1:ℝ) < p := by
    have : (0:ℝ) < 2 / d_s := by positivity
    linarith
  have hp1 : (0:ℝ) < p - 1 := by linarith
  have hp2 : (2:ℝ) < p := by nlinarith [hqθ, hq1, hθ1, hp1]
  have hple : (1:ℝ) ≤ p := by linarith
  have hqp : q < p := by nlinarith [hqθ, hθ1, hp1]
  have hαθ : max (1 - d_s / 2) 0 = 1 - θ := by
    rcases le_or_gt (d_s / 2) 1 with h | h
    · rw [hθdef, min_eq_left h, max_eq_left (by linarith)]
    · rw [hθdef, min_eq_right h.le, max_eq_right (by linarith)]
      ring
  set η : ℝ := (θ - q / (p - 1)) / 2 with hηdef
  have hηval : η * (p - 1) = (θ * (p - 1) - q) / 2 := by
    rw [hηdef]
    field_simp
  have hη : 0 < η := by
    rw [hηdef]
    have : q / (p - 1) < θ := by
      rw [div_lt_iff₀ hp1]
      linarith [hqθ]
    linarith
  set δ : ℝ := θ / 2 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ < min (d_s / 2) 1 := by rw [hδdef, ← hθdef]; linarith
  set nn : ℕ := ⌈2 * (1 + q) / θ⌉₊ + 1 with hnndef
  have hnnbig : 2 * (1 + q) / θ < (nn : ℝ) := by
    have h1 : 2 * (1 + q) / θ ≤ (⌈2 * (1 + q) / θ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 * (1 + q) / θ⌉₊ : ℕ) : ℝ) + 1 = (nn : ℝ) := by
      rw [hnndef]; push_cast; ring
    linarith
  have hnnθ : 1 + q < (nn : ℝ) * θ / 2 := by
    rw [div_lt_iff₀ hθ0] at hnnbig
    linarith
  have hq2 : q < ((2 * nn : ℕ) : ℝ) := by
    have hcast : ((2 * nn : ℕ) : ℝ) = 2 * (nn : ℝ) := by push_cast; ring
    rw [hcast]
    nlinarith [hnnθ, hθ1, hq0]
  have he1 : 1 + (max (1 - d_s / 2) 0 + η) * (p - 1) + q - p < 0 := by
    rw [hαθ]
    nlinarith [hηval, hqθ, hθdef]
  have he2 : 1 + (nn : ℝ) + (max (1 - d_s / 2) 0 + δ) * nn + q - ((2 * nn : ℕ) : ℝ) < 0 := by
    have hcast : ((2 * nn : ℕ) : ℝ) = 2 * (nn : ℝ) := by push_cast; ring
    rw [hαθ, hcast, hδdef]
    nlinarith [hnnθ]
  obtain ⟨M, hM0, habs, m, hmext, hmneg⟩ := exists_lowTrunc ν hple hmom hmean
  set ρ : Measure ℝ := ν.map (lowTrunc M) with hρdef
  haveI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map (measurable_lowTrunc M).aemeasurable
  have hpp : RWRS.posPart ρ ≠ ⊤ := by
    rw [hρdef, posPart_map_lowTrunc ν hM0]
    exact posPart_ne_top_of_posMoment ν hple hmom
  have hnn' : RWRS.negPart ρ ≠ ⊤ := negPart_map_lowTrunc_ne_top ν M
  have hint : Integrable (fun z : ℝ => z) ρ := integrable_id_of_finite hpp hnn'
  have hm : ∫ z, z ∂ρ = m := by
    have h1 := extMean_eq_coe hpp hnn'
    rw [hmext] at h1
    have h2 : m = (RWRS.posPart ρ).toReal - (RWRS.negPart ρ).toReal := by exact_mod_cast h1
    rw [integral_id_eq hint, ← h2]
  have hsq : Integrable (fun z : ℝ => (z - m) ^ 2) ρ := integrable_sq_sub hp2.le habs
  obtain ⟨c, Cp, hc, hCp, hFNb⟩ :=
    (RWRS.Frozen.fukNagaev hVBE hFNt RWRS.External.bernstein).2.1 p hp2.le
  obtain ⟨B, hB, hbound⟩ := exists_supPayoff_moment_bound (G := G) (ν := ρ) hG nn d hFNb
    hbd hdeg hd hds hsp m hmext hmneg hint hm hsq hple habs hc hCp.le hq1 hqp hq2 hη hδ0 hδ1
    he1 he2
  refine ne_top_of_le_ne_top hB (iSup_le fun x => ?_)
  exact le_trans (lintegral_supPayoff_rpow_le_lowTrunc ν hq0.le x) (hbound x)


/-- **Part 2 of `prop:subcritical`**: when the exponent range contains `1`, the
value of the optimal bounded rule is almost surely finite. -/
theorem ae_supStopValue_ne_top [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] [DecidableEq V] (hG : G.Connected)
    (hVBE : RWRS.External.VonBahrEsseen) (hFNt : RWRS.External.FukNagaevTail)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d) {d_s A : ℝ} (hds : 0 < d_s)
    (hsp : RWRS.SpectralDimensionBound G d_s A)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : RWRS.extMean ν < 0)
    {p : ℝ} (hp : 1 + 2 / d_s < p) (hmom : RWRS.posMoment ν p ≠ ⊤)
    (hgt : 1 < (p - 1) * min (d_s / 2) 1) (x : V) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ x ≠ ⊤ := by
  classical
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by rw [walkLaw_eq_lib]; infer_instance
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have h1 := lintegral_supPayoff_rpow_ne_top (G := G) hG hVBE hFNt d hbd hds hsp ν hmean
    hp hmom (q := 1) le_rfl hgt
  have h2 : (∫⁻ z, RWRS.supPayoff G z.1 z.2 ∂(RWRS.jointLaw G ν x)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top h1 ?_
    refine le_trans (le_of_eq ?_) (le_iSup (fun y : V =>
      ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ (1:ℝ) ∂(RWRS.jointLaw G ν y)) x)
    exact lintegral_congr fun z => (ENNReal.rpow_one _).symm
  have hmeasf : Measurable fun z : (V → ℝ) × (ℕ → V) => RWRS.supPayoff G z.1 z.2 :=
    measurable_supPayoff_prod
  have h3 : (∫⁻ ξ, (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G x)) ∂(RWRS.iidLaw V ν))
      ≠ ⊤ := by
    rw [RWRS.jointLaw, MeasureTheory.lintegral_prod _ hmeasf.aemeasurable] at h2
    exact h2
  have hmeasg : Measurable fun ξ : V → ℝ => ∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G x) :=
    hmeasf.lintegral_prod_right'
  have h4 := ae_lt_top hmeasg h3
  filter_upwards [h4] with ξ hξ
  exact ne_top_of_le_ne_top (ne_of_lt hξ) (supStopValue_le_lintegral_supPayoff hG ξ x)


end RWRS.Support
