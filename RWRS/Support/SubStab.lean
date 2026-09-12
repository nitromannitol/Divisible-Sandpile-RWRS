/-
The moments of the odometer on a bounded-degree graph, for `thm:stab`(i).

`rwrs.tex:157`: "Theorem thm:stab(i) follows: setting `ξ(v) = σ(v)-1` gives
`E[ξ] = μ-1 < 0` and `E[(ξ⁺)^p] ≤ E[(σ⁺)^p] < ∞`, so
`sup_x E_x[(sup_n S_n)^q] < ∞`.  By Corollary cor:RW-infinite,
`u_∞(x) ≤ E_x[sup_n S_n | ξ]`, and Jensen's inequality gives
`E[u_∞(x)^q] < ∞`."  The spectral dimension is `d_s = 1`, which the universal
heat kernel bound on bounded-degree graphs supplies.
-/
import RWRS.Support.SubFinal
import RWRS.Frozen.RWInfinite

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal


/-- **Jensen's inequality for a convex power against a probability measure.** -/
theorem lintegral_rpow_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {g : Ω → ℝ≥0∞} (hg : AEMeasurable g μ) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ ω, g ω ∂μ) ^ q ≤ ∫⁻ ω, g ω ^ q ∂μ := by
  rcases eq_or_lt_of_le hq with heq | hlt
  · rw [← heq]
    simp only [ENNReal.rpow_one]
    exact le_rfl
  · have hq0 : (0:ℝ) < q := lt_trans zero_lt_one hlt
    have hpq : Real.HolderConjugate q (q / (q - 1)) := Real.HolderConjugate.conjExponent hlt
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hg
      (aemeasurable_const (b := (1 : ℝ≥0∞)))
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
      ENNReal.one_rpow] at h
    calc (∫⁻ ω, g ω ∂μ) ^ q
        ≤ ((∫⁻ ω, g ω ^ q ∂μ) ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow h hq0.le
      _ = ∫⁻ ω, g ω ^ q ∂μ := by
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ (ne_of_gt hq0), ENNReal.rpow_one]


/-! ### The law of the excess -/

theorem posPart_map_sub_one (ν : Measure ℝ) :
    RWRS.posPart (ν.map (fun z : ℝ => z - 1)) = ∫⁻ z, ENNReal.ofReal (z - 1) ∂ν :=
  lintegral_map ENNReal.measurable_ofReal (measurable_id.sub_const 1)

theorem negPart_map_sub_one (ν : Measure ℝ) :
    RWRS.negPart (ν.map (fun z : ℝ => z - 1)) = ∫⁻ z, ENNReal.ofReal (1 - z) ∂ν := by
  have h : RWRS.negPart (ν.map (fun z : ℝ => z - 1))
      = ∫⁻ z, ENNReal.ofReal (-(z - 1)) ∂ν :=
    lintegral_map (ENNReal.measurable_ofReal.comp measurable_neg) (measurable_id.sub_const 1)
  rw [h]
  refine lintegral_congr fun z => ?_
  congr 1
  ring

theorem posPart_map_sub_one_le (ν : Measure ℝ) :
    RWRS.posPart (ν.map (fun z : ℝ => z - 1)) ≤ RWRS.posPart ν := by
  rw [posPart_map_sub_one]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (by linarith)

theorem negPart_le_map_sub_one (ν : Measure ℝ) :
    RWRS.negPart ν ≤ RWRS.negPart (ν.map (fun z : ℝ => z - 1)) := by
  rw [negPart_map_sub_one]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (by linarith)

theorem negPart_map_sub_one_ne_top (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hn : RWRS.negPart ν ≠ ⊤) : RWRS.negPart (ν.map (fun z : ℝ => z - 1)) ≠ ⊤ := by
  have hle : RWRS.negPart (ν.map (fun z : ℝ => z - 1)) ≤ 1 + RWRS.negPart ν := by
    rw [negPart_map_sub_one]
    have hstep : ∀ z : ℝ, ENNReal.ofReal (1 - z)
        ≤ ENNReal.ofReal 1 + ENNReal.ofReal (-z) := by
      intro z
      have : (1 : ℝ) - z = 1 + -z := by ring
      rw [this]
      exact ENNReal.ofReal_add_le
    refine le_trans (lintegral_mono hstep) ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      ENNReal.ofReal_one]
    rfl
  exact ne_top_of_le_ne_top (by simp [hn]) hle

/-- **The `p`-th positive moment of the excess is at most that of the mass.** -/
theorem posMoment_map_sub_one_le (ν : Measure ℝ) {p : ℝ} (hp : 0 ≤ p) :
    RWRS.posMoment (ν.map (fun z : ℝ => z - 1)) p ≤ RWRS.posMoment ν p := by
  have h : RWRS.posMoment (ν.map (fun z : ℝ => z - 1)) p
      = ∫⁻ z, ENNReal.ofReal (max (z - 1) 0 ^ p) ∂ν :=
    lintegral_map (by fun_prop) (measurable_id.sub_const 1)
  rw [h, RWRS.posMoment]
  refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
  refine Real.rpow_le_rpow (le_max_right _ _) ?_ hp
  exact max_le_max (by linarith) le_rfl

/-- **The excess of a subcritical mass has negative mean.** -/
theorem extMean_map_sub_one_lt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : RWRS.extMean ν < 1) :
    RWRS.extMean (ν.map (fun z : ℝ => z - 1)) < 0 := by
  by_cases hn : RWRS.negPart ν = ⊤
  · have hn' : RWRS.negPart (ν.map (fun z : ℝ => z - 1)) = ⊤ :=
      top_le_iff.1 (hn ▸ negPart_le_map_sub_one ν)
    rw [RWRS.extMean, hn', EReal.coe_ennreal_top, EReal.sub_top]
    exact EReal.bot_lt_coe 0
  · have hp : RWRS.posPart ν ≠ ⊤ := by
      intro hc
      have hne : ((RWRS.negPart ν : ℝ≥0∞) : EReal) = (((RWRS.negPart ν).toReal : ℝ) : EReal) :=
        (EReal.coe_ennreal_toReal hn).symm
      rw [RWRS.extMean, hc, EReal.coe_ennreal_top, hne, EReal.top_sub_coe] at hmean
      exact absurd hmean (by simp)
    have hp' : RWRS.posPart (ν.map (fun z : ℝ => z - 1)) ≠ ⊤ :=
      ne_top_of_le_ne_top hp (posPart_map_sub_one_le ν)
    have hn'' : RWRS.negPart (ν.map (fun z : ℝ => z - 1)) ≠ ⊤ :=
      negPart_map_sub_one_ne_top ν hn
    haveI : IsProbabilityMeasure (ν.map (fun z : ℝ => z - 1)) :=
      Measure.isProbabilityMeasure_map (measurable_id.sub_const 1).aemeasurable
    have hint : Integrable (fun z : ℝ => z) ν := integrable_id_of_finite hp hn
    have hint' : Integrable (fun z : ℝ => z) (ν.map (fun z : ℝ => z - 1)) :=
      integrable_id_of_finite hp' hn''
    have hmap : ∫ z, z ∂(ν.map (fun z : ℝ => z - 1)) = ∫ z, (z - 1) ∂ν :=
      integral_map (measurable_id.sub_const 1).aemeasurable
        (by fun_prop)
    have hsub : ∫ z, (z - 1) ∂ν = (∫ z, z ∂ν) - 1 := by
      rw [integral_sub hint (integrable_const 1), integral_const]
      simp
    have hval : ∫ z, z ∂ν < 1 := by
      rw [integral_id_eq hint]
      rw [extMean_eq_coe hp hn] at hmean
      have : ((RWRS.posPart ν).toReal - (RWRS.negPart ν).toReal : ℝ) < 1 := by
        exact_mod_cast hmean
      exact this
    rw [extMean_eq_coe hp' hn'']
    have hlt : (RWRS.posPart (ν.map (fun z : ℝ => z - 1))).toReal
        - (RWRS.negPart (ν.map (fun z : ℝ => z - 1))).toReal < 0 := by
      rw [← integral_id_eq hint', hmap, hsub]
      linarith
    exact_mod_cast hlt


/-! ### The moments of the odometer -/

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

set_option linter.unusedVariables false in
/-- **The first clause of `thm:stab`(i)**: on a bounded-degree graph the `q`-th
moment of the odometer is finite, uniformly in the vertex, for
`q ∈ [1,(p-1)/2)`. -/
theorem lintegral_odometerLimit_rpow_ne_top [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] [DecidableEq V] (hG : G.Connected)
    (hVBE : RWRS.External.VonBahrEsseen) (hFNt : RWRS.External.FukNagaevTail)
    (d : ℕ) (hbd : RWRS.BoundedDegree G d) {A : ℝ}
    (hsp : RWRS.SpectralDimensionBound G 1 A)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hmean : RWRS.extMean ν < 1)
    {p q : ℝ} (hp : 3 < p) (hmom : RWRS.posMoment ν p ≠ ⊤)
    (hq1 : 1 ≤ q) (hq2 : q < (p - 1) / 2) :
    (⨆ v : V, ∫⁻ σ, RWRS.odometerLimit G σ v ^ q ∂(RWRS.iidLaw V ν)) ≠ ⊤ := by
  classical
  have hq0 : (0:ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  set ν' : Measure ℝ := ν.map (fun z : ℝ => z - 1) with hν'def
  haveI : IsProbabilityMeasure ν' :=
    Measure.isProbabilityMeasure_map (measurable_id.sub_const 1).aemeasurable
  have hmean' : RWRS.extMean ν' < 0 := extMean_map_sub_one_lt ν hmean
  have hmom' : RWRS.posMoment ν' p ≠ ⊤ :=
    ne_top_of_le_ne_top hmom (posMoment_map_sub_one_le ν (by linarith))
  have hpds : 1 + 2 / (1:ℝ) < p := by
    have h21 : (2:ℝ) / 1 = 2 := by norm_num
    rw [h21]
    linarith
  have hqθ : q < (p - 1) * min ((1:ℝ) / 2) 1 := by
    rw [min_eq_left (by norm_num)]
    linarith [hq2]
  have hbig := lintegral_supPayoff_rpow_ne_top (G := G) hG hVBE hFNt d hbd
    (by norm_num : (0:ℝ) < 1) hsp ν' hmean' hpds hmom' hq1 hqθ
  refine ne_top_of_le_ne_top hbig (iSup_le fun v => ?_)
  haveI : IsProbabilityMeasure (RWRS.walkLaw G v) := by rw [walkLaw_eq_lib]; infer_instance
  have hstep : ∀ σ : V → ℝ, RWRS.odometerLimit G σ v ^ q
      ≤ ∫⁻ X, RWRS.supPayoff G (RWRS.excess σ) X ^ q ∂(RWRS.walkLaw G v) := by
    intro σ
    have h1 : RWRS.odometerLimit G σ v = RWRS.supStopValue G (RWRS.excess σ) v :=
      RWRS.Frozen.rwInfinite hG σ v
    have h2 : RWRS.supStopValue G (RWRS.excess σ) v
        ≤ ∫⁻ X, RWRS.supPayoff G (RWRS.excess σ) X ∂(RWRS.walkLaw G v) :=
      supStopValue_le_lintegral_supPayoff hG _ v
    calc RWRS.odometerLimit G σ v ^ q
        = RWRS.supStopValue G (RWRS.excess σ) v ^ q := by rw [h1]
      _ ≤ (∫⁻ X, RWRS.supPayoff G (RWRS.excess σ) X ∂(RWRS.walkLaw G v)) ^ q :=
          ENNReal.rpow_le_rpow h2 hq0.le
      _ ≤ ∫⁻ X, RWRS.supPayoff G (RWRS.excess σ) X ^ q ∂(RWRS.walkLaw G v) :=
          lintegral_rpow_ge _ (measurable_supPayoff_prod.comp
            (measurable_const.prodMk measurable_id)).aemeasurable hq1
  refine le_trans (lintegral_mono hstep) ?_
  have hmapexc : (RWRS.iidLaw V ν).map (fun σ : V → ℝ => RWRS.excess σ) = RWRS.iidLaw V ν' :=
    iidLaw_map ν (measurable_id.sub_const 1)
  have hmeasg : Measurable fun ξ : V → ℝ =>
      ∫⁻ X, RWRS.supPayoff G ξ X ^ q ∂(RWRS.walkLaw G v) :=
    (measurable_supPayoff_rpow q).lintegral_prod_right'
  have hchain : (∫⁻ σ, ∫⁻ X, RWRS.supPayoff G (RWRS.excess σ) X ^ q ∂(RWRS.walkLaw G v)
        ∂(RWRS.iidLaw V ν))
      = ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν' v) := by
    calc (∫⁻ σ, ∫⁻ X, RWRS.supPayoff G (RWRS.excess σ) X ^ q ∂(RWRS.walkLaw G v)
          ∂(RWRS.iidLaw V ν))
        = ∫⁻ ξ, (∫⁻ X, RWRS.supPayoff G ξ X ^ q ∂(RWRS.walkLaw G v)) ∂(RWRS.iidLaw V ν') := by
          have hexcm : Measurable fun σ : V → ℝ => RWRS.excess σ :=
            measurable_pi_lambda _ fun w => (measurable_pi_apply w).sub_const 1
          rw [← hmapexc, lintegral_map hmeasg hexcm]
      _ = ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν' v) := by
          rw [RWRS.jointLaw,
            MeasureTheory.lintegral_prod _ (measurable_supPayoff_rpow q).aemeasurable]
  rw [hchain]
  exact le_iSup (fun x : V => ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν' x)) v


end RWRS.Support
