/-
The Pareto law of `sec:transient-nonstab` and `sec:recurrent-nonstab`: the law
of `U^{-1/q}` for `U` uniform on `(0,1]`.  Its tail is `P(Y ≥ t) = t^{-q}` for
`t ≥ 1`, it is supported on `[1,∞)`, and it has a finite `p`-th moment exactly
when `p < q`.
-/
import RWRS.Support.Truncation
import RWRS.Support.PipeTree
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-! ### The change of variable -/

/-- The map `u ↦ u^{-1/q}` sends `u` above `t` exactly when `u` is below
`t^{-q}`. -/
theorem pareto_le_iff {q : ℝ} (hq : 0 < q) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    t ≤ u ^ (-(1 / q)) ↔ u ≤ t ^ (-q) := by
  rw [Real.rpow_neg hu.le, Real.rpow_neg ht.le,
    le_inv_comm₀ ht (Real.rpow_pos_of_pos hu _)]
  have h1 : (u ^ (1 / q)) ^ q = u := by
    rw [one_div]; exact Real.rpow_inv_rpow hu.le hq.ne'
  have h2 : (t⁻¹) ^ q = (t ^ q)⁻¹ := Real.inv_rpow ht.le q
  calc u ^ (1 / q) ≤ t⁻¹
      ↔ (u ^ (1 / q)) ^ q ≤ (t⁻¹) ^ q :=
        (Real.rpow_le_rpow_iff (Real.rpow_nonneg hu.le _) (by positivity) hq).symm
    _ ↔ u ≤ (t ^ q)⁻¹ := by rw [h1, h2]

/-! ### The law -/

/-- The Pareto law with tail exponent `q`: the law of `U^{-1/q}` for `U`
uniform on `(0,1]`. -/
noncomputable def paretoLaw (q : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioc (0 : ℝ) 1)).map (fun u => u ^ (-(1 / q)))

theorem measurable_rpow_const (c : ℝ) : Measurable (fun u : ℝ => u ^ c) :=
  Measurable.pow_const measurable_id c

instance isProbabilityMeasure_unitInterval :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  simp

instance isProbabilityMeasure_paretoLaw (q : ℝ) : IsProbabilityMeasure (paretoLaw q) :=
  Measure.isProbabilityMeasure_map (measurable_rpow_const _).aemeasurable

theorem paretoLaw_apply {q : ℝ} {s : Set ℝ} (hs : MeasurableSet s) :
    paretoLaw q s
      = volume ((fun u : ℝ => u ^ (-(1 / q))) ⁻¹' s ∩ Set.Ioc (0 : ℝ) 1) := by
  rw [paretoLaw, Measure.map_apply (measurable_rpow_const _) hs, Measure.restrict_apply]
  exact (measurable_rpow_const _) hs

/-- **The Pareto tail.** -/
theorem isPareto_paretoLaw {q : ℝ} (hq : 0 < q) : RWRS.IsPareto (paretoLaw q) q := by
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  have htq : (0 : ℝ) < t ^ (-q) := Real.rpow_pos_of_pos ht0 _
  have htq1 : t ^ (-q) ≤ 1 := by
    rw [Real.rpow_neg ht0.le, inv_le_one₀ (Real.rpow_pos_of_pos ht0 _)]
    exact Real.one_le_rpow ht hq.le
  have hset : (fun u : ℝ => u ^ (-(1 / q))) ⁻¹' {z : ℝ | t ≤ z} ∩ Set.Ioc (0 : ℝ) 1
      = Set.Ioc (0 : ℝ) (t ^ (-q)) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Ioc]
    constructor
    · rintro ⟨hle, hu0, -⟩
      exact ⟨hu0, (pareto_le_iff hq hu0 ht0).1 hle⟩
    · rintro ⟨hu0, hule⟩
      exact ⟨(pareto_le_iff hq hu0 ht0).2 hule, hu0, le_trans hule htq1⟩
  have hms : MeasurableSet {z : ℝ | t ≤ z} := measurableSet_Ici
  rw [paretoLaw_apply hms, hset, Real.volume_Ioc, sub_zero]

/-- The Pareto law is carried by `[1,∞)`. -/
theorem ae_one_le_paretoLaw {q : ℝ} (hq : 0 < q) : ∀ᵐ z ∂(paretoLaw q), 1 ≤ z := by
  have hms : MeasurableSet {z : ℝ | 1 ≤ z} := measurableSet_Ici
  rw [paretoLaw]
  refine (ae_map_iff (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (f := fun u : ℝ => u ^ (-(1 / q))) (p := fun z : ℝ => 1 ≤ z)
    (measurable_rpow_const _).aemeasurable hms).2 ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  filter_upwards with u hu
  exact (pareto_le_iff hq hu.1 zero_lt_one).2 (by rw [Real.one_rpow]; exact hu.2)

/-! ### The moments -/

/-- **The `p`-th moment of the Pareto law is finite for `p < q`.** -/
theorem lintegral_rpow_paretoLaw_ne_top {q p : ℝ} (hq : 0 < q) (hpq : p < q) :
    (∫⁻ z, ENNReal.ofReal (z ^ p) ∂(paretoLaw q)) ≠ ⊤ := by
  set s : ℝ := -(p / q) with hsdef
  have hs : -1 < s := by
    rw [hsdef, neg_lt_neg_iff, div_lt_one hq]
    exact hpq
  have hgm : Measurable fun z : ℝ => ENNReal.ofReal (z ^ p) :=
    ENNReal.measurable_ofReal.comp (measurable_rpow_const p)
  have hchange : (∫⁻ z, ENNReal.ofReal (z ^ p) ∂(paretoLaw q))
      = ∫⁻ u, ENNReal.ofReal ((u ^ (-(1 / q))) ^ p)
          ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    rw [paretoLaw, lintegral_map hgm (measurable_rpow_const _)]
  have hpow : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ENNReal.ofReal ((u ^ (-(1 / q))) ^ p) = ENNReal.ofReal (u ^ s) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with u hu
    congr 1
    rw [← Real.rpow_mul hu.1.le, hsdef]
    congr 1
    field_simp
  have hint : IntegrableOn (fun x : ℝ => x ^ s) (Set.Ioc (0 : ℝ) 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (s := s) (t := 1) one_pos).2 hs).congr_set_ae
      Ioo_ae_eq_Ioc.symm
  have hle : (∫⁻ u, ENNReal.ofReal (u ^ s) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      ≤ ∫⁻ u, ‖u ^ s‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    lintegral_mono fun u => Real.ofReal_le_enorm _
  rw [hchange, lintegral_congr_ae hpow]
  exact ne_top_of_le_ne_top (LT.lt.ne hint.2) hle

/-! ### The mean, and the shifted law -/

/-- The extended mean of a marginal whose two halves are finite is its
integral. -/
theorem extMean_eq_integral {ν : Measure ℝ} (hp : RWRS.posPart ν ≠ ⊤)
    (hn : RWRS.negPart ν ≠ ⊤) : RWRS.extMean ν = ((∫ z, z ∂ν : ℝ) : EReal) := by
  rw [integral_id_eq (integrable_id_of_finite hp hn), RWRS.extMean,
    ← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn, ← EReal.coe_sub]

theorem negPart_paretoLaw {q : ℝ} (hq : 0 < q) : RWRS.negPart (paretoLaw q) = 0 := by
  rw [RWRS.negPart]
  refine (lintegral_eq_zero_iff' ?_).2 ?_
  · exact (ENNReal.measurable_ofReal.comp measurable_neg).aemeasurable
  · filter_upwards [ae_one_le_paretoLaw hq] with z hz
    simp only [Pi.zero_apply]
    exact ENNReal.ofReal_eq_zero.2 (by linarith)

theorem posPart_paretoLaw_ne_top {q : ℝ} (hq : 1 < q) : RWRS.posPart (paretoLaw q) ≠ ⊤ := by
  have h := lintegral_rpow_paretoLaw_ne_top (q := q) (p := 1) (by linarith) hq
  rw [RWRS.posPart]
  refine ne_of_eq_of_ne (lintegral_congr fun z => ?_) h
  rw [Real.rpow_one]

theorem integrable_id_paretoLaw {q : ℝ} (hq : 1 < q) :
    Integrable (fun z : ℝ => z) (paretoLaw q) :=
  integrable_id_of_finite (posPart_paretoLaw_ne_top hq)
    (by rw [negPart_paretoLaw (by linarith : (0:ℝ) < q)]; exact ENNReal.zero_ne_top)

/-- The Pareto law shifted so that its mean is `μ`. -/
noncomputable def shiftedParetoLaw (q μ : ℝ) : Measure ℝ :=
  (paretoLaw q).map (fun z => z + (μ - ∫ y, y ∂(paretoLaw q)))

instance isProbabilityMeasure_shiftedParetoLaw (q μ : ℝ) :
    IsProbabilityMeasure (shiftedParetoLaw q μ) :=
  Measure.isProbabilityMeasure_map (measurable_id.add_const _).aemeasurable

/-- **The shifted Pareto law is bounded from below, has mean `μ`, and has a
finite `p`-th centred moment for every `p < q`.** -/
theorem shiftedParetoLaw_spec {q μ p : ℝ} (hq : 1 < q) (hp : 0 ≤ p) (hpq : p < q) :
    (∀ᵐ z ∂(shiftedParetoLaw q μ), 1 + (μ - ∫ y, y ∂(paretoLaw q)) ≤ z) ∧
      RWRS.extMean (shiftedParetoLaw q μ) = (μ : EReal) ∧
      RWRS.centeredMoment (shiftedParetoLaw q μ) μ p ≠ ⊤ := by
  have hq0 : (0 : ℝ) < q := by linarith
  set m : ℝ := ∫ y, y ∂(paretoLaw q) with hm
  set c : ℝ := μ - m with hc
  have hmeas : Measurable (fun z : ℝ => z + c) := measurable_id.add_const _
  have hint : Integrable (fun z : ℝ => z) (paretoLaw q) := integrable_id_paretoLaw hq
  have hlow : ∀ᵐ z ∂(shiftedParetoLaw q μ), 1 + c ≤ z := by
    rw [shiftedParetoLaw, ae_map_iff hmeas.aemeasurable
      (measurableSet_Ici (a := 1 + c))]
    filter_upwards [ae_one_le_paretoLaw hq0] with y hy
    show 1 + c ≤ y + c
    linarith
  refine ⟨hlow, ?_, ?_⟩
  · have hpos : RWRS.posPart (shiftedParetoLaw q μ) ≠ ⊤ := by
      rw [RWRS.posPart, shiftedParetoLaw, lintegral_map ENNReal.measurable_ofReal hmeas]
      have hbd : ∀ y : ℝ, ENNReal.ofReal (y + c)
          ≤ ENNReal.ofReal y + ENNReal.ofReal |c| := by
        intro y
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
        exact add_le_add_left (le_abs_self c) y |>.trans_eq (by ring) |>.trans_eq' (by ring)
      refine ne_top_of_le_ne_top ?_ (lintegral_mono hbd)
      rw [lintegral_add_right _ measurable_const, lintegral_const]
      exact ENNReal.add_ne_top.2 ⟨posPart_paretoLaw_ne_top hq, by
        simp [measure_univ]⟩
    have hneg : RWRS.negPart (shiftedParetoLaw q μ) ≠ ⊤ := by
      rw [RWRS.negPart, shiftedParetoLaw]
      rw [lintegral_map (g := fun z : ℝ => z + c)
        (f := fun z : ℝ => ENNReal.ofReal (-z))
        (ENNReal.measurable_ofReal.comp measurable_neg) hmeas]
      refine ne_top_of_le_ne_top ?_
        (lintegral_mono_ae (g := fun _ : ℝ => ENNReal.ofReal |c|) ?_)
      · rw [lintegral_const]
        simp [measure_univ]
      · filter_upwards [ae_one_le_paretoLaw hq0] with y hy
        refine ENNReal.ofReal_le_ofReal ?_
        have : -c ≤ |c| := neg_le_abs c
        show -(y + c) ≤ |c|
        linarith
    rw [extMean_eq_integral hpos hneg, shiftedParetoLaw,
      integral_map hmeas.aemeasurable (by fun_prop)]
    have : ∫ y, (y + c) ∂(paretoLaw q) = m + c := by
      rw [integral_add hint (integrable_const _), integral_const]
      simp [hm]
    rw [this, hc]
    norm_num
  · have hmom := lintegral_rpow_paretoLaw_ne_top (q := q) (p := p) hq0 hpq
    rw [RWRS.centeredMoment, shiftedParetoLaw,
      lintegral_map (g := fun z : ℝ => z + c)
        (f := fun z : ℝ => ENNReal.ofReal (|z - μ| ^ p))
        (ENNReal.measurable_ofReal.comp
          ((continuous_abs.measurable.comp (measurable_id.sub_const μ)).pow_const p)) hmeas]
    have hcst : (0 : ℝ) ≤ (1 + |m|) ^ p := by positivity
    refine ne_top_of_le_ne_top ?_
      (lintegral_mono_ae (g := fun y : ℝ =>
        ENNReal.ofReal ((1 + |m|) ^ p) * ENNReal.ofReal (y ^ p)) ?_)
    · have hsplit : (∫⁻ a, ENNReal.ofReal ((1 + |m|) ^ p) * ENNReal.ofReal (a ^ p)
            ∂(paretoLaw q))
          = ENNReal.ofReal ((1 + |m|) ^ p) * ∫⁻ a, ENNReal.ofReal (a ^ p) ∂(paretoLaw q) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      rw [hsplit]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmom
    · filter_upwards [ae_one_le_paretoLaw hq0] with y hy
      have hy0 : (0 : ℝ) < y := by linarith
      have habs : |y + c - μ| ≤ (1 + |m|) * y := by
        have h1 : y + c - μ = y - m := by rw [hc]; ring
        rw [h1]
        have : |y - m| ≤ y + |m| := by
          calc |y - m| ≤ |y| + |m| := abs_sub _ _
            _ = y + |m| := by rw [abs_of_pos hy0]
        nlinarith [abs_nonneg m]
      rw [← ENNReal.ofReal_mul hcst, ← Real.mul_rpow (by positivity) hy0.le]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg _) habs hp)

end RWRS.Support
