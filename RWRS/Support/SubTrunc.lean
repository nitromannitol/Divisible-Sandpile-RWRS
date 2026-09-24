/-
The reduction that opens the proof of `prop:subcritical`: replacing `ξ(v)` by
`max(ξ(v), -M)`.

The paper begins "Replacing `ξ(v)` by `max(ξ(v),-M)` increases `ζ` pointwise,
hence increases `S_n` pathwise and gives `E[|ξ|^p] < ∞`.  Since
`E[max(ξ,-M)] ↓ E[ξ] < 0`, for large `M` the truncated mean is still negative.
We may therefore assume `E[ξ] > -∞` and `E[|ξ|^p] < ∞`."  Here that is four
statements: the payoff is monotone in the scenery, so the two suprema of the
optimal stopping problem are; the image of an i.i.d. field under a coordinate
map is the i.i.d. field of the image marginal, so the comparison is a
comparison of integrals against the two joint laws; the truncated marginal
keeps the positive part and has a finite negative part, and its negative part
increases to that of `ν`, so some level makes the mean a negative real; and the
`p`-th absolute moment of the truncated marginal is finite as soon as the
`p`-th moment of the positive part of `ν` is.
-/
import RWRS.Support.DyadicSup
import RWRS.Support.Explosion
import RWRS.Support.VoltageIdentity

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-! ### The one-sided truncation of the marginal -/

/-- The one-sided truncation `max(z,-M)` of the reduction of `prop:subcritical`. -/
noncomputable def lowTrunc (M z : ℝ) : ℝ := max z (-M)

theorem measurable_lowTrunc (M : ℝ) : Measurable (lowTrunc M) := by
  unfold lowTrunc
  fun_prop

theorem le_lowTrunc (M z : ℝ) : z ≤ lowTrunc M z := le_max_left _ _

/-- The truncation does not change the positive part. -/
theorem ofReal_lowTrunc {M : ℝ} (hM : 0 ≤ M) (z : ℝ) :
    ENNReal.ofReal (lowTrunc M z) = ENNReal.ofReal z := by
  unfold lowTrunc
  rcases le_or_gt 0 z with hz | hz
  · rw [max_eq_left (by linarith : -M ≤ z)]
  · rw [ENNReal.ofReal_eq_zero.mpr (by linarith : z ≤ 0),
      ENNReal.ofReal_eq_zero.mpr (max_le (by linarith : z ≤ 0) (by linarith : -M ≤ 0))]

theorem neg_lowTrunc (M z : ℝ) : -(lowTrunc M z) = min (-z) M := by
  unfold lowTrunc
  rw [show max z (-M) = z ⊔ (-M) from rfl, neg_sup, neg_neg,
    show (-z) ⊓ M = min (-z) M from rfl]

theorem abs_lowTrunc_le {M : ℝ} (hM : 0 ≤ M) (z : ℝ) : |lowTrunc M z| ≤ max z 0 + M := by
  unfold lowTrunc
  have h1 : (0:ℝ) ≤ max z 0 := le_max_right z 0
  have h2 : z ≤ max z 0 := le_max_left z 0
  rcases le_or_gt 0 z with hz | hz
  · rw [max_eq_left (by linarith : -M ≤ z), abs_of_nonneg hz]
    linarith
  · rw [abs_le]
    refine ⟨?_, ?_⟩
    · have : -M ≤ max z (-M) := le_max_right z (-M)
      linarith
    · have : max z (-M) ≤ 0 := max_le (by linarith) (by linarith)
      linarith

theorem posPart_map_lowTrunc (ν : Measure ℝ) {M : ℝ} (hM : 0 ≤ M) :
    RWRS.posPart (ν.map (lowTrunc M)) = RWRS.posPart ν := by
  unfold RWRS.posPart
  rw [lintegral_map ENNReal.measurable_ofReal (measurable_lowTrunc M)]
  exact lintegral_congr fun z => ofReal_lowTrunc hM z

theorem negPart_map_lowTrunc_eq (ν : Measure ℝ) (M : ℝ) :
    RWRS.negPart (ν.map (lowTrunc M)) = ∫⁻ z, ENNReal.ofReal (min (-z) M) ∂ν := by
  unfold RWRS.negPart
  rw [lintegral_map (by fun_prop) (measurable_lowTrunc M)]
  exact lintegral_congr fun z => by rw [neg_lowTrunc]

theorem negPart_map_lowTrunc_ne_top (ν : Measure ℝ) [IsProbabilityMeasure ν] (M : ℝ) :
    RWRS.negPart (ν.map (lowTrunc M)) ≠ ⊤ := by
  rw [negPart_map_lowTrunc_eq]
  refine ne_top_of_le_ne_top ?_
    (lintegral_mono fun z => ENNReal.ofReal_le_ofReal (min_le_right _ _))
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_ne_top

theorem iSup_ofReal_min (z : ℝ) :
    (⨆ k : ℕ, ENNReal.ofReal (min (-z) (k : ℝ))) = ENNReal.ofReal (-z) := by
  refine le_antisymm (iSup_le fun k => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  refine le_iSup_of_le ⌈(-z)⌉₊ ?_
  rw [min_eq_left (Nat.le_ceil (-z))]

/-- The negative part of the truncated marginal increases to that of `ν`. -/
theorem iSup_negPart_map_lowTrunc (ν : Measure ℝ) :
    (⨆ k : ℕ, RWRS.negPart (ν.map (lowTrunc (k : ℝ)))) = RWRS.negPart ν := by
  have hmono : Monotone fun k : ℕ => fun z : ℝ => ENNReal.ofReal (min (-z) (k : ℝ)) := by
    intro a b hab
    refine fun z => ENNReal.ofReal_le_ofReal (min_le_min le_rfl ?_)
    exact_mod_cast hab
  calc (⨆ k : ℕ, RWRS.negPart (ν.map (lowTrunc (k : ℝ))))
      = ⨆ k : ℕ, ∫⁻ z, ENNReal.ofReal (min (-z) (k : ℝ)) ∂ν := by
        exact iSup_congr fun k => negPart_map_lowTrunc_eq ν (k : ℝ)
    _ = ∫⁻ z, ⨆ k : ℕ, ENNReal.ofReal (min (-z) (k : ℝ)) ∂ν :=
        (lintegral_iSup (fun k => by fun_prop) hmono).symm
    _ = RWRS.negPart ν := lintegral_congr fun z => iSup_ofReal_min z

/-! ### The moments of the truncated marginal -/

/-- A finite `p`-th moment of the positive part makes the positive part
integrable, for `p ≥ 1`. -/
theorem posPart_ne_top_of_posMoment (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ}
    (hp : 1 ≤ p) (hmom : RWRS.posMoment ν p ≠ ⊤) : RWRS.posPart ν ≠ ⊤ := by
  unfold RWRS.posPart
  unfold RWRS.posMoment at hmom
  have hpt : ∀ z : ℝ, ENNReal.ofReal z ≤ 1 + ENNReal.ofReal (max z 0 ^ p) := by
    intro z
    have hnn : (0:ℝ) ≤ max z 0 ^ p := Real.rpow_nonneg (le_max_right z 0) p
    have hreal : z ≤ 1 + max z 0 ^ p := by
      rcases le_or_gt z 1 with hz | hz
      · linarith
      · have hz0 : max z 0 = z := max_eq_left (by linarith)
        have hmono : z ^ (1:ℝ) ≤ z ^ p := Real.rpow_le_rpow_of_exponent_le (by linarith) hp
        rw [Real.rpow_one] at hmono
        rw [hz0]
        linarith
    calc ENNReal.ofReal z ≤ ENNReal.ofReal (1 + max z 0 ^ p) := ENNReal.ofReal_le_ofReal hreal
      _ = 1 + ENNReal.ofReal (max z 0 ^ p) := by
          rw [ENNReal.ofReal_add zero_le_one hnn, ENNReal.ofReal_one]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_add_left measurable_const]
  refine ENNReal.add_ne_top.mpr ⟨?_, hmom⟩
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.one_ne_top

theorem abs_lowTrunc_rpow_le {M p : ℝ} (hM : 0 ≤ M) (hp : 0 ≤ p) (z : ℝ) :
    |lowTrunc M z| ^ p ≤ 2 ^ p * (max z 0 ^ p + M ^ p) := by
  have h0 : (0:ℝ) ≤ max z 0 := le_max_right z 0
  have habs : (0:ℝ) ≤ |lowTrunc M z| := abs_nonneg _
  have h1 : |lowTrunc M z| ^ p ≤ (max z 0 + M) ^ p :=
    Real.rpow_le_rpow habs (abs_lowTrunc_le hM z) hp
  have h2 : (max z 0 + M) ^ p ≤ (2 * max (max z 0) M) ^ p := by
    refine Real.rpow_le_rpow (by linarith) ?_ hp
    rcases le_total (max z 0) M with hc | hc
    · rw [max_eq_right hc]; linarith
    · rw [max_eq_left hc]; linarith
  have h3 : (2 * max (max z 0) M) ^ p = 2 ^ p * (max (max z 0) M) ^ p :=
    Real.mul_rpow (by norm_num) (le_trans h0 (le_max_left _ _))
  have h4 : (max (max z 0) M) ^ p ≤ max z 0 ^ p + M ^ p := by
    rcases le_total (max z 0) M with hc | hc
    · rw [max_eq_right hc]
      have : (0:ℝ) ≤ max z 0 ^ p := Real.rpow_nonneg h0 p
      linarith
    · rw [max_eq_left hc]
      have : (0:ℝ) ≤ M ^ p := Real.rpow_nonneg hM p
      linarith
  have h5 : (0:ℝ) ≤ (2:ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
  calc |lowTrunc M z| ^ p ≤ (2 * max (max z 0) M) ^ p := le_trans h1 h2
    _ = 2 ^ p * (max (max z 0) M) ^ p := h3
    _ ≤ 2 ^ p * (max z 0 ^ p + M ^ p) := mul_le_mul_of_nonneg_left h4 h5

/-- The truncated marginal has a finite `p`-th absolute moment. -/
theorem absMoment_map_lowTrunc_ne_top (ν : Measure ℝ) [IsProbabilityMeasure ν] {M p : ℝ}
    (hM : 0 ≤ M) (hp : 0 ≤ p) (hmom : RWRS.posMoment ν p ≠ ⊤) :
    RWRS.absMoment (ν.map (lowTrunc M)) p ≠ ⊤ := by
  unfold RWRS.absMoment
  rw [lintegral_map (by fun_prop) (measurable_lowTrunc M)]
  have hpt : ∀ z : ℝ, ENNReal.ofReal (|lowTrunc M z| ^ p)
      ≤ ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (max z 0 ^ p) + ENNReal.ofReal (M ^ p)) := by
    intro z
    calc ENNReal.ofReal (|lowTrunc M z| ^ p)
        ≤ ENNReal.ofReal (2 ^ p * (max z 0 ^ p + M ^ p)) :=
          ENNReal.ofReal_le_ofReal (abs_lowTrunc_rpow_le hM hp z)
      _ = ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (max z 0 ^ p) + ENNReal.ofReal (M ^ p)) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) p),
            ENNReal.ofReal_add (Real.rpow_nonneg (le_max_right z 0) p) (Real.rpow_nonneg hM p)]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
  rw [lintegral_const_mul _ (by fun_prop), lintegral_add_right _ measurable_const,
    lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨hmom, ENNReal.ofReal_ne_top⟩)

/-! ### A truncation level with a negative mean -/

theorem extMean_eq_coe {ρ : Measure ℝ} (hp : RWRS.posPart ρ ≠ ⊤) (hn : RWRS.negPart ρ ≠ ⊤) :
    RWRS.extMean ρ = (((RWRS.posPart ρ).toReal - (RWRS.negPart ρ).toReal : ℝ) : EReal) := by
  have hpe : (((RWRS.posPart ρ).toReal : ℝ) : EReal) = (RWRS.posPart ρ : EReal) :=
    EReal.coe_ennreal_toReal hp
  have hne : (((RWRS.negPart ρ).toReal : ℝ) : EReal) = (RWRS.negPart ρ : EReal) :=
    EReal.coe_ennreal_toReal hn
  rw [RWRS.extMean, ← hpe, ← hne, ← EReal.coe_sub]

theorem posPart_lt_negPart (ν : Measure ℝ) (hp : RWRS.posPart ν ≠ ⊤)
    (hmean : RWRS.extMean ν < 0) : RWRS.posPart ν < RWRS.negPart ν := by
  by_contra hcon
  rw [not_lt] at hcon
  have hn : RWRS.negPart ν ≠ ⊤ := ne_top_of_le_ne_top hp hcon
  rw [extMean_eq_coe hp hn] at hmean
  have h0 : (RWRS.posPart ν).toReal - (RWRS.negPart ν).toReal < 0 := by
    exact_mod_cast hmean
  have h1 : (RWRS.negPart ν).toReal ≤ (RWRS.posPart ν).toReal :=
    ENNReal.toReal_le_toReal hn hp |>.mpr hcon
  linarith

/-- **A truncation level that keeps the mean negative and makes every moment
finite.** -/
theorem exists_lowTrunc (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ} (hp : 1 ≤ p)
    (hmom : RWRS.posMoment ν p ≠ ⊤) (hmean : RWRS.extMean ν < 0) :
    ∃ M : ℝ, 0 ≤ M ∧ RWRS.absMoment (ν.map (lowTrunc M)) p ≠ ⊤ ∧
      ∃ m : ℝ, RWRS.extMean (ν.map (lowTrunc M)) = (m : EReal) ∧ m < 0 := by
  have hpos : RWRS.posPart ν ≠ ⊤ := posPart_ne_top_of_posMoment ν hp hmom
  have hlt : RWRS.posPart ν < RWRS.negPart ν := posPart_lt_negPart ν hpos hmean
  rw [← iSup_negPart_map_lowTrunc ν] at hlt
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
  have hM : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine ⟨(k : ℝ), hM, absMoment_map_lowTrunc_ne_top ν hM (by linarith) hmom, ?_⟩
  have hp' : RWRS.posPart (ν.map (lowTrunc (k : ℝ))) ≠ ⊤ := by
    rw [posPart_map_lowTrunc ν hM]; exact hpos
  have hn' : RWRS.negPart (ν.map (lowTrunc (k : ℝ))) ≠ ⊤ := negPart_map_lowTrunc_ne_top ν _
  refine ⟨(RWRS.posPart (ν.map (lowTrunc (k : ℝ)))).toReal
      - (RWRS.negPart (ν.map (lowTrunc (k : ℝ)))).toReal, extMean_eq_coe hp' hn', ?_⟩
  have h1 : (RWRS.posPart (ν.map (lowTrunc (k : ℝ)))).toReal
      < (RWRS.negPart (ν.map (lowTrunc (k : ℝ)))).toReal := by
    refine (ENNReal.toReal_lt_toReal hp' hn').mpr ?_
    rw [posPart_map_lowTrunc ν hM]
    exact hk
  linarith

/-! ### The payoff is monotone in the scenery -/

section Mono

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The payoff at a deterministic time is monotone in the scenery. -/
theorem payoff_mono_scenery {ξ ξ' : V → ℝ} (h : ∀ v, ξ v ≤ ξ' v) (n : ℕ) (X : ℕ → V) :
    RWRS.payoff G ξ n X ≤ RWRS.payoff G ξ' n X := by
  unfold RWRS.payoff
  refine Finset.sum_le_sum fun k _ => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (h (X k)) (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- `sup_n S_n` is monotone in the scenery. -/
theorem supPayoff_mono {ξ ξ' : V → ℝ} (h : ∀ v, ξ v ≤ ξ' v) (X : ℕ → V) :
    RWRS.supPayoff G ξ X ≤ RWRS.supPayoff G ξ' X :=
  iSup_mono fun n => ENNReal.ofReal_le_ofReal (payoff_mono_scenery h n X)

section Meas

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

theorem measurable_payoff_prod (n : ℕ) :
    Measurable fun z : (V → ℝ) × (ℕ → V) => RWRS.payoff G z.1 n z.2 := by
  unfold RWRS.payoff
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_scenery_at k).div (measurable_degree_at k)

theorem measurable_supPayoff_prod :
    Measurable fun z : (V → ℝ) × (ℕ → V) => RWRS.supPayoff G z.1 z.2 := by
  unfold RWRS.supPayoff
  exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp (measurable_payoff_prod n)

theorem measurable_supPayoff_rpow (q : ℝ) :
    Measurable fun z : (V → ℝ) × (ℕ → V) => RWRS.supPayoff G z.1 z.2 ^ q :=
  measurable_supPayoff_prod.pow_const q

end Meas

variable [MeasurableSpace V]

/-- The joint law of the truncated scenery with the walk is the image of the
joint law under the truncation of the scenery. -/
theorem jointLaw_map_lowTrunc [MeasurableSingletonClass V] [Countable V]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (M : ℝ) (x : V) :
    RWRS.jointLaw G (ν.map (lowTrunc M)) x
      = (RWRS.jointLaw G ν x).map (Prod.map (fun (ξ : V → ℝ) v => lowTrunc M (ξ v)) id) := by
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by rw [walkLaw_eq_lib]; infer_instance
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have hT : Measurable fun (ξ : V → ℝ) v => lowTrunc M (ξ v) :=
    measurable_pi_lambda _ fun v => (measurable_lowTrunc M).comp (measurable_pi_apply v)
  calc RWRS.jointLaw G (ν.map (lowTrunc M)) x
      = ((RWRS.iidLaw V ν).map (fun (ξ : V → ℝ) v => lowTrunc M (ξ v))).prod
          (RWRS.walkLaw G x) := by
        rw [RWRS.jointLaw, iidLaw_map ν (measurable_lowTrunc M)]
    _ = ((RWRS.iidLaw V ν).map (fun (ξ : V → ℝ) v => lowTrunc M (ξ v))).prod
          ((RWRS.walkLaw G x).map id) := by rw [Measure.map_id]
    _ = ((RWRS.iidLaw V ν).prod (RWRS.walkLaw G x)).map
          (Prod.map (fun (ξ : V → ℝ) v => lowTrunc M (ξ v)) id) :=
        Measure.map_prod_map _ _ hT measurable_id
    _ = (RWRS.jointLaw G ν x).map
          (Prod.map (fun (ξ : V → ℝ) v => lowTrunc M (ξ v)) id) := rfl

/-- **The reduction of `prop:subcritical`**: raising the scenery to its
truncation raises every moment of `sup_n S_n`. -/
theorem lintegral_supPayoff_rpow_le_lowTrunc [MeasurableSingletonClass V] [Countable V]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {M q : ℝ} (hq : 0 ≤ q) (x : V) :
    (∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x))
      ≤ ∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G (ν.map (lowTrunc M)) x) := by
  have hT : Measurable fun (ξ : V → ℝ) v => lowTrunc M (ξ v) :=
    measurable_pi_lambda _ fun v => (measurable_lowTrunc M).comp (measurable_pi_apply v)
  rw [jointLaw_map_lowTrunc ν M x,
    lintegral_map (measurable_supPayoff_rpow q) (hT.prodMap measurable_id)]
  exact lintegral_mono fun z =>
    ENNReal.rpow_le_rpow (supPayoff_mono (fun v => le_lowTrunc M (z.1 v)) z.2) hq

end Mono

end RWRS.Support
