/-
The dyadic decomposition of the running supremum of the recentred field, and the
comparison with the scenery on the scenery event.

`rwrs.tex:1304`: `Z ≤ ∑_{k≥0} Y_k`, which is `lem:dyadic` along one trajectory,
applied here to the recentred field.  The recentred field dominates the scenery
wherever the scenery is below the levels, so the running supremum of the payoff
of the scenery is dominated there by that of the recentred field, and the
almost sure finiteness of the latter transfers to the scenery event.
-/
import RWRS.Support.SubPolyMoment
import RWRS.Support.Convexity

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ρ : Measure ℝ}

/-- **The recentred field dominates the payoff of the scenery on the scenery
event.** -/
theorem supPayoff_le_zetaField [Infinite V] {M m : ℝ} {t : V → ℝ}
    (hc : ∀ v : V, siteMean ρ M (t v) ≤ m) {ξ : V → ℝ} (hξ : ∀ v, ξ v ≤ t v) (X : ℕ → V) :
    RWRS.supPayoff G ξ X ≤ RWRS.supPayoff G (zetaField ρ M m t ξ) X :=
  supPayoff_mono (fun v => le_zetaField hc hξ v) X

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **The dyadic decomposition of the running supremum of the recentred
field.** -/
theorem lintegral_supPayoff_zetaField_le [Infinite V] (hG : G.Connected) {d : ℕ}
    (hbd : RWRS.BoundedDegree G d) {M m : ℝ} (hm : m < 0) (t : V → ℝ) (o : V) :
    (∫⁻ z, RWRS.supPayoff G (zetaField ρ M m t z.1) z.2 ∂(RWRS.jointLaw G ρ o))
      ≤ ∑' k : ℕ, ∫⁻ z, ENNReal.ofReal (RWRS.dyadicY G (zetaField ρ M m t z.1) m d k z.2)
          ∂(RWRS.jointLaw G ρ o) := by
  have hpt : ∀ z : (V → ℝ) × (ℕ → V),
      RWRS.supPayoff G (zetaField ρ M m t z.1) z.2
        ≤ ∑' k : ℕ, ENNReal.ofReal (RWRS.dyadicY G (zetaField ρ M m t z.1) m d k z.2) := by
    intro z
    have h := supPayoff_rpow_le hG hbd (zetaField ρ M m t z.1) hm (q := (1:ℝ)) one_pos z.2
    rw [ENNReal.rpow_one] at h
    refine le_trans h (le_of_eq ?_)
    refine tsum_congr fun k => ?_
    rw [Real.rpow_one]
  refine le_trans (lintegral_mono hpt) (le_of_eq ?_)
  exact lintegral_tsum fun k =>
    (measurable_dyadicY_zetaField (G := G) ρ M m t d k).ennreal_ofReal.aemeasurable

/-- The joint integral is the scenery average of the walk average. -/
theorem lintegral_jointLaw_eq (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (o : V)
    {F : (V → ℝ) × (ℕ → V) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂(RWRS.jointLaw G ρ o))
      = ∫⁻ ξ, (∫⁻ X, F (ξ, X) ∂(RWRS.walkLaw G o)) ∂(RWRS.iidLaw V ρ) := by
  haveI : IsProbabilityMeasure (RWRS.walkLaw G o) := by rw [walkLaw_eq_lib]; infer_instance
  rw [RWRS.jointLaw]
  exact MeasureTheory.lintegral_prod _ hF.aemeasurable

/-- **The value of the scenery is almost surely finite on the scenery event.**
If the recentred field has a finite joint mean running supremum, then the value
of the optimal bounded rule is finite for almost every scenery below the
levels. -/
theorem ae_supStopValue_ne_top_of_lintegral [Infinite V] [IsProbabilityMeasure ρ]
    (hG : G.Connected) {M m : ℝ} {t : V → ℝ} (hc : ∀ v : V, siteMean ρ M (t v) ≤ m) (o : V)
    (hfin : (∫⁻ z, RWRS.supPayoff G (zetaField ρ M m t z.1) z.2
        ∂(RWRS.jointLaw G ρ o)) ≠ ⊤) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), (∀ v : V, ξ v ≤ t v) → RWRS.supStopValue G ξ o ≠ ⊤ := by
  haveI : IsProbabilityMeasure (RWRS.walkLaw G o) := by rw [walkLaw_eq_lib]; infer_instance
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ρ) := instIsProbabilityMeasureIid ρ
  have hmeas : Measurable fun z : (V → ℝ) × (ℕ → V) =>
      RWRS.supPayoff G (zetaField ρ M m t z.1) z.2 := by
    have h := (measurable_supPayoff_prod (G := G)).comp (measurable_zetaField_prod ρ M m t)
    simpa [Function.comp_def] using h
  have hswap := lintegral_jointLaw_eq (G := G) ρ o hmeas
  rw [hswap] at hfin
  have hmeasg : Measurable fun ξ : V → ℝ =>
      ∫⁻ X, RWRS.supPayoff G (zetaField ρ M m t ξ) X ∂(RWRS.walkLaw G o) := by
    have h := hmeas.lintegral_prod_right' (ν := RWRS.walkLaw G o)
    exact h
  have h4 := ae_lt_top hmeasg hfin
  filter_upwards [h4] with ξ hξ
  intro hle
  have h1 : RWRS.supStopValue G ξ o ≤ ∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o) :=
    supStopValue_le_lintegral_supPayoff hG ξ o
  have h2 : (∫⁻ X, RWRS.supPayoff G ξ X ∂(RWRS.walkLaw G o))
      ≤ ∫⁻ X, RWRS.supPayoff G (zetaField ρ M m t ξ) X ∂(RWRS.walkLaw G o) :=
    lintegral_mono fun X => supPayoff_le_zetaField hc hle X
  exact ne_of_lt (lt_of_le_of_lt (le_trans h1 h2) hξ)

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- **The reduction of `thm:stab`(ii) to `prop:poly-growth`.**  If the value of
the optimal bounded rule for the excess is almost surely finite at every vertex,
the configuration stabilizes almost surely. -/
theorem measure_stabilizes_eq_one_of_ae_supStopValue [Infinite V] (hG : G.Connected)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : ∀ v : V, ∀ᵐ ξ ∂(RWRS.iidLaw V (ν.map (fun z : ℝ => z - 1))),
      RWRS.supStopValue G ξ v ≠ ⊤) :
    RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1 := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have hexcm : Measurable fun σ : V → ℝ => RWRS.excess σ :=
    measurable_pi_lambda _ fun w => (measurable_pi_apply w).sub_const 1
  have hmapexc : (RWRS.iidLaw V ν).map (fun σ : V → ℝ => RWRS.excess σ)
      = RWRS.iidLaw V (ν.map (fun z : ℝ => z - 1)) :=
    iidLaw_map ν (measurable_id.sub_const 1)
  have hstep : ∀ v : V, ∀ᵐ σ ∂(RWRS.iidLaw V ν), RWRS.odometerLimit G σ v ≠ ⊤ := by
    intro v
    have hset : MeasurableSet {ξ : V → ℝ | RWRS.supStopValue G ξ v ≠ ⊤} :=
      (measurableSet_supStopValue_top hG v).compl
    have hpull : ∀ᵐ σ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G (RWRS.excess σ) v ≠ ⊤ := by
      refine (MeasureTheory.ae_map_iff hexcm.aemeasurable hset).1 ?_
      rw [hmapexc]
      exact h v
    filter_upwards [hpull] with σ hσ
    rw [RWRS.Frozen.rwInfinite hG σ v]
    exact hσ
  have hmeas : MeasurableSet {σ : V → ℝ | RWRS.Stabilizes G σ} := measurableSet_stabilizes hG
  have hae : ∀ᵐ σ ∂(RWRS.iidLaw V ν), RWRS.Stabilizes G σ :=
    (MeasureTheory.ae_all_iff).2 hstep
  have hz : RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ}ᶜ = 0 :=
    MeasureTheory.ae_iff.1 hae
  have hcompl : RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ}ᶜ
      = 1 - RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} := by
    rw [MeasureTheory.measure_compl hmeas (measure_ne_top _ _), measure_univ]
  rw [hcompl] at hz
  exact le_antisymm prob_le_one (tsub_eq_zero_iff_le.1 hz)

end RWRS.Support
