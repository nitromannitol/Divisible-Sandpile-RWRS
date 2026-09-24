/-
The subcritical half of `thm:stationary-phase`.

If the sandpile almost surely does not stabilize then the mean mark is at least
one (`rwrs.tex:363-366`).  Non-stabilization makes the odometer infinite
everywhere, so the mass at the root is eventually at least one; the increments
`Y_k = (σ_k(ρ) - σ(ρ) ∧ 1)/deg(ρ)` are non-negative, conservation makes their
mean `(E[σ] - E[σ ∧ 1]) E[1/deg(ρ)]` at every round, and Fatou's lemma against
the eventual bound `Y_k ≥ (1 - σ(ρ) ∧ 1)/deg(ρ)` gives
`(1 - E[σ ∧ 1]) E[1/deg(ρ)] ≤ (E[σ] - E[σ ∧ 1]) E[1/deg(ρ)]`, where the mean
reciprocal degree is positive.
-/
import RWRS.Support.ErgSuperFinal
import RWRS.Support.ErgProp
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace RWRS.Support

theorem min_one_le_config {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {σ : V → ℝ}
    (k : ℕ) (v : V) : min (σ v) 1 ≤ RWRS.config G σ k v := by
  induction k generalizing v with
  | zero => exact min_le_left _ _
  | succ k ih =>
    rw [config_succ, RWRS.topple]
    have hstep : min (σ v) 1 ≤ min (RWRS.config G σ k v) 1 :=
      le_min (ih v) (min_le_right _ _)
    have hsum : 0 ≤ ∑ w ∈ G.neighborFinset v, RWRS.emission G (RWRS.config G σ k) w :=
      Finset.sum_nonneg fun w _ => emission_nonneg _ w
    linarith

theorem netWeightedMassAt_eq_mul (N : RWRS.Net 1) (k : ℕ) :
    RWRS.netWeightedMassAt N k
      = RWRS.config (RWRS.netGraph N) (RWRS.netConfig N) k (RWRS.netRoot N)
          * degWeight (RWRS.forgetMarks N) := by
  rw [RWRS.netWeightedMassAt, degWeight, div_eq_mul_inv]
  rfl

/-- The subcritical estimate: if the sandpile almost surely does not stabilize
then the mean mark is at least one (`rwrs.tex:363-366`). -/
theorem one_le_integral_id_of_ae_not_stabilizes
    (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun N => |RWRS.netWeightedMass N|) (RWRS.markIid Q ν))
    (hns : ∀ᵐ N ∂(RWRS.markIid Q ν),
      ¬ RWRS.Stabilizes (RWRS.netGraph N) (RWRS.netConfig N)) :
    1 ≤ ∫ z, z ∂ν := by
  haveI hP : IsProbabilityMeasure (RWRS.markIid Q ν) := isProbabilityMeasure_markIid Q ν
  have hgoodP : ∀ᵐ N ∂(RWRS.markIid Q ν), RWRS.NetGood N := ae_netGood_markIid Q ν hgood
  have hstatP : RWRS.IsStationaryNet (RWRS.markIid Q ν) :=
    RWRS.Frozen.iidStationary Q inferInstance ν inferInstance hstat
  have hν1 : Integrable (fun z : ℝ => z) ν :=
    integrable_id_of_integrable_netWeightedMass Q hgood ν hint
  set c : ℝ := ∫ N, degWeight N ∂Q with hc
  have hcpos : 0 < c := integral_degWeight_pos Q hgood
  -- the truncation of the mark at one
  have hmin1 : Measurable fun z : ℝ => min z 1 := measurable_id.min measurable_const
  have hminint : Integrable (fun z : ℝ => min z 1) ν := by
    refine (hν1.abs.add (integrable_const (1 : ℝ))).mono' hmin1.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs]
    rcases le_total z 1 with h | h
    · rw [min_eq_left h]; simp
    · rw [min_eq_right h]; simp
  set m1 : ℝ := ∫ z, min z 1 ∂ν with hm1
  set W : RWRS.Net 1 → ℝ := fun N =>
    min (RWRS.netConfig N (RWRS.netRoot N)) 1 * degWeight (RWRS.forgetMarks N) with hW
  have hWmeas : Measurable W :=
    ((hmin1.comp measurable_netConfig_root).mul (measurable_degWeight.comp measurable_forgetMarks))
  have hWint : Integrable W (RWRS.markIid Q ν) :=
    integrable_markIid_mark_mul Q ν hmin1 measurable_degWeight hminint (integrable_degWeight Q)
  have hWval : ∫ N, W N ∂(RWRS.markIid Q ν) = m1 * c :=
    integral_markIid_mark_mul Q ν hmin1 measurable_degWeight hminint (integrable_degWeight Q)
  -- the nonnegative increments
  set Y : ℕ → RWRS.Net 1 → ℝ := fun k N => RWRS.netWeightedMassAt N k - W N with hY
  have hYnn : ∀ k N, 0 ≤ Y k N := by
    intro k N
    show 0 ≤ RWRS.netWeightedMassAt N k
      - min (RWRS.netConfig N (RWRS.netRoot N)) 1 * degWeight (RWRS.forgetMarks N)
    rw [netWeightedMassAt_eq_mul, sub_nonneg]
    exact mul_le_mul_of_nonneg_right (min_one_le_config k (RWRS.netRoot N))
      (degWeight_nonneg _)
  have hYmeas : ∀ k, Measurable (Y k) := fun k => (measurable_netWeightedMassAt k).sub hWmeas
  have hYint : ∀ k, Integrable (Y k) (RWRS.markIid Q ν) := fun k =>
    ((RWRS.Frozen.stationaryToppling (RWRS.markIid Q ν) hP hgoodP hstatP hint k).2.1).sub hWint
  have hYval : ∀ k, ∫ N, Y k N ∂(RWRS.markIid Q ν) = (∫ z, z ∂ν) * c - m1 * c := by
    intro k
    rw [hY, integral_sub
      ((RWRS.Frozen.stationaryToppling (RWRS.markIid Q ν) hP hgoodP hstatP hint k).2.1) hWint,
      (RWRS.Frozen.stationaryToppling (RWRS.markIid Q ν) hP hgoodP hstatP hint k).2.2,
      integral_netWeightedMass_markIid Q ν hν1, hWval]
  -- the limiting lower bound
  set Z : RWRS.Net 1 → ℝ := fun N =>
    (1 - min (RWRS.netConfig N (RWRS.netRoot N)) 1) * degWeight (RWRS.forgetMarks N) with hZ
  have hZnn : ∀ N, 0 ≤ Z N := by
    intro N
    exact mul_nonneg (by simp [sub_nonneg]) (degWeight_nonneg _)
  have hZmeas : Measurable Z :=
    ((measurable_const.sub (hmin1.comp measurable_netConfig_root)).mul
      (measurable_degWeight.comp measurable_forgetMarks))
  have hZint : Integrable Z (RWRS.markIid Q ν) := by
    have := integrable_markIid_mark_mul Q ν (f := fun z : ℝ => 1 - min z 1)
      (measurable_const.sub hmin1) measurable_degWeight
      ((integrable_const (1 : ℝ)).sub hminint) (integrable_degWeight Q)
    exact this
  have hZval : ∫ N, Z N ∂(RWRS.markIid Q ν) = (1 - m1) * c := by
    have hfac := integral_markIid_mark_mul Q ν (f := fun z : ℝ => 1 - min z 1)
      (measurable_const.sub hmin1) measurable_degWeight
      ((integrable_const (1 : ℝ)).sub hminint) (integrable_degWeight Q)
    have h2 : ∫ z : ℝ, (1 - min z 1) ∂ν = 1 - m1 := by
      rw [integral_sub (integrable_const (1 : ℝ)) hminint, hm1]
      simp
    rw [show (fun N : RWRS.Net 1 => Z N) = fun N : RWRS.Net 1 =>
      (fun z : ℝ => 1 - min z 1) (RWRS.netConfig N (RWRS.netRoot N))
        * degWeight (RWRS.forgetMarks N) from rfl, hfac, h2]
  have hZle : ∀ᵐ N ∂(RWRS.markIid Q ν), ∀ᶠ k in atTop, Z N ≤ Y k N := by
    filter_upwards [hns, hgoodP] with N hN hgoodN
    obtain ⟨j, hj⟩ := exists_one_le_config_of_not_stabilizes hgoodN (RWRS.netConfig N) hN
      (RWRS.netRoot N)
    filter_upwards [Filter.eventually_ge_atTop j] with k hk
    show (1 - min (RWRS.netConfig N (RWRS.netRoot N)) 1) * degWeight (RWRS.forgetMarks N)
      ≤ RWRS.netWeightedMassAt N k
        - min (RWRS.netConfig N (RWRS.netRoot N)) 1 * degWeight (RWRS.forgetMarks N)
    rw [netWeightedMassAt_eq_mul, ← sub_mul]
    exact mul_le_mul_of_nonneg_right (by linarith [hj k hk]) (degWeight_nonneg _)
  -- Fatou
  have hlin : ∀ k, ∫⁻ N, ENNReal.ofReal (Y k N) ∂(RWRS.markIid Q ν)
      = ENNReal.ofReal ((∫ z, z ∂ν) * c - m1 * c) := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hYint k)
      (Filter.Eventually.of_forall (hYnn k)), hYval k]
  have hfat : (∫⁻ N, ENNReal.ofReal (Z N) ∂(RWRS.markIid Q ν))
      ≤ ENNReal.ofReal ((∫ z, z ∂ν) * c - m1 * c) := by
    calc (∫⁻ N, ENNReal.ofReal (Z N) ∂(RWRS.markIid Q ν))
        ≤ ∫⁻ N, liminf (fun k => ENNReal.ofReal (Y k N)) atTop ∂(RWRS.markIid Q ν) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hZle] with N hN
          refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
          filter_upwards [hN] with k hk
          exact ENNReal.ofReal_le_ofReal hk
      _ ≤ liminf (fun k => ∫⁻ N, ENNReal.ofReal (Y k N) ∂(RWRS.markIid Q ν)) atTop :=
          lintegral_liminf_le fun k => (hYmeas k).ennreal_ofReal
      _ = ENNReal.ofReal ((∫ z, z ∂ν) * c - m1 * c) := by
          simp only [hlin]
          exact liminf_const _
  have hC0 : 0 ≤ (∫ z, z ∂ν) * c - m1 * c := by
    rw [← hYval 0]
    exact integral_nonneg (hYnn 0)
  have hZle' : ∫ N, Z N ∂(RWRS.markIid Q ν) ≤ (∫ z, z ∂ν) * c - m1 * c := by
    rw [← ENNReal.ofReal_le_ofReal_iff hC0,
      ofReal_integral_eq_lintegral_ofReal hZint (Filter.Eventually.of_forall hZnn)]
    exact hfat
  rw [hZval] at hZle'
  nlinarith [hZle', hcpos]

/-- The extended expectation of an integrable mark law is its integral. -/
theorem extMean_eq_integral_of_integrable (ν : Measure ℝ) (hint : Integrable (fun z : ℝ => z) ν) :
    RWRS.extMean ν = ((∫ z, z ∂ν : ℝ) : EReal) := by
  have hbound : ∀ z : ℝ, ENNReal.ofReal z ≤ ‖z‖ₑ := by
    intro z
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self z)
  have hboundneg : ∀ z : ℝ, ENNReal.ofReal (-z) ≤ ‖z‖ₑ := by
    intro z
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs z)
  have hfin : (∫⁻ z, ‖z‖ₑ ∂ν) ≠ ⊤ := ne_of_lt hint.2
  have hpos : RWRS.posPart ν ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (lintegral_mono hbound)
  have hneg : RWRS.negPart ν ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (lintegral_mono hboundneg)
  rw [RWRS.extMean, ← EReal.coe_ennreal_toReal hpos, ← EReal.coe_ennreal_toReal hneg,
    ← EReal.coe_sub]
  congr 1
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint).symm

end RWRS.Support
