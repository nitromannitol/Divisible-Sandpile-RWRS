/-
The supercritical half of `thm:stationary-phase`.

If the sandpile stabilizes almost surely then the mean mark is at most one
(`rwrs.tex:351-358`).  At a mark law bounded above by `M` the emissions of every
round are bounded by `M - 1`, so they vanish in mean along the rounds by
dominated convergence; conservation of the degree-weighted mass and the bound
`σ_k(ρ)/deg(ρ) ≤ 1/deg(ρ) + e_k(ρ)` then give `E[σ] E[1/deg(ρ)] ≤ E[1/deg(ρ)]`,
and the mean reciprocal degree is positive.  The general case follows by
truncating the marks above at `M`, which preserves stabilization, and letting
`M` grow, the mark law having a finite first moment.
-/
import RWRS.Support.ErgSuper
import RWRS.Support.ErgDom
import RWRS.Support.ProbHelpers
import RWRS.Frozen.StationaryToppling
import RWRS.Frozen.IidStationary
import RWRS.Support.ErgStab

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace RWRS.Support

theorem ae_netGood_markIid (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) :
    ∀ᵐ N ∂(RWRS.markIid Q ν), RWRS.NetGood N := by
  have hqmp : Measure.QuasiMeasurePreserving RWRS.forgetMarks (RWRS.markIid Q ν) Q :=
    ⟨measurable_forgetMarks, by rw [map_forgetMarks_markIid Q ν]⟩
  exact hqmp.ae hgood

theorem integral_degWeight_markIid (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (∫ N : RWRS.Net 1, degWeight (RWRS.forgetMarks N) ∂(RWRS.markIid Q ν))
      = ∫ N, degWeight N ∂Q := by
  conv_rhs => rw [← map_forgetMarks_markIid Q ν]
  exact (integral_map measurable_forgetMarks.aemeasurable
    measurable_degWeight.aestronglyMeasurable).symm

/-- The supercritical estimate for a mark law bounded above: if the sandpile
stabilizes almost surely then the mean mark is at most one.  This is
`rwrs.tex:351-358` at a fixed truncation level. -/
theorem integral_id_le_one_of_bddAbove
    (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {M : ℝ} (hM : 1 ≤ M)
    (hbd : ∀ᵐ z ∂ν, z ≤ M)
    (hint : Integrable (fun N => |RWRS.netWeightedMass N|) (RWRS.markIid Q ν))
    (hstab : ∀ᵐ N ∂(RWRS.markIid Q ν),
      RWRS.Stabilizes (RWRS.netGraph N) (RWRS.netConfig N)) :
    ∫ z, z ∂ν ≤ 1 := by
  haveI hP : IsProbabilityMeasure (RWRS.markIid Q ν) := isProbabilityMeasure_markIid Q ν
  have hgoodP : ∀ᵐ N ∂(RWRS.markIid Q ν), RWRS.NetGood N := ae_netGood_markIid Q ν hgood
  have hstatP : RWRS.IsStationaryNet (RWRS.markIid Q ν) :=
    RWRS.Frozen.iidStationary Q inferInstance ν inferInstance hstat
  set c : ℝ := ∫ N, degWeight N ∂Q with hc
  have hcpos : 0 < c := integral_degWeight_pos Q hgood
  have hν1 : Integrable (fun z : ℝ => z) ν :=
    integrable_id_of_integrable_netWeightedMass Q hgood ν hint
  -- the emissions are uniformly bounded
  have hbdd : ∀ k : ℕ, ∀ᵐ N ∂(RWRS.markIid Q ν), netEmission N k ≤ M - 1 := by
    intro k
    filter_upwards [hgoodP, ae_netConfig_mem Q ν measurableSet_Iic hbd] with N hN hmark
    exact emission_config_le hN hM (fun v => hmark v) k (RWRS.netRoot N)
  have hemint : ∀ k : ℕ, Integrable (fun N : RWRS.Net 1 => netEmission N k)
      (RWRS.markIid Q ν) := by
    intro k
    refine (integrable_const (M - 1)).mono' (measurable_netEmission k).aestronglyMeasurable ?_
    filter_upwards [hbdd k] with N hN
    rw [Real.norm_eq_abs, abs_of_nonneg (netEmission_nonneg N k)]
    exact hN
  have hdegint : Integrable (fun N : RWRS.Net 1 => degWeight (RWRS.forgetMarks N))
      (RWRS.markIid Q ν) := by
    refine (integrable_const (1 : ℝ)).mono'
      (measurable_degWeight.comp measurable_forgetMarks).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun N => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (degWeight_nonneg _)]
    exact degWeight_le_one _
  -- conservation
  have hcons : ∀ k : ℕ, Integrable (fun N => RWRS.netWeightedMassAt N k) (RWRS.markIid Q ν) ∧
      ∫ N, RWRS.netWeightedMassAt N k ∂(RWRS.markIid Q ν)
        = ∫ N, RWRS.netWeightedMass N ∂(RWRS.markIid Q ν) := fun k =>
    ⟨(RWRS.Frozen.stationaryToppling (RWRS.markIid Q ν) hP hgoodP hstatP hint k).2.1,
      (RWRS.Frozen.stationaryToppling (RWRS.markIid Q ν) hP hgoodP hstatP hint k).2.2⟩
  have hmass : ∫ N, RWRS.netWeightedMass N ∂(RWRS.markIid Q ν) = (∫ z, z ∂ν) * c :=
    integral_netWeightedMass_markIid Q ν hν1
  -- the estimate at each round
  have hle : ∀ k : ℕ, (∫ z, z ∂ν) * c
      ≤ c + ∫ N, netEmission N k ∂(RWRS.markIid Q ν) := by
    intro k
    have hstep : ∫ N, RWRS.netWeightedMassAt N k ∂(RWRS.markIid Q ν)
        ≤ ∫ N, (degWeight (RWRS.forgetMarks N) + netEmission N k) ∂(RWRS.markIid Q ν) := by
      refine integral_mono (hcons k).1 (hdegint.add (hemint k)) fun N => ?_
      have := netWeightedMassAt_le N k
      rw [one_div] at this
      exact this
    rw [integral_add hdegint (hemint k), integral_degWeight_markIid Q ν] at hstep
    rw [← hmass, ← (hcons k).2]
    exact hstep
  -- the emission vanishes in the limit
  have hlim : Tendsto (fun k : ℕ => ∫ N, netEmission N k ∂(RWRS.markIid Q ν)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_integral_netEmission (RWRS.markIid Q ν) hbdd hstab
  have hfinal : (∫ z, z ∂ν) * c ≤ c := by
    have hconv : Tendsto (fun k : ℕ => c + ∫ N, netEmission N k ∂(RWRS.markIid Q ν))
        atTop (𝓝 (c + 0)) := tendsto_const_nhds.add hlim
    rw [add_zero] at hconv
    exact ge_of_tendsto hconv (Filter.Eventually.of_forall hle)
  nlinarith [hfinal, hcpos]


/-- The supercritical estimate: if the sandpile stabilizes almost surely then
the mean mark is at most one (`rwrs.tex:351-358`). -/
theorem integral_id_le_one_of_ae_stabilizes
    (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun N => |RWRS.netWeightedMass N|) (RWRS.markIid Q ν))
    (hstab : ∀ᵐ N ∂(RWRS.markIid Q ν),
      RWRS.Stabilizes (RWRS.netGraph N) (RWRS.netConfig N)) :
    ∫ z, z ∂ν ≤ 1 := by
  haveI hP : IsProbabilityMeasure (RWRS.markIid Q ν) := isProbabilityMeasure_markIid Q ν
  have hgoodP : ∀ᵐ N ∂(RWRS.markIid Q ν), RWRS.NetGood N := ae_netGood_markIid Q ν hgood
  have hν1 : Integrable (fun z : ℝ => z) ν :=
    integrable_id_of_integrable_netWeightedMass Q hgood ν hint
  -- the estimate at every truncation level
  have hstep : ∀ M : ℝ, 1 ≤ M → ∫ z, min z M ∂ν ≤ 1 := by
    intro M hM
    have hmeas : Measurable fun z : ℝ => min z M := measurable_id.min measurable_const
    set νM : Measure ℝ := ν.map fun z => min z M with hνM
    haveI : IsProbabilityMeasure νM := Measure.isProbabilityMeasure_map hmeas.aemeasurable
    have habs : ∀ z : ℝ, |min z M| ≤ |z| := by
      intro z
      rcases le_total z M with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, abs_of_nonneg (le_trans zero_le_one hM)]
        exact le_trans h (le_abs_self z)
    have hmapint : Integrable (fun z : ℝ => min z M) ν :=
      hν1.abs.mono' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          exact habs z)
    have hνM1 : Integrable (fun z : ℝ => z) νM :=
      (integrable_map_measure measurable_id.aestronglyMeasurable hmeas.aemeasurable).mpr hmapint
    have hbdM : ∀ᵐ z ∂νM, z ≤ M := by
      rw [hνM, ae_map_iff hmeas.aemeasurable measurableSet_Iic]
      exact Filter.Eventually.of_forall fun z => min_le_right z M
    have hintM : Integrable (fun N => |RWRS.netWeightedMass N|) (RWRS.markIid Q νM) := by
      have h1 : Integrable (fun N : RWRS.Net 1 =>
          (fun z : ℝ => z) (RWRS.netConfig N (RWRS.netRoot N))
            * degWeight (RWRS.forgetMarks N)) (RWRS.markIid Q νM) :=
        integrable_markIid_mark_mul Q νM measurable_id measurable_degWeight hνM1
          (integrable_degWeight Q)
      have h2 : Integrable (fun N : RWRS.Net 1 => RWRS.netWeightedMass N) (RWRS.markIid Q νM) := by
        refine h1.congr (Filter.Eventually.of_forall fun N => ?_)
        exact (netWeightedMass_eq_mul N).symm
      exact h2.abs
    have hstabM : ∀ᵐ N ∂(RWRS.markIid Q νM),
        RWRS.Stabilizes (RWRS.netGraph N) (RWRS.netConfig N) := by
      rw [hνM, ← markIid_map_truncMarks Q ν M,
        ae_map_iff (measurable_truncMarks M).aemeasurable measurableSet_stabilizesNet]
      filter_upwards [hstab, hgoodP] with N hN hgoodN
      exact stabilizes_of_le hgoodN (fun v => min_le_left _ _) hN
    have := integral_id_le_one_of_bddAbove Q hgood hstat νM hM hbdM hintM hstabM
    rwa [hνM, integral_map (f := fun z : ℝ => z) hmeas.aemeasurable
      measurable_id.aestronglyMeasurable] at this
  -- let the truncation level grow
  have hlim : Tendsto (fun n : ℕ => ∫ z, min z (n : ℝ) ∂ν) atTop (𝓝 (∫ z, z ∂ν)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun z : ℝ => |z|)
      (fun n => (measurable_id.min measurable_const).aestronglyMeasurable) hν1.abs
      (fun n => Filter.Eventually.of_forall fun z => ?_) ?_
    · rw [Real.norm_eq_abs]
      rcases le_total z (n : ℝ) with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h, abs_le]
        exact ⟨by linarith [neg_abs_le z, abs_nonneg z, Nat.cast_nonneg (α := ℝ) n],
          le_trans h (le_abs_self z)⟩
    · refine Filter.Eventually.of_forall fun z => ?_
      obtain ⟨n0, hn0⟩ := exists_nat_gt z
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop n0] with n hn
      have : z ≤ (n : ℝ) := le_trans (le_of_lt hn0) (Nat.cast_le.mpr hn)
      exact (min_eq_left this).symm
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact hstep (n : ℝ) (by exact_mod_cast hn)

end RWRS.Support
