/-
The independence used in Step 4 of `lem:moment-sharpness`: the mass at a site is
independent of the background, which reads only the other sites, and the masses
at two distinct sites are independent of each other.
-/
import RWRS.Support.Critical

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {V : Type*} {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- The law of one coordinate is the marginal. -/
theorem meas_coord (v : V) {s : Set ℝ} (hs : MeasurableSet s) :
    RWRS.iidLaw V ν {ξ : V → ℝ | ξ v ∈ s} = ν s := by
  have hmap : (RWRS.iidLaw V ν).map (fun ξ : V → ℝ => ξ v) = ν :=
    Measure.infinitePi_map_eval (fun _ : V => ν) v
  have := Measure.map_apply (measurable_pi_apply v) (μ := RWRS.iidLaw V ν) hs
  rw [hmap] at this
  exact this.symm

/-- **The mass at a site is independent of a weighted sum over the other sites.** -/
theorem indepFun_coord_weighted (v : V) (S : Finset V) (hv : v ∉ S) (w : V → ℝ) (μ : ℝ) :
    IndepFun (fun ξ : V → ℝ => ξ v)
      (fun ξ : V → ℝ => ∑ u ∈ S, w u * (ξ u - μ)) (RWRS.iidLaw V ν) := by
  classical
  have hdisj : Disjoint ({v} : Finset V) S := by
    simpa [Finset.disjoint_singleton_left] using hv
  have h := (iIndepFun_coord (V := V) ν).indepFun_finset ({v} : Finset V) S hdisj
    (fun i => measurable_pi_apply i)
  have hφ : Measurable (fun y : ({v} : Finset V) → ℝ => y ⟨v, Finset.mem_singleton_self v⟩) :=
    measurable_pi_apply _
  have hψ : Measurable (fun y : S → ℝ => ∑ u : S, w u * (y u - μ)) := by
    refine Finset.measurable_sum _ fun u _ => ?_
    have hu : Measurable fun y : S → ℝ => y u := measurable_pi_apply u
    exact (hu.sub_const μ).const_mul (w (u : V))
  have hcomp := h.comp hφ hψ
  refine hcomp.congr ?_ ?_
  · filter_upwards with ξ
    rfl
  · filter_upwards with ξ
    simp only [Function.comp_apply]
    exact (Finset.sum_coe_sort S (fun u => w u * (ξ u - μ)))

/-- The mass at a site and the background factorize. -/
theorem meas_inter_coord_weighted (v : V) (S : Finset V) (hv : v ∉ S) (w : V → ℝ) (μ : ℝ)
    {s r : Set ℝ} (hs : MeasurableSet s) (hr : MeasurableSet r) :
    RWRS.iidLaw V ν ({ξ : V → ℝ | ξ v ∈ s} ∩
        {ξ : V → ℝ | (∑ u ∈ S, w u * (ξ u - μ)) ∈ r})
      = ν s * RWRS.iidLaw V ν {ξ : V → ℝ | (∑ u ∈ S, w u * (ξ u - μ)) ∈ r} := by
  have h : RWRS.iidLaw V ν ({ξ : V → ℝ | ξ v ∈ s} ∩
        {ξ : V → ℝ | (∑ u ∈ S, w u * (ξ u - μ)) ∈ r})
      = RWRS.iidLaw V ν {ξ : V → ℝ | ξ v ∈ s} *
        RWRS.iidLaw V ν {ξ : V → ℝ | (∑ u ∈ S, w u * (ξ u - μ)) ∈ r} :=
    (indepFun_coord_weighted (ν := ν) v S hv w μ).measure_inter_preimage_eq_mul s r hs hr
  rw [h, meas_coord v hs]

/-- **The masses at two distinct sites are independent.** -/
theorem meas_inter_two_coord {v u : V} (hvu : v ≠ u) {s : Set ℝ} (hs : MeasurableSet s) :
    RWRS.iidLaw V ν ({ξ : V → ℝ | ξ v ∈ s} ∩ {ξ : V → ℝ | ξ u ∈ s}) = ν s * ν s := by
  have h : RWRS.iidLaw V ν ({ξ : V → ℝ | ξ v ∈ s} ∩ {ξ : V → ℝ | ξ u ∈ s})
      = RWRS.iidLaw V ν {ξ : V → ℝ | ξ v ∈ s} * RWRS.iidLaw V ν {ξ : V → ℝ | ξ u ∈ s} :=
    ((iIndepFun_coord (V := V) ν).indepFun hvu).measure_inter_preimage_eq_mul s s hs hs
  rw [h, meas_coord v hs, meas_coord u hs]

/-- A `[0,∞]`-valued function of one coordinate integrates against the marginal. -/
theorem lintegral_coord (v : V) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ξ, f (ξ v) ∂(RWRS.iidLaw V ν) = ∫⁻ z, f z ∂ν := by
  have hmap : (RWRS.iidLaw V ν).map (fun ξ : V → ℝ => ξ v) = ν :=
    Measure.infinitePi_map_eval (fun _ : V => ν) v
  conv_rhs => rw [← hmap]
  rw [lintegral_map hf (measurable_pi_apply v)]

end RWRS.Support
