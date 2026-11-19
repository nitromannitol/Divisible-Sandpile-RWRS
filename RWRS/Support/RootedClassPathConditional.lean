import RWRS.Support.RootedClassPathJoint
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Conditional expectations of class-walk paths

Given a finite prefix, conditional expectations of bounded path observables
are obtained by integrating against the trajectory kernel from that prefix.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder Filtration

/-- A path integral over a prefix event is the integral of the continuation means. -/
theorem setIntegral_rootedClassPathLaw_traj (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (n : ℕ) {L : (ℕ → RootedBallClass) → ℝ}
    (hL : Measurable L) {C : ℝ} (hbound : ∀ x, |L x| ≤ C)
    {A : Set (Finset.Iic n → RootedBallClass)} (hA : MeasurableSet A) :
    (∫ x in frestrictLe n ⁻¹' A, L x ∂rootedClassPathLaw ν) =
      ∫ u in A, ∫ x, L x ∂Kernel.traj rootedClassPathStep n u
        ∂(rootedClassPathLaw ν).map (frestrictLe n) := by
  let P := rootedClassPathLaw ν
  let μ := P.map (frestrictLe n)
  let K := Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep n
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_rootedClassPathLaw ν
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
  have hJ : μ ⊗ₘ K = P.map (fun x => (frestrictLe n x, x)) :=
    rootedClassPathLaw_prefix_compProd_traj ν n
  haveI : IsProbabilityMeasure (μ ⊗ₘ K) := inferInstance
  have hL₂ : Measurable (fun p : (Finset.Iic n → RootedBallClass) × (ℕ → RootedBallClass) => L p.2) :=
    hL.comp measurable_snd
  have hi : Integrable (fun p : (Finset.Iic n → RootedBallClass) × (ℕ → RootedBallClass) => L p.2)
      (μ ⊗ₘ K) := by
    apply Integrable.of_bound hL₂.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hbound p.2
  have h := Measure.setIntegral_compProd hA MeasurableSet.univ hi.integrableOn
  rw [hJ] at h
  have hF : Measurable (fun x : ℕ → RootedBallClass => (frestrictLe n x, x)) :=
    (measurable_frestrictLe n).prodMk measurable_id
  rw [setIntegral_map (hA.prod MeasurableSet.univ) hL₂.aestronglyMeasurable hF.aemeasurable] at h
  simpa only [Set.mem_univ, Set.prod_univ, Set.preimage_preimage, Function.comp_def,
    Measure.restrict_univ] using h

/-- The conditional expectation given a prefix is the mean under its continuation kernel. -/
theorem condExp_rootedClassPathLaw_traj (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (n : ℕ) {L : (ℕ → RootedBallClass) → ℝ}
    (hL : Measurable L) {C : ℝ} (hbound : ∀ x, |L x| ≤ C) :
    (rootedClassPathLaw ν)[L | piLE n] =ᵐ[rootedClassPathLaw ν]
      fun x => ∫ y, L y ∂Kernel.traj rootedClassPathStep n (frestrictLe n x) := by
  let P := rootedClassPathLaw ν
  let μ := P.map (frestrictLe n)
  let K := Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep n
  let G : (Finset.Iic n → RootedBallClass) → ℝ := fun u => ∫ x, L x ∂K u
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_rootedClassPathLaw ν
  haveI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
  have hi : Integrable L P := Integrable.of_bound hL.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  have hG : StronglyMeasurable G := hL.stronglyMeasurable.integral_kernel
  have hGb : ∀ u, ‖G u‖ ≤ C := by
    intro u
    haveI : IsProbabilityMeasure (K u) := inferInstance
    have h := norm_integral_le_of_norm_le_const (μ := K u) (f := L) (C := C)
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x)
    simpa only [G, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using h
  have hGi : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable C
    (Filter.Eventually.of_forall hGb)
  refine ae_eq_condExp_of_forall_setIntegral_eq (piLE.le _) hi
    (fun _ _ _ => hGi.comp_aemeasurable (measurable_frestrictLe n).aemeasurable |>.integrableOn)
    ?_ ?_ |>.symm <;> rw [piLE_eq_comap_frestrictLe]
  · rintro - ⟨A, hA, rfl⟩ -
    change (∫ x in frestrictLe n ⁻¹' A, G (frestrictLe n x) ∂P) = _
    rw [← setIntegral_map hA hGi.aestronglyMeasurable (measurable_frestrictLe n).aemeasurable]
    exact (setIntegral_rootedClassPathLaw_traj ν n hL hbound hA).symm
  · exact hGi.1.comp_ae_measurable' (measurable_frestrictLe n).aemeasurable

end RWRS.Support
