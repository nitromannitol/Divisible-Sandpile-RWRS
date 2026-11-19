import RWRS.Support.RootedClassPathKernel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Harmonic means of shift-invariant path observables

Integrating a bounded shift-invariant path observable against the path kernel
gives a bounded measurable harmonic function of the initial rooted class.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- Mean of a path observable under the walk started at a given class. -/
noncomputable def rootedClassPathMean (L : (ℕ → RootedBallClass) → ℝ)
    (c : RootedBallClass) : ℝ := ∫ x, L x ∂rootedClassPathKernel c

/-- The mean of a measurable path observable is measurable in the initial class. -/
theorem measurable_rootedClassPathMean {L : (ℕ → RootedBallClass) → ℝ} (hL : Measurable L) :
    Measurable (rootedClassPathMean L) := by
  exact (hL.stronglyMeasurable.integral_kernel (κ := rootedClassPathKernel)).measurable

/-- A uniform bound on the path observable bounds all its class means. -/
theorem abs_rootedClassPathMean_le {L : (ℕ → RootedBallClass) → ℝ} {C : ℝ}
    (hbound : ∀ x, |L x| ≤ C) (c : RootedBallClass) :
    |rootedClassPathMean L c| ≤ C := by
  haveI : IsProbabilityMeasure (rootedClassPathKernel c) := inferInstance
  have h := norm_integral_le_of_norm_le_const (μ := rootedClassPathKernel c) (f := L) (C := C)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x))
  simpa only [rootedClassPathMean, Real.norm_eq_abs, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul, mul_one] using h

/-- A bounded shift-invariant path observable has a harmonic class mean. -/
theorem rootedClassPathMean_harmonic {L : (ℕ → RootedBallClass) → ℝ}
    (hL : Measurable L) {C : ℝ} (hbound : ∀ x, |L x| ≤ C)
    (hshift : ∀ x, L (rootedClassPathShift x) = L x) (c : RootedBallClass) :
    rootedClassPathMean L c = ∫ d, rootedClassPathMean L d ∂classRerootKernel c := by
  haveI : IsProbabilityMeasure ((rootedClassPathKernel ∘ₖ classRerootKernel) c) := inferInstance
  have hi : Integrable L ((rootedClassPathKernel ∘ₖ classRerootKernel) c) := by
    apply Integrable.of_bound hL.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x
  calc
    rootedClassPathMean L c = ∫ x, L (rootedClassPathShift x) ∂rootedClassPathKernel c := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (hshift x).symm
    _ = ∫ x, L x ∂(rootedClassPathKernel c).map rootedClassPathShift := by
      symm
      exact integral_map measurable_rootedClassPathShift.aemeasurable hL.aestronglyMeasurable
    _ = ∫ x, L x ∂(rootedClassPathKernel ∘ₖ classRerootKernel) c := by
      rw [← Kernel.map_apply _ measurable_rootedClassPathShift, rootedClassPathKernel_map_shift]
    _ = ∫ d, rootedClassPathMean L d ∂classRerootKernel c := Kernel.integral_comp hi

end RWRS.Support
