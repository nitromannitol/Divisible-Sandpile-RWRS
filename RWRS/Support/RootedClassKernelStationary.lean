import RWRS.Support.RootedClassKernel

/-!
# Stationarity of the class rerooting kernel

The class law induced by a stationary connected network law is preserved by
the uniform-neighbor rerooting kernel.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The class law is stationary under uniform-neighbor rerooting. -/
theorem lintegral_classRerootKernel_apply (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q)
    {D : Set RootedBallClass} (hD : MeasurableSet D) :
    (∫⁻ c, classRerootKernel c D ∂goodNetClassLaw Q) = goodNetClassLaw Q D := by
  let f : RootedBallClass → ℝ≥0∞ := D.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hD
  obtain ⟨g, -, hgeq, hgintegral⟩ := exists_classRerootAvg_integral_eq Q hgood hstat f hf
  have hpoint (c : RootedBallClass) : classRerootKernel c D = g c := by
    change classRerootMeasure c D = g c
    rw [classRerootMeasure_apply c hD]
    have h := hgeq (goodNetClassRepresentative c)
    rw [goodNetClass_representative] at h
    exact h.symm
  calc
    (∫⁻ c, classRerootKernel c D ∂goodNetClassLaw Q) =
        ∫⁻ c, g c ∂goodNetClassLaw Q := lintegral_congr hpoint
    _ = ∫⁻ c, f c ∂goodNetClassLaw Q := hgintegral
    _ = goodNetClassLaw Q D := by
      rw [show f = D.indicator (fun _ => (1 : ℝ≥0∞)) from rfl, lintegral_indicator hD]
      simp

end RWRS.Support
