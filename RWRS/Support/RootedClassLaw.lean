import RWRS.Support.RootedClassStationary

/-!
# Probability laws on rooted graph classes

A probability measure supported on connected network codes pushes forward to
a probability measure on rooted graph classes.
-/

namespace RWRS.Support

open MeasureTheory

/-- A probability law supported on connected networks gives a probability class law. -/
theorem isProbabilityMeasure_goodNetClassLaw (Q : Measure (Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, NetGood N) : IsProbabilityMeasure (goodNetClassLaw Q) := by
  haveI : IsProbabilityMeasure (Q.comap (Subtype.val : GoodNet → Net 0)) :=
    (MeasurableEmbedding.subtype_coe measurableSet_netGood).isProbabilityMeasure_comap
      (by
        filter_upwards [hgood] with N hN
        exact ⟨⟨N, hN⟩, rfl⟩)
  exact Measure.isProbabilityMeasure_map measurable_goodNetClass.aemeasurable

end RWRS.Support
