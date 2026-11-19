import RWRS.Support.RootedClassPathNext

/-!
# Stationary one-time rooted-class path laws

The rerooting kernel preserves the initial class law, so every individual
coordinate of the class walk has that law.
-/

open MeasureTheory ProbabilityTheory

namespace RWRS.Support

/-- The class rerooting kernel preserves the stationary class law. -/
theorem classRerootKernel_comp_goodNetClassLaw (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q) :
    classRerootKernel ∘ₘ goodNetClassLaw Q = goodNetClassLaw Q := by
  ext D hD
  rw [Measure.bind_apply hD (Kernel.aemeasurable _)]
  exact lintegral_classRerootKernel_apply Q hgood hstat hD

/-- Each coordinate of the rooted-class walk has the stationary class law. -/
theorem rootedClassPathLaw_map_eq (Q : Measure (Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q) (n : ℕ) :
    (rootedClassPathLaw (goodNetClassLaw Q)).map (fun x => x n) = goodNetClassLaw Q := by
  haveI := isProbabilityMeasure_goodNetClassLaw Q hgood
  induction n with
  | zero => exact rootedClassPathLaw_map_zero _
  | succ n ih =>
      rw [rootedClassPathLaw_map_succ, ih, classRerootKernel_comp_goodNetClassLaw Q hgood hstat]

end RWRS.Support
