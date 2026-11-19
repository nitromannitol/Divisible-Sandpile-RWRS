import RWRS.Support.ConditionalClassPath
import RWRS.Support.ConditionalClassObservables

/-!
# Invariant observables on conditional class paths

A countable family of invariant class observables has a deterministic initial
value along the paths of almost every conditional network law.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- Invariant class observables are almost surely constant at time zero in conditional class paths. -/
theorem ae_conditional_classPath_initial_values (Q : Measure (Net 0)) [IsProbabilityMeasure Q]
    (hgood : ∀ᵐ N ∂Q, NetGood N) (f : ℕ → RootedBallClass → ℝ)
    (hf : ∀ j, Measurable[rootedClassInvariantSigma] (f j)) :
    ∀ᵐ N ∂Q, ∀ j, ∀ᵐ x ∂rootedClassPathLaw
      (goodNetClassLaw (condExpKernel Q (invariantSigma 0) N)),
      f j (x 0) = invariantClassObservable (f j) N := by
  obtain ⟨N, hN⟩ := hgood.exists
  let N₀ : GoodNet := ⟨N, hN⟩
  have hconst := ae_ae_invariantClassObservable Q f hf
  have hsupport := LatticeProb.ae_ae_conditionalMeasure Q invariantSigma_zero_le hgood
  filter_upwards [hconst, hsupport] with M hM hMg j
  let K := condExpKernel Q (invariantSigma 0) M
  let ν := goodNetClassLaw K
  let P := rootedClassPathLaw ν
  haveI : IsProbabilityMeasure K := inferInstance
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_goodNetClassLaw K hMg
  have hmeas : Measurable (f j) := (hf j).mono rootedClassInvariantSigma_le le_rfl
  have hD : MeasurableSet {c | f j c = invariantClassObservable (f j) M} :=
    measurableSet_eq_fun hmeas measurable_const
  have hclass : ∀ᵐ c ∂ν, f j c = invariantClassObservable (f j) M := by
    change ∀ᵐ c ∂goodNetClassLaw K, f j c = invariantClassObservable (f j) M
    rw [goodNetClassLaw_eq_map_total N₀ K hMg]
    apply (ae_map_iff (measurable_goodNetClassTotal N₀).aemeasurable hD).2
    filter_upwards [hM j, hMg] with Z hZ hZg
    rw [goodNetClassTotal_of_good N₀ ⟨Z, hZg⟩,
      ← invariantClassObservable_of_good (f j) ⟨Z, hZg⟩]
    exact hZ
  have hpath : ∀ᵐ c ∂P.map (fun x => x 0), f j c = invariantClassObservable (f j) M := by
    change ∀ᵐ c ∂(rootedClassPathLaw ν).map (fun x => x 0),
      f j c = invariantClassObservable (f j) M
    rw [rootedClassPathLaw_map_zero]
    exact hclass
  exact (ae_map_iff (measurable_pi_apply 0).aemeasurable hD).1 hpath

end RWRS.Support
