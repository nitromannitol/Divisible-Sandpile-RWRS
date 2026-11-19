import RWRS.Support.ConditionalErgodicityCriterion

/-!
# Conditional ergodicity from path information

Identifying bounded shift-invariant path observables with invariant observables
of the initial class gives ergodicity of the conditional network laws.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Path-information identification implies conditional ergodicity. -/
theorem ae_conditional_isErgodicNet_of_path_information (Q : Measure (Net 0))
    [IsProbabilityMeasure Q] (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q)
    (hinfo : ∀ L : (ℕ → RootedBallClass) → ℝ, Measurable L →
      (∀ x, |L x| ≤ 1) → (∀ x, L (rootedClassPathShift x) = L x) →
      ∃ g : RootedBallClass → ℝ, Measurable[rootedClassInvariantSigma] g ∧
        ∀ᵐ x ∂rootedClassPathLaw (goodNetClassLaw Q), L x = g (x 0)) :
    ∀ᵐ N ∂Q, IsErgodicNet (condExpKernel Q (invariantSigma 0) N) := by
  obtain ⟨C, hcount, hpi, hgen⟩ :=
    LatticeProb.exists_countable_generating_piSystem (X := RootedBallClass)
  apply ae_conditional_isErgodicNet_of_average_factors Q hgood hstat hcount hpi hgen
  intro A hA
  let ν := goodNetClassLaw Q
  let P := rootedClassPathLaw ν
  let A₀ : Set (ℕ → RootedBallClass) := (fun x => x 0) ⁻¹' A
  let F : (ℕ → RootedBallClass) → ℝ := A₀.indicator (fun _ => 1)
  let L := LatticeProb.bLimsup rootedClassPathShift F
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_goodNetClassLaw Q hgood
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_rootedClassPathLaw ν
  have hAm : MeasurableSet A := by
    have hh : MeasurableSet[MeasurableSpace.generateFrom C] A :=
      MeasurableSpace.measurableSet_generateFrom hA
    rw [← hgen] at hh
    exact hh
  have hF : Measurable F := measurable_const.indicator (hAm.preimage (measurable_pi_apply 0))
  have hb : ∀ x, |F x| ≤ 1 := by
    classical
    intro x
    by_cases hx : x ∈ A₀ <;> simp [F, hx]
  have hL : Measurable L := LatticeProb.measurable_bLimsup measurable_rootedClassPathShift hF
  have hLb : ∀ x, |L x| ≤ 1 := LatticeProb.abs_bLimsup_le zero_le_one hb
  have hLs : ∀ x, L (rootedClassPathShift x) = L x :=
    LatticeProb.bLimsup_comp (T := rootedClassPathShift) (f := F) zero_le_one hb
  obtain ⟨g, hg, hfactor⟩ := hinfo L hL hLb hLs
  refine ⟨g, hg, ?_⟩
  have hi : Integrable F P := Integrable.of_bound hF.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hconv := LatticeProb.ae_tendsto_bLimsup
    (measurePreserving_rootedClassPathShift ν
      (classRerootKernel_comp_goodNetClassLaw Q hgood hstat)) hF hi
  filter_upwards [hconv, hfactor] with x hx hfactorx
  rw [← hfactorx]
  exact hx

end RWRS.Support
