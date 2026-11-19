import RWRS.Support.ConditionalClassPathObservables
import RWRS.Support.RootedClassErgodicityTransfer
import RWRS.Support.RootedClassStationarityTransfer

/-!
# Conditional ergodicity from invariant average factors

If the generating class-walk averages converge to invariant functions of the
initial class, almost every conditional network law is ergodic.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- Invariant factors for generating class-walk averages imply conditional network ergodicity. -/
theorem ae_conditional_isErgodicNet_of_average_factors (Q : Measure (Net 0))
    [IsProbabilityMeasure Q] (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q)
    {C : Set (Set RootedBallClass)} (hcount : C.Countable) (hpi : IsPiSystem C)
    (hgen : (inferInstance : MeasurableSpace RootedBallClass) = MeasurableSpace.generateFrom C)
    (hfac : ∀ A ∈ C, ∃ g : RootedBallClass → ℝ, Measurable[rootedClassInvariantSigma] g ∧
      ∀ᵐ x ∂rootedClassPathLaw (goodNetClassLaw Q),
        Tendsto (fun n => LatticeProb.bAvg rootedClassPathShift
          (((fun x : ℕ → RootedBallClass => x 0) ⁻¹' A).indicator (fun _ => (1 : ℝ))) n x)
          atTop (𝓝 (g (x 0)))) :
    ∀ᵐ N ∂Q, IsErgodicNet (condExpKernel Q (invariantSigma 0) N) := by
  classical
  letI : Countable C := hcount.to_subtype
  let g : C → RootedBallClass → ℝ := fun A => Classical.choose (hfac A.1 A.2)
  have hg (A : C) : Measurable[rootedClassInvariantSigma] (g A) :=
    (Classical.choose_spec (hfac A.1 A.2)).1
  have hconv (A : C) : ∀ᵐ N ∂Q, ∀ᵐ x ∂rootedClassPathLaw
      (goodNetClassLaw (condExpKernel Q (invariantSigma 0) N)),
      Tendsto (fun n => LatticeProb.bAvg rootedClassPathShift
        (((fun x : ℕ → RootedBallClass => x 0) ⁻¹' A.1).indicator (fun _ => (1 : ℝ))) n x)
        atTop (𝓝 (g A (x 0))) :=
    ae_ae_conditional_rootedClassPathLaw Q hgood (Classical.choose_spec (hfac A.1 A.2)).2
  have hconvs : ∀ᵐ N ∂Q, ∀ A : C, ∀ᵐ x ∂rootedClassPathLaw
      (goodNetClassLaw (condExpKernel Q (invariantSigma 0) N)),
      Tendsto (fun n => LatticeProb.bAvg rootedClassPathShift
        (((fun x : ℕ → RootedBallClass => x 0) ⁻¹' A.1).indicator (fun _ => (1 : ℝ))) n x)
        atTop (𝓝 (g A (x 0))) := ae_all_iff.mpr hconv
  have hvals := ae_conditional_classPath_initial_values Q hgood g hg
  have hsupport := LatticeProb.ae_ae_conditionalMeasure Q invariantSigma_zero_le hgood
  have hstatclass := ae_conditional_goodNetClassLaw_stationary Q hgood hstat
  filter_upwards [hconvs, hvals, hsupport, hstatclass] with N hNconv hNval hNg hNs
  let K := condExpKernel Q (invariantSigma 0) N
  let ν := goodNetClassLaw K
  let P := rootedClassPathLaw ν
  haveI : IsProbabilityMeasure K := inferInstance
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_goodNetClassLaw K hNg
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_rootedClassPathLaw ν
  apply isErgodicNet_of_goodNetClassLaw K hNg
  apply classInvariant_zero_or_one_of_path_averages ν hNs hgen hpi
  intro A hA
  let a : C := ⟨A, hA⟩
  let A₀ : Set (ℕ → RootedBallClass) := (fun x => x 0) ⁻¹' A
  let F : (ℕ → RootedBallClass) → ℝ := A₀.indicator (fun _ => 1)
  let c := invariantClassObservable (g a) N
  have hAm : MeasurableSet A := by
    have hh : MeasurableSet[MeasurableSpace.generateFrom C] A :=
      MeasurableSpace.measurableSet_generateFrom hA
    rw [← hgen] at hh
    exact hh
  have hA₀ : MeasurableSet A₀ := hAm.preimage (measurable_pi_apply 0)
  have hF : Measurable F := measurable_const.indicator hA₀
  have hFb : ∀ x, |F x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ A₀ <;> simp [F, hx]
  have hlimit : ∀ᵐ x ∂P, Tendsto (fun n => LatticeProb.bAvg rootedClassPathShift F n x)
      atTop (𝓝 c) := by
    filter_upwards [hNconv a, hNval a] with x hx hv
    change Tendsto (fun n => LatticeProb.bAvg rootedClassPathShift F n x)
      atTop (𝓝 (invariantClassObservable (g a) N))
    rw [← hv]
    exact hx
  have hmean : (∫ x, F x ∂P) = ν.real A := by
    rw [show F = A₀.indicator (fun _ => (1 : ℝ)) from rfl, integral_indicator hA₀,
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    change (P ((fun x : ℕ → RootedBallClass => x 0) ⁻¹' A)).toReal = _
    rw [← Measure.map_apply (measurable_pi_apply 0) hAm, rootedClassPathLaw_map_zero]
    rfl
  have hconstant := LatticeProb.setIntegral_eq_mul_of_bAvg_tendsto
    (measurePreserving_rootedClassPathShift ν hNs) hF zero_le_one hFb hlimit
    (MeasurableSet.univ : MeasurableSet[MeasurableSpace.invariants rootedClassPathShift] Set.univ)
  have hc : c = ν.real A := by
    rw [Measure.restrict_univ] at hconstant
    change (∫ x, F x ∂P) = P.real Set.univ * c at hconstant
    rw [hmean] at hconstant
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul] using hconstant.symm
  simpa only [← hc] using hlimit

end RWRS.Support
