import RWRS.Support.RootedClassPathTail
import LatticeProb.Prob.ErgodicDecomposition

/-!
# Ergodicity from class-walk averages

If the time averages of a generating family converge to their class-law means,
every rerooting-invariant class event has probability zero or one.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- Convergence to the class-law means on a generating π-system gives invariant-event triviality. -/
theorem classInvariant_zero_or_one_of_path_averages (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (hstat : classRerootKernel ∘ₘ ν = ν)
    {C : Set (Set RootedBallClass)}
    (hgen : (inferInstance : MeasurableSpace RootedBallClass) = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C)
    (hlim : ∀ A ∈ C, ∀ᵐ x ∂rootedClassPathLaw ν,
      Tendsto (fun n => LatticeProb.bAvg rootedClassPathShift
        (((fun x : ℕ → RootedBallClass => x 0) ⁻¹' A).indicator (fun _ => (1 : ℝ))) n x)
        atTop (𝓝 (ν.real A))) :
    ∀ D, MeasurableSet[rootedClassInvariantSigma] D → ν D = 0 ∨ ν D = 1 := by
  intro D hD
  apply LatticeProb.measure_zero_or_one_of_inter_eq_mul ν hgen hpi hD.1
  intro A hA
  let P := rootedClassPathLaw ν
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_rootedClassPathLaw ν
  let T := rootedClassPathTailEvent D
  let A₀ : Set (ℕ → RootedBallClass) := (fun x => x 0) ⁻¹' A
  let D₀ : Set (ℕ → RootedBallClass) := (fun x => x 0) ⁻¹' D
  have hAm : MeasurableSet A := by
    have hh : MeasurableSet[MeasurableSpace.generateFrom C] A :=
      MeasurableSpace.measurableSet_generateFrom hA
    rw [← hgen] at hh
    exact hh
  have hA₀ : MeasurableSet A₀ := hAm.preimage (measurable_pi_apply 0)
  have hfm : Measurable (A₀.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA₀
  have hfb : ∀ x, |A₀.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
    classical
    intro x
    by_cases hx : x ∈ A₀ <;> simp [hx]
  have ht : T =ᵐ[P] D₀ := rootedClassPathTailEvent_ae_eq ν hD
  have hmass : P T = ν D := by
    calc
      P T = P D₀ := measure_congr ht
      _ = (P.map (fun x => x 0)) D := (Measure.map_apply (measurable_pi_apply 0) hD.1).symm
      _ = ν D := by rw [rootedClassPathLaw_map_zero]
  have hi := LatticeProb.setIntegral_eq_mul_of_bAvg_tendsto
    (measurePreserving_rootedClassPathShift ν hstat) hfm zero_le_one hfb (hlim A hA)
    (measurableSet_rootedClassPathTailEvent_invariants hD.1)
  change (∫ x in T, A₀.indicator (fun _ => (1 : ℝ)) x ∂P) = P.real T * ν.real A at hi
  rw [Measure.restrict_congr_set ht] at hi
  have hleft : (∫ x in D₀, A₀.indicator (fun _ => (1 : ℝ)) x ∂P) = (ν (A ∩ D)).toReal := by
    rw [integral_indicator hA₀, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def, Measure.restrict_apply hA₀]
    change (P ((fun x : ℕ → RootedBallClass => x 0) ⁻¹' (A ∩ D))).toReal = _
    rw [← Measure.map_apply (measurable_pi_apply 0) (hAm.inter hD.1),
      rootedClassPathLaw_map_zero]
  rw [hleft, measureReal_def, hmass, measureReal_def] at hi
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top ν (A ∩ D))
    (ENNReal.mul_ne_top (measure_ne_top ν D) (measure_ne_top ν A))).mp
  simpa only [ENNReal.toReal_mul] using hi

end RWRS.Support
