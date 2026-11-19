import RWRS.Support.RootedClassPathInvariant

/-!
# Stationary laws restricted to invariant class events

Restricting a stationary class law to a rerooting-invariant event preserves
stationarity under the class kernel.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- An invariant event can be moved outside a class transition probability. -/
theorem classRerootKernel_apply_inter_invariant {D B : Set RootedBallClass}
    (hD : MeasurableSet[rootedClassInvariantSigma] D)
    (c : RootedBallClass) :
    classRerootKernel c (B ∩ D) = D.indicator (fun c => classRerootKernel c B) c := by
  classical
  by_cases hc : c ∈ D
  · rw [Set.indicator_of_mem hc]
    apply measure_congr
    filter_upwards [ae_classRerootKernel_mem_iff hD c] with d hd
    apply propext
    change (d ∈ B ∧ d ∈ D) ↔ d ∈ B
    exact ⟨And.left, fun h => ⟨h, hd.mpr hc⟩⟩
  · rw [Set.indicator_of_notMem hc]
    have hzero : classRerootKernel c D = 0 := by
      rw [classRerootKernel_apply_of_invariantSigma hD, Set.indicator_of_notMem hc]
    exact measure_mono_null Set.inter_subset_right hzero

/-- Restricting a stationary class law to an invariant event gives a stationary finite measure. -/
theorem classRerootKernel_comp_restrict (ν : Measure RootedBallClass)
    (hstat : classRerootKernel ∘ₘ ν = ν) {D : Set RootedBallClass}
    (hD : MeasurableSet[rootedClassInvariantSigma] D) :
    classRerootKernel ∘ₘ (ν.restrict D) = ν.restrict D := by
  ext B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _), Measure.restrict_apply hB,
    ← lintegral_indicator hD.1]
  conv_rhs => rw [← hstat, Measure.bind_apply (hB.inter hD.1) (Kernel.aemeasurable _)]
  exact lintegral_congr fun c => (classRerootKernel_apply_inter_invariant hD c).symm

end RWRS.Support
