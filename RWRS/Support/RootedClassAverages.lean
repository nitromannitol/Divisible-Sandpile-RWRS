import RWRS.Support.RootedClassPathShift
import LatticeProb.Prob.Birkhoff

/-!
# Time averages along rooted-class paths

For bounded observables of the rooted class, their time averages converge
almost surely under a stationary class path law. The upper limit is measurable
and invariant under path shift at every path.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- The value of a class observable at the initial point of a path. -/
def rootedClassPathObservable (f : RootedBallClass → ℝ) (x : ℕ → RootedBallClass) : ℝ :=
  f (x 0)

/-- The upper time-average limit of a rooted-class observable. -/
noncomputable def rootedClassPathAverageLimit (f : RootedBallClass → ℝ)
    (x : ℕ → RootedBallClass) : ℝ :=
  LatticeProb.bLimsup rootedClassPathShift (rootedClassPathObservable f) x

/-- The upper time-average limit is measurable. -/
theorem measurable_rootedClassPathAverageLimit {f : RootedBallClass → ℝ}
    (hf : Measurable f) : Measurable (rootedClassPathAverageLimit f) := by
  exact LatticeProb.measurable_bLimsup measurable_rootedClassPathShift
    (hf.comp (measurable_pi_apply 0))

/-- The upper time-average limit of a bounded observable is path-shift invariant. -/
theorem rootedClassPathAverageLimit_shift {f : RootedBallClass → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ c, |f c| ≤ C) (x : ℕ → RootedBallClass) :
    rootedClassPathAverageLimit f (rootedClassPathShift x) = rootedClassPathAverageLimit f x := by
  exact LatticeProb.bLimsup_comp (T := rootedClassPathShift)
    (f := rootedClassPathObservable f) hC (fun x => hf (x 0)) x

/-- Stationary class-walk time averages of a bounded measurable observable converge almost surely. -/
theorem ae_tendsto_rootedClassPathAverageLimit (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (hstat : classRerootKernel ∘ₘ ν = ν)
    {f : RootedBallClass → ℝ} (hf : Measurable f) {C : ℝ}
    (hbound : ∀ c, |f c| ≤ C) :
    ∀ᵐ x ∂rootedClassPathLaw ν,
      Tendsto (fun n => LatticeProb.bAvg rootedClassPathShift (rootedClassPathObservable f) n x)
        atTop (𝓝 (rootedClassPathAverageLimit f x)) := by
  haveI := isProbabilityMeasure_rootedClassPathLaw ν
  have hobs : Measurable (rootedClassPathObservable f) := hf.comp (measurable_pi_apply 0)
  have hi : Integrable (rootedClassPathObservable f) (rootedClassPathLaw ν) := by
    apply Integrable.of_bound hobs.aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun x => by simpa only [rootedClassPathObservable, Real.norm_eq_abs] using hbound (x 0)
  exact LatticeProb.ae_tendsto_bLimsup (measurePreserving_rootedClassPathShift ν hstat) hobs hi

end RWRS.Support
