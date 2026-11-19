import RWRS.Support.RootedClassPathShift

/-!
# Rooted-class path kernel

The random walk path law is a Markov kernel in its initial rooted class.
Dropping its first state composes that kernel with one rerooting step.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- The path law started from a specified rooted class. -/
noncomputable def rootedClassPathKernel : Kernel RootedBallClass (ℕ → RootedBallClass) :=
  (Kernel.traj rootedClassPathStep 0).comap
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => RootedBallClass)).symm
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => RootedBallClass)).symm.measurable

/-- Each rooted class gives a probability law on paths. -/
instance isMarkovKernel_rootedClassPathKernel : IsMarkovKernel rootedClassPathKernel := by
  unfold rootedClassPathKernel
  infer_instance

/-- Mixing the path kernel against an initial law gives the path law. -/
theorem rootedClassPathKernel_comp (ν : Measure RootedBallClass) :
    rootedClassPathKernel ∘ₘ ν = rootedClassPathLaw ν := by
  unfold rootedClassPathLaw Kernel.trajMeasure
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _),
    Measure.bind_apply hS (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hS)
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => RootedBallClass)).symm.measurable]
  rfl

/-- The path law started from a point is the kernel at that point. -/
theorem rootedClassPathKernel_eq_dirac (c : RootedBallClass) :
    rootedClassPathKernel c = rootedClassPathLaw (Measure.dirac c) := by
  rw [← rootedClassPathKernel_comp, Measure.dirac_bind (Kernel.measurable _)]

/-- Shifting the path kernel is the path kernel preceded by one class transition. -/
theorem rootedClassPathKernel_map_shift :
    rootedClassPathKernel.map rootedClassPathShift = rootedClassPathKernel ∘ₖ classRerootKernel := by
  ext c
  rw [Kernel.map_apply _ measurable_rootedClassPathShift, rootedClassPathKernel_eq_dirac,
    rootedClassPathLaw_map_shift, Measure.dirac_bind (Kernel.measurable _),
    ← rootedClassPathKernel_comp, Kernel.comp_apply]

end RWRS.Support
