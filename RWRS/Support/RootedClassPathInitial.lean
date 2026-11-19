import RWRS.Support.RootedClassPath

/-!
# Initial law of the rooted class path

The zero-prefix marginal of the rooted class path is its prescribed initial
class law, transported to the one-coordinate prefix space.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- The zero-prefix marginal of the class path is its initial law. -/
theorem rootedClassPathLaw_map_prefix_zero (ν : Measure RootedBallClass) :
    (rootedClassPathLaw ν).map (frestrictLe 0) =
      ν.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => RootedBallClass)).symm := by
  rw [rootedClassPathLaw, Kernel.trajMeasure,
    Measure.map_comp _ _ (measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
    Kernel.partialTraj_self, Measure.id_comp]

end RWRS.Support
