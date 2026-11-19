import RWRS.Support.RootedClassPathInitial

/-!
# The initial class of a rooted walk

The initial coordinate of the rooted-class path has its prescribed law.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- The initial coordinate of the rooted-class path has law `ν`. -/
theorem rootedClassPathLaw_map_zero (ν : Measure RootedBallClass) :
    (rootedClassPathLaw ν).map (fun x => x 0) = ν := by
  let e := MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => RootedBallClass)
  have hfun : (fun x : ℕ → RootedBallClass => x 0) = e ∘ frestrictLe 0 := by
    funext x
    change x 0 = x (default : Finset.Iic 0).1
    have hzero : (default : Finset.Iic 0).1 = 0 :=
      Nat.le_zero.mp (Finset.mem_Iic.mp (default : Finset.Iic 0).2)
    rw [hzero]
  rw [hfun, ← Measure.map_map e.measurable (measurable_frestrictLe 0),
    rootedClassPathLaw_map_prefix_zero]
  exact MeasurableEquiv.map_map_symm e

end RWRS.Support
