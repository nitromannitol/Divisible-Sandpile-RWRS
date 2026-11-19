import RWRS.Support.RootedClassPathRestart

/-!
# Prefix and future of a class walk

The joint law of a finite prefix and the full walk is obtained by sampling the
prefix and continuing it with the trajectory kernel.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- The joint prefix and path law disintegrates through the trajectory kernel. -/
theorem rootedClassPathLaw_prefix_compProd_traj (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (rootedClassPathLaw ν).map (frestrictLe n) ⊗ₘ Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep n =
      (rootedClassPathLaw ν).map (fun x => (frestrictLe n x, x)) := by
  let μ₀ := ν.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => RootedBallClass)).symm
  haveI : IsProbabilityMeasure μ₀ := Measure.isProbabilityMeasure_map
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => RootedBallClass)).symm.measurable.aemeasurable
  have hF : Measurable (fun x : ℕ → RootedBallClass => (frestrictLe n x, x)) :=
    (measurable_frestrictLe n).prodMk measurable_id
  have hk : (Kernel.id ×ₖ Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep n) ∘ₖ
      Kernel.partialTraj (X := fun _ => RootedBallClass) rootedClassPathStep 0 n =
      (Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep 0).map (fun x => (frestrictLe n x, x)) := by
    ext u : 1
    rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod,
      Kernel.map_apply _ hF]
    exact Kernel.partialTraj_compProd_traj (X := fun _ => RootedBallClass) (κ := rootedClassPathStep) (Nat.zero_le n) u
  change ((Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep 0 ∘ₘ μ₀).map (frestrictLe n)) ⊗ₘ
      Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep n =
    (Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep 0 ∘ₘ μ₀).map (fun x => (frestrictLe n x, x))
  rw [Measure.map_comp _ _ (measurable_frestrictLe n), Kernel.traj_map_frestrictLe,
    Measure.compProd_eq_comp_prod, Measure.comp_assoc, hk,
    ← Measure.map_comp _ _ hF]

end RWRS.Support
