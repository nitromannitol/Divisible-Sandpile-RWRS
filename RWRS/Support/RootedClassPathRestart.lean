import RWRS.Support.RootedClassPathDrop

/-!
# Restarting the class walk after a fixed prefix

The future after a prescribed finite trajectory has the class path law started
from the last state of that trajectory.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- Dropping a prescribed prefix restarts the path at its last state. -/
theorem rootedClassTraj_map_drop (n : ℕ) (u : Finset.Iic n → RootedBallClass) :
    (Kernel.traj rootedClassPathStep n u).map (rootedClassPathDrop n) =
      rootedClassPathKernel (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  let μ : Measure (ℕ → RootedBallClass) := Kernel.traj rootedClassPathStep n u
  let c := u ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  haveI : IsProbabilityMeasure μ := inferInstance
  haveI : IsProbabilityMeasure (μ.map (rootedClassPathDrop n)) :=
    Measure.isProbabilityMeasure_map (measurable_rootedClassPathDrop n).aemeasurable
  haveI : IsProbabilityMeasure (rootedClassPathLaw (Measure.dirac c)) :=
    isProbabilityMeasure_rootedClassPathLaw _
  rw [rootedClassPathKernel_eq_dirac]
  apply rootedClassPathLaw_unique
  · have hpre : μ.map (frestrictLe n) = Measure.dirac u := by
      change (Kernel.traj (X := fun _ => RootedBallClass) rootedClassPathStep n u).map (frestrictLe n) = _
      rw [← Kernel.map_apply _ (measurable_frestrictLe n), Kernel.traj_map_frestrictLe,
        Kernel.partialTraj_self, Kernel.id_apply]
    have heval : μ.map (fun x => x n) = Measure.dirac c := by
      have hfun : (fun x : ℕ → RootedBallClass => x n) =
          (fun z : Finset.Iic n → RootedBallClass => z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) ∘
            frestrictLe n := rfl
      have hg : Measurable (fun z : Finset.Iic n → RootedBallClass =>
          z ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
      rw [hfun, ← Measure.map_map hg (measurable_frestrictLe n), hpre,
        Measure.map_dirac' hg]
    rw [Measure.map_map (measurable_pi_apply 0) (measurable_rootedClassPathDrop n),
      rootedClassPathLaw_map_zero]
    simpa only [rootedClassPathDrop, Nat.add_zero, Function.comp_def] using heval
  · intro k
    apply map_rootedClassPathDrop_prefix μ n k
    have h := Kernel.partialTraj_compProd_eq_map_traj (X := fun _ => RootedBallClass) (κ := rootedClassPathStep)
      (a := n) (b := n + k) (Nat.le_add_right n k) (x₀ := u)
    rw [← Kernel.traj_map_frestrictLe_apply (X := fun _ => RootedBallClass) (κ := rootedClassPathStep) n (n + k) u] at h
    exact h
  · exact rootedClassPathLaw_prefix (Measure.dirac c)

end RWRS.Support
