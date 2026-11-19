import RWRS.Support.RootedClassKernel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Random-walk paths of rooted graph classes

The Ionescu–Tulcea construction gives the path law for the class rerooting
kernel from any initial law on rooted graph classes.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- The next-step kernel reads the last class of a finite path. -/
noncomputable def rootedClassPathStep (n : ℕ) :
    Kernel (Finset.Iic n → RootedBallClass) RootedBallClass :=
  classRerootKernel.comap
    (fun x => x ⟨n, Finset.mem_Iic.mpr (le_refl n)⟩)
    (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr (le_refl n)⟩ : Finset.Iic n))

/-- Every finite-prefix class transition is a Markov kernel. -/
instance isMarkovKernel_rootedClassPathStep (n : ℕ) : IsMarkovKernel (rootedClassPathStep n) := by
  unfold rootedClassPathStep
  infer_instance

/-- The rooted-class random-walk path law with initial class law `ν`. -/
noncomputable def rootedClassPathLaw (ν : Measure RootedBallClass) :
    Measure (ℕ → RootedBallClass) := Kernel.trajMeasure ν rootedClassPathStep

/-- A probability initial class law gives a probability path law. -/
theorem isProbabilityMeasure_rootedClassPathLaw (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (rootedClassPathLaw ν) := by
  unfold rootedClassPathLaw
  infer_instance

/-- The finite-prefix path law extends by the class rerooting kernel. -/
theorem rootedClassPathLaw_prefix (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (rootedClassPathLaw ν).map (frestrictLe n) ⊗ₘ rootedClassPathStep n =
      (rootedClassPathLaw ν).map (fun x => (frestrictLe n x, x (n + 1))) := by
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end RWRS.Support
