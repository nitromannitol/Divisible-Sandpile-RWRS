import RWRS.Support.RootedClassPath

/-!
# Mapping finite-prefix transition laws

A measurable change of the past commutes with adjoining a transition whose
kernel depends on that changed past.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- Mapping the past of a composition product transports a comapped kernel. -/
theorem map_compProd_comap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) [SFinite μ] (κ : Kernel β γ)
    [IsSFiniteKernel κ] (f : α → β) (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) = μ.map f ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs, Measure.compProd_apply
    (hs.preimage (hf.prodMap measurable_id)), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

/-- Drop the initial state of a rooted-class path. -/
def rootedClassPathShift (x : ℕ → RootedBallClass) : ℕ → RootedBallClass :=
  fun n => x (n + 1)

/-- Drop the initial state of a finite rooted-class path. -/
def rootedClassPrefixShift (n : ℕ) (x : Finset.Iic (n + 1) → RootedBallClass) :
    Finset.Iic n → RootedBallClass :=
  fun i => x ⟨i.1 + 1, Finset.mem_Iic.mpr (Nat.succ_le_succ (Finset.mem_Iic.mp i.2))⟩

/-- Dropping the first state of a finite path is measurable. -/
theorem measurable_rootedClassPrefixShift (n : ℕ) : Measurable (rootedClassPrefixShift n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- Dropping the first state of an infinite path is measurable. -/
theorem measurable_rootedClassPathShift : Measurable rootedClassPathShift := by
  apply measurable_pi_lambda
  intro n
  exact measurable_pi_apply (n + 1)

/-- The transition after a shifted prefix uses the original last state. -/
theorem rootedClassPathStep_succ_eq_comap (n : ℕ) :
    rootedClassPathStep (n + 1) =
      (rootedClassPathStep n).comap (rootedClassPrefixShift n)
        (measurable_rootedClassPrefixShift n) := by
  rfl

/-- A shifted path still follows the rooted-class transition kernel. -/
theorem rootedClassPathLaw_shift_prefix (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (n : ℕ) :
    ((rootedClassPathLaw ν).map rootedClassPathShift).map (frestrictLe n) ⊗ₘ
        rootedClassPathStep n =
      ((rootedClassPathLaw ν).map rootedClassPathShift).map
        (fun x => (frestrictLe n x, x (n + 1))) := by
  let P := rootedClassPathLaw ν
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_rootedClassPathLaw ν
  haveI : IsProbabilityMeasure (P.map (frestrictLe (n + 1))) :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe (n + 1)).aemeasurable
  have h := map_compProd_comap (P.map (frestrictLe (n + 1)))
    (rootedClassPathStep n) (rootedClassPrefixShift n) (measurable_rootedClassPrefixShift n)
  rw [← rootedClassPathStep_succ_eq_comap, rootedClassPathLaw_prefix ν (n + 1)] at h
  have hleft : (P.map (frestrictLe (n + 1))).map (rootedClassPrefixShift n) =
      (P.map rootedClassPathShift).map (frestrictLe n) := by
    rw [Measure.map_map (measurable_rootedClassPrefixShift n) (measurable_frestrictLe (n + 1)),
      Measure.map_map (measurable_frestrictLe n) measurable_rootedClassPathShift]
    rfl
  rw [hleft] at h
  have hright :
      (P.map (fun x => (frestrictLe (n + 1) x, x (n + 1 + 1)))).map
          (Prod.map (rootedClassPrefixShift n) id) =
        (P.map rootedClassPathShift).map (fun x => (frestrictLe n x, x (n + 1))) := by
    rw [Measure.map_map ((measurable_rootedClassPrefixShift n).prodMap measurable_id)
      ((measurable_frestrictLe (n + 1)).prodMk (measurable_pi_apply (n + 1 + 1))),
      Measure.map_map ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1)))
        measurable_rootedClassPathShift]
    rfl
  rw [hright] at h
  exact h.symm

end RWRS.Support
