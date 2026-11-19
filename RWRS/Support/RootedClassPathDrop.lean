import RWRS.Support.RootedClassPathKernel

/-!
# Dropping an initial path segment

Dropping a finite initial segment of a class path preserves its forward
transition identities.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- Drop the first `n` states of a class path. -/
def rootedClassPathDrop (n : ℕ) (x : ℕ → RootedBallClass) : ℕ → RootedBallClass :=
  fun k => x (n + k)

/-- Drop the first `n` states from a finite class path. -/
def rootedClassPrefixDrop (n k : ℕ) (x : Finset.Iic (n + k) → RootedBallClass) :
    Finset.Iic k → RootedBallClass :=
  fun i => x ⟨n + i.1, Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp i.2) n)⟩

/-- Dropping an initial path segment is measurable. -/
theorem measurable_rootedClassPathDrop (n : ℕ) : Measurable (rootedClassPathDrop n) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_pi_apply (n + k)

/-- Dropping an initial finite-prefix segment is measurable. -/
theorem measurable_rootedClassPrefixDrop (n k : ℕ) : Measurable (rootedClassPrefixDrop n k) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

/-- The class kernel reads the same last state before and after dropping a prefix. -/
theorem rootedClassPathStep_add_eq_comap (n k : ℕ) :
    rootedClassPathStep (n + k) =
      (rootedClassPathStep k).comap (rootedClassPrefixDrop n k)
        (measurable_rootedClassPrefixDrop n k) := by
  rfl

/-- A forward transition identity is inherited by the path after dropping its first states. -/
theorem map_rootedClassPathDrop_prefix (μ : Measure (ℕ → RootedBallClass))
    [IsProbabilityMeasure μ] (n k : ℕ)
    (hforward : μ.map (frestrictLe (n + k)) ⊗ₘ rootedClassPathStep (n + k) =
      μ.map (fun x => (frestrictLe (n + k) x, x (n + k + 1)))) :
    (μ.map (rootedClassPathDrop n)).map (frestrictLe k) ⊗ₘ rootedClassPathStep k =
      (μ.map (rootedClassPathDrop n)).map (fun x => (frestrictLe k x, x (k + 1))) := by
  haveI : IsProbabilityMeasure (μ.map (frestrictLe (n + k))) :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe (n + k)).aemeasurable
  have h := map_compProd_comap (μ.map (frestrictLe (n + k)))
    (rootedClassPathStep k) (rootedClassPrefixDrop n k) (measurable_rootedClassPrefixDrop n k)
  rw [← rootedClassPathStep_add_eq_comap, hforward] at h
  have hleft : (μ.map (frestrictLe (n + k))).map (rootedClassPrefixDrop n k) =
      (μ.map (rootedClassPathDrop n)).map (frestrictLe k) := by
    rw [Measure.map_map (measurable_rootedClassPrefixDrop n k) (measurable_frestrictLe (n + k)),
      Measure.map_map (measurable_frestrictLe k) (measurable_rootedClassPathDrop n)]
    rfl
  rw [hleft] at h
  have hright :
      (μ.map (fun x => (frestrictLe (n + k) x, x (n + k + 1)))).map
          (Prod.map (rootedClassPrefixDrop n k) id) =
        (μ.map (rootedClassPathDrop n)).map (fun x => (frestrictLe k x, x (k + 1))) := by
    rw [Measure.map_map ((measurable_rootedClassPrefixDrop n k).prodMap measurable_id)
      ((measurable_frestrictLe (n + k)).prodMk (measurable_pi_apply (n + k + 1))),
      Measure.map_map ((measurable_frestrictLe k).prodMk (measurable_pi_apply (k + 1)))
        (measurable_rootedClassPathDrop n)]
    congr 1
  rw [hright] at h
  exact h.symm

end RWRS.Support
