import RWRS.Support.RootedClassPathInvariant

/-!
# Invariant observable values along class paths

A rerooting-invariant measurable class observable is almost surely constant
along the class walk.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- A class transition preserves an invariant observable almost surely. -/
theorem ae_classRerootKernel_invariantValue {g : RootedBallClass → ℝ}
    (hg : Measurable[rootedClassInvariantSigma] g) (c : RootedBallClass) :
    ∀ᵐ d ∂classRerootKernel c, g d = g c := by
  let D : Set RootedBallClass := g ⁻¹' {g c}
  have hD : MeasurableSet[rootedClassInvariantSigma] D := hg (measurableSet_singleton _)
  have hc : c ∈ D := Set.mem_singleton _
  filter_upwards [ae_classRerootKernel_mem_iff hD c] with d hd
  exact Set.mem_singleton_iff.mp (hd.mpr hc)

/-- Consecutive values of an invariant class observable agree almost surely. -/
theorem ae_rootedClassPathLaw_invariantValue_succ (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] {g : RootedBallClass → ℝ}
    (hg : Measurable[rootedClassInvariantSigma] g) (n : ℕ) :
    ∀ᵐ x ∂rootedClassPathLaw ν, g (x (n + 1)) = g (x n) := by
  let P := rootedClassPathLaw ν
  let i : Finset.Iic n := ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hg' : Measurable g := hg.mono rootedClassInvariantSigma_le le_rfl
  have hp : MeasurableSet {p : (Finset.Iic n → RootedBallClass) × RootedBallClass |
      g p.2 = g (p.1 i)} := measurableSet_eq_fun (hg'.comp measurable_snd)
        (hg'.comp ((measurable_pi_apply i).comp measurable_fst))
  have h : ∀ᵐ p ∂(P.map (frestrictLe n) ⊗ₘ rootedClassPathStep n),
      g p.2 = g (p.1 i) := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards with x
    exact ae_classRerootKernel_invariantValue hg (x i)
  rw [rootedClassPathLaw_prefix ν n] at h
  exact (ae_map_iff (measurable_frestrictLe n |>.prodMk (measurable_pi_apply (n + 1))).aemeasurable hp).mp h

/-- An invariant class observable has the same value at every time almost surely. -/
theorem ae_rootedClassPathLaw_invariantValue (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] {g : RootedBallClass → ℝ}
    (hg : Measurable[rootedClassInvariantSigma] g) :
    ∀ᵐ x ∂rootedClassPathLaw ν, ∀ n, g (x n) = g (x 0) := by
  have h : ∀ᵐ x ∂rootedClassPathLaw ν, ∀ n, g (x (n + 1)) = g (x n) :=
    ae_all_iff.mpr fun n => ae_rootedClassPathLaw_invariantValue_succ ν hg n
  filter_upwards [h] with x hx n
  induction n with
  | zero => rfl
  | succ n ih => exact (hx n).trans ih

end RWRS.Support
