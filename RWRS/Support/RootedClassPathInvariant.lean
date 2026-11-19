import RWRS.Support.RootedClassPath
import RWRS.Support.RootedClassSigma

/-!
# Invariant events along rooted-class paths

A rerooting-invariant class event has constant membership along the random walk.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

/-- A class transition preserves membership in each invariant event almost surely. -/
theorem ae_classRerootKernel_mem_iff {D : Set RootedBallClass}
    (hD : MeasurableSet[rootedClassInvariantSigma] D) (c : RootedBallClass) :
    ∀ᵐ d ∂classRerootKernel c, (d ∈ D ↔ c ∈ D) := by
  classical
  by_cases hc : c ∈ D
  · have h : ∀ᵐ d ∂classRerootKernel c, d ∈ D := by
      apply (ae_mem_iff_measure_eq hD.1.nullMeasurableSet).2
      rw [classRerootKernel_apply_of_invariantSigma hD, Set.indicator_of_mem hc, measure_univ]
    exact h.mono fun _ hd => ⟨fun _ => hc, fun _ => hd⟩
  · have hzero : classRerootKernel c D = 0 := by
      rw [classRerootKernel_apply_of_invariantSigma hD, Set.indicator_of_notMem hc]
    have h : ∀ᵐ d ∂classRerootKernel c, d ∉ D := by
      apply ae_iff.mpr
      simpa only [not_not, Set.setOf_mem_eq] using hzero
    exact h.mono fun _ hd => ⟨fun hd' => (hd hd').elim, fun hc' => (hc hc').elim⟩

/-- The membership of an invariant event agrees at consecutive times almost surely. -/
theorem ae_rootedClassPathLaw_mem_iff_succ (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] {D : Set RootedBallClass}
    (hD : MeasurableSet[rootedClassInvariantSigma] D) (n : ℕ) :
    ∀ᵐ x ∂rootedClassPathLaw ν, (x (n + 1) ∈ D ↔ x n ∈ D) := by
  let P := rootedClassPathLaw ν
  let f : (ℕ → RootedBallClass) →
      ((Finset.Iic n → RootedBallClass) × RootedBallClass) :=
    fun x => (frestrictLe n x, x (n + 1))
  let i : Finset.Iic n := ⟨n, Finset.mem_Iic.mpr (le_refl n)⟩
  have hp : MeasurableSet {p : (Finset.Iic n → RootedBallClass) × RootedBallClass |
      p.2 ∈ D ↔ p.1 i ∈ D} := by
    exact (measurable_snd hD.1).iff
      (((measurable_pi_apply i).comp measurable_fst) hD.1)
  have h : ∀ᵐ p ∂(P.map (frestrictLe n) ⊗ₘ rootedClassPathStep n),
      (p.2 ∈ D ↔ p.1 i ∈ D) := by
    apply Measure.ae_compProd_of_ae_ae hp
    filter_upwards with x
    exact ae_classRerootKernel_mem_iff hD (x i)
  rw [rootedClassPathLaw_prefix ν n] at h
  exact (ae_map_iff (measurable_frestrictLe n |>.prodMk (measurable_pi_apply (n + 1))).aemeasurable hp).mp h

/-- An invariant class event has constant membership at every time almost surely. -/
theorem ae_rootedClassPathLaw_mem_iff_zero (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] {D : Set RootedBallClass}
    (hD : MeasurableSet[rootedClassInvariantSigma] D) :
    ∀ᵐ x ∂rootedClassPathLaw ν, ∀ n, (x n ∈ D ↔ x 0 ∈ D) := by
  have h : ∀ᵐ x ∂rootedClassPathLaw ν, ∀ n, (x (n + 1) ∈ D ↔ x n ∈ D) :=
    ae_all_iff.mpr fun n => ae_rootedClassPathLaw_mem_iff_succ ν hD n
  filter_upwards [h] with x hx n
  induction n with
  | zero => rfl
  | succ n ih => exact (hx n).trans ih

end RWRS.Support
