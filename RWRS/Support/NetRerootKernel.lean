import RWRS.Support.Marking

/-!
# The uniform-neighbor rerooting measure

The rerooting law is the uniform average of Dirac measures over neighbors,
with the Dirac measure at the current network used for an isolated root.
This construction follows `LatticeProb/Prob/RerootKernelInvariant.lean` in
Lattice-Probability.
-/

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The uniform-neighbor rerooting law, with the current root retained if isolated. -/
noncomputable def netRerootKernel {m : ℕ} (N : Net m) : Measure (Net m) :=
  if ((netGraph N).neighborFinset (netRoot N)).Nonempty then
    ((netGraph N).degree (netRoot N) : ℝ≥0∞)⁻¹ •
      ∑ y ∈ (netGraph N).neighborFinset (netRoot N), Measure.dirac (netReroot N y)
  else Measure.dirac N

/-- The uniform-neighbor rerooting law is a probability measure. -/
instance isProbabilityMeasure_netRerootKernel {m : ℕ} (N : Net m) :
    IsProbabilityMeasure (netRerootKernel N) := by
  classical
  rw [netRerootKernel]
  by_cases h : ((netGraph N).neighborFinset (netRoot N)).Nonempty
  · rw [if_pos h]
    constructor
    have hcard : ((netGraph N).neighborFinset (netRoot N)).card =
        (netGraph N).degree (netRoot N) := rfl
    have hpos : (((netGraph N).degree (netRoot N) : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by rw [← hcard]; exact Finset.card_ne_zero.mpr h)
    have htop : ((netGraph N).degree (netRoot N) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [Measure.smul_apply, Measure.finsetSum_apply]
    simp only [Measure.dirac_apply_of_mem (Set.mem_univ _)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, hcard,
      ENNReal.inv_mul_cancel hpos htop]
  · rw [if_neg h]
    infer_instance

/-- The rerooting law evaluates a rerooting-invariant event at its current root. -/
theorem netRerootKernel_apply_of_invariantSigma {m : ℕ} {A : Set (Net m)}
    (hA : MeasurableSet[invariantSigma m] A) (N : Net m) :
    netRerootKernel N A = A.indicator (fun _ => (1 : ℝ≥0∞)) N := by
  classical
  have hre : RerootInvariant A := hA.2.2
  rw [netRerootKernel]
  by_cases h : ((netGraph N).neighborFinset (netRoot N)).Nonempty
  · rw [if_pos h]
    have hcard : ((netGraph N).neighborFinset (netRoot N)).card =
        (netGraph N).degree (netRoot N) := rfl
    have hpos : (((netGraph N).degree (netRoot N) : ℕ) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by rw [← hcard]; exact Finset.card_ne_zero.mpr h)
    have htop : ((netGraph N).degree (netRoot N) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    rw [Measure.smul_apply, Measure.finsetSum_apply]
    have hconst : ∀ y ∈ (netGraph N).neighborFinset (netRoot N),
        Measure.dirac (netReroot N y) A = A.indicator (fun _ => (1 : ℝ≥0∞)) N := by
      intro y hy
      have hadj : (netGraph N).Adj (netRoot N) y := by
        simpa [SimpleGraph.mem_neighborFinset] using hy
      rw [Measure.dirac_apply' _ hA.1]
      by_cases hN : N ∈ A
      · have hyA : netReroot N y ∈ A := (hre N y hadj).1 hN
        rw [Set.indicator_of_mem hN, Set.indicator_of_mem hyA]
        rfl
      · have hyA : netReroot N y ∉ A := fun hyA => hN ((hre N y hadj).2 hyA)
        rw [Set.indicator_of_notMem hN, Set.indicator_of_notMem hyA]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, smul_eq_mul, hcard,
      ← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]
  · rw [if_neg h, Measure.dirac_apply' _ hA.1]
    rfl

end RWRS.Support
