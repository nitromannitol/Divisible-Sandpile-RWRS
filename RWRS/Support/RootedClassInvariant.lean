import RWRS.Support.RootedClassKernelStationary

/-!
# Rerooting-invariant class events

A measurable class event unchanged by rerooting is fixed pointwise by the
uniform-neighbor transition kernel.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A class event unchanged by rerooting is fixed by the class transition kernel. -/
theorem classRerootKernel_apply_of_rerootInvariant {D : Set RootedBallClass}
    (hD : MeasurableSet D)
    (hre : ∀ (N : GoodNet) (y : ℕ),
      goodNetClass N ∈ D ↔ goodNetClass ⟨netReroot N.1 y, netGood_netReroot N.2 y⟩ ∈ D)
    (c : RootedBallClass) :
    classRerootKernel c D = D.indicator (fun _ => (1 : ℝ≥0∞)) c := by
  classical
  let N := goodNetClassRepresentative c
  have hc : goodNetClass N = c := goodNetClass_representative c
  have hcard : ((netGraph N.1).neighborFinset (netRoot N.1)).card =
      (netGraph N.1).degree (netRoot N.1) := rfl
  have hpos : (((netGraph N.1).degree (netRoot N.1) : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (degree_netRoot_pos N.2).ne'
  have htop : ((netGraph N.1).degree (netRoot N.1) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  change (((netGraph N.1).degree (netRoot N.1) : ℝ≥0∞)⁻¹ •
    ∑ y ∈ (netGraph N.1).neighborFinset (netRoot N.1),
      Measure.dirac (goodNetClass ⟨netReroot N.1 y, netGood_netReroot N.2 y⟩)) D = _
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  have hconst : ∀ y ∈ (netGraph N.1).neighborFinset (netRoot N.1),
      Measure.dirac (goodNetClass ⟨netReroot N.1 y, netGood_netReroot N.2 y⟩) D =
        D.indicator (fun _ => (1 : ℝ≥0∞)) c := by
    intro y _
    rw [Measure.dirac_apply' _ hD]
    have hy := hre N y
    rw [hc] at hy
    by_cases h : c ∈ D
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hy.1 h)]
      rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hh => h (hy.2 hh))]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, smul_eq_mul, hcard,
    ← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]

end RWRS.Support
