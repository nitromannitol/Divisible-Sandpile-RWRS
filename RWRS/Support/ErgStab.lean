/-
Stabilization is a measurable, isomorphism-invariant, rerooting-invariant event.

The `0`-`1` law of `lem:01-stationary` conditions the indicator of stabilization,
so that indicator has to be a measurable function of the network, and the paper's
proof uses that the event does not depend on the labelling of the vertices or on
the choice of root.  The toppling machinery of `Toppling.lean` already carries
the odometer through both, so only the passage to the limiting odometer is left.
-/
import RWRS.Support.Toppling

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The limiting odometer at a vertex is a measurable function of the network. -/
theorem measurable_odometerLimitNet (v : ℕ) :
    Measurable fun N : RWRS.Net 1 =>
      RWRS.odometerLimit (RWRS.netGraph N) (RWRS.netConfig N) v :=
  Measurable.iSup fun n => ENNReal.measurable_ofReal.comp (measurable_odometerNet n v)

/-- **Stabilization is a measurable event.** -/
theorem measurableSet_stabilizesNet :
    MeasurableSet {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} := by
  have heq : {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)}
      = ⋂ v : ℕ, {M : RWRS.Net 1 |
          RWRS.odometerLimit (RWRS.netGraph M) (RWRS.netConfig M) v ≠ ⊤} := by
    ext M
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [heq]
  exact MeasurableSet.iInter fun v => (measurable_odometerLimitNet v)
    (MeasurableSet.compl (measurableSet_singleton (⊤ : ℝ≥0∞)))

theorem netIso_symm {m : ℕ} {N N' : RWRS.Net m} (h : RWRS.NetIso N N') : RWRS.NetIso N' N := by
  obtain ⟨φ, hadj, hroot, hmark⟩ := h
  refine ⟨φ.symm, ?_, ?_, ?_⟩
  · intro i j
    have h2 := hadj (φ.symm i) (φ.symm j)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h2
    exact h2.symm
  · rw [← hroot, Equiv.symm_apply_apply]
  · intro i
    have h2 := hmark (φ.symm i)
    rw [Equiv.apply_symm_apply] at h2
    exact h2.symm

/-- **Stabilization does not depend on the labelling of the vertices.** -/
theorem netInvariantSet_stabilizes :
    RWRS.NetInvariantSet
      {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} := by
  have hone : ∀ (M M' : RWRS.Net 1), RWRS.NetIso M M' →
      RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M) →
      RWRS.Stabilizes (RWRS.netGraph M') (RWRS.netConfig M') := by
    rintro M M' ⟨φ, hadj, -, hmark⟩ hM z
    have hσ : ∀ i, RWRS.netConfig M' (φ i) = RWRS.netConfig M i := by
      intro i
      rw [RWRS.netConfig, RWRS.netConfig, hmark i]
    have hlim : RWRS.odometerLimit (RWRS.netGraph M') (RWRS.netConfig M') z
        = RWRS.odometerLimit (RWRS.netGraph M) (RWRS.netConfig M) (φ.symm z) := by
      have hstep : ∀ n : ℕ,
          RWRS.odometer (RWRS.netGraph M') (RWRS.netConfig M') n z
            = RWRS.odometer (RWRS.netGraph M) (RWRS.netConfig M) n (φ.symm z) := by
        intro n
        have := netIso_odometer (N := M) (N' := M') (φ := φ) hadj
          (RWRS.netConfig M) (RWRS.netConfig M') hσ n (φ.symm z)
        rwa [Equiv.apply_symm_apply] at this
      rw [RWRS.odometerLimit, RWRS.odometerLimit]
      exact iSup_congr fun n => by rw [hstep n]
    rw [hlim]
    exact hM (φ.symm z)
  intro M M' h
  exact ⟨fun hM => hone M M' h hM, fun hM' => hone M' M (netIso_symm h) hM'⟩

/-- **Stabilization does not depend on the choice of root.**  Rerooting changes
only the root coordinate, and neither the graph nor the marks read it. -/
theorem rerootInvariant_stabilizes :
    RWRS.RerootInvariant
      {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} :=
  fun _ _ _ => Iff.rfl

end RWRS.Support
