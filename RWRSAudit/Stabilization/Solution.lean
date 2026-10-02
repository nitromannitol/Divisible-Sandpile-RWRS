import Mathlib
import RWRS.MainTheorems
import RWRSAudit.Stabilization.SolutionBasic
import RWRSAudit.Support.StabilizationBridge

/-!
# Solution: Stabilization

The challenge module `RWRSAudit/Stabilization/Challenge.lean` imports only Mathlib and states
the theorem with one intentional `sorry`.  This solution imports the repository
together with `RWRSAudit.Stabilization.SolutionBasic`, a verbatim copy of the challenge's
vocabulary, and proves the byte-identical statement from `RWRS.stabilization`.  Every
vocabulary constant in this statement is definitionally equal to its
repository counterpart (`RWRSAudit/Support/StabilizationBridge.lean` records each
identification), so the library theorem, applied to the transported
hypothesis, closes the goal by `exact`.
-/

namespace RWRSAudit

open MeasureTheory
open scoped ENNReal

universe u

/-- Theorem 1.3 (`thm:stab`). -/
theorem stabilization {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : HasExtMean ν) (hmean : extMean ν < 1) :
    (∀ p : ℝ, 3 < p → posMoment ν p ≠ ⊤ →
      (∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 →
        (⨆ v : V, ∫⁻ σ, odometerLimit G σ v ^ q ∂(iidLaw V ν)) ≠ ⊤) ∧
      iidLaw V ν {σ : V → ℝ | Stabilizes G σ} = 1) ∧
    (∀ (o : V) (C d_f : ℝ), 0 < C → 1 ≤ d_f → VolumeGrowthUpper G o C d_f →
      ∀ p : ℝ, d_f < p → posMoment ν p ≠ ⊤ →
        iidLaw V ν {σ : V → ℝ | Stabilizes G σ} = 1) := by
  exact _root_.RWRS.stabilization hG d hd ν hν hdet hmean

end RWRSAudit
