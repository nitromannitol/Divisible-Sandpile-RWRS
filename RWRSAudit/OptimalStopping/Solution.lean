import Mathlib
import RWRS.MainTheorems
import RWRSAudit.OptimalStopping.SolutionBasic
import RWRSAudit.Support.OptimalStoppingBridge

/-!
# Solution: OptimalStopping

The challenge module `RWRSAudit/OptimalStopping/Challenge.lean` imports only Mathlib and states
the theorem with one intentional `sorry`.  This solution imports the repository
together with `RWRSAudit.OptimalStopping.SolutionBasic`, a verbatim copy of the challenge's
vocabulary, and proves the byte-identical statement from `RWRS.optimalStopping`.  The goal
is rewritten with the identifications of `RWRSAudit/Support/OptimalStoppingBridge.lean` for the
four constants built on recursive definitions (`supMeanPayoff`,
`supStopValue`, `DoublyTransient`, `jointLaw`); every other vocabulary
constant is definitionally equal to its repository counterpart, so the library
theorem, applied to the transported hypothesis, closes the goal by `exact`.
-/

namespace RWRSAudit

open MeasureTheory
open scoped ENNReal

universe u

/-- Theorem 1.1 (`thm:OS`). -/
theorem optimalStopping {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : HasExtMean ν) :
    (0 < extMean ν →
      ∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ x = ⊤) ∧
    (extMean ν = 0 →
      ((0 < evar ν ∧ evar ν < ⊤) ∨ (ν ≠ Measure.dirac 0 ∧ IsSymmetric ν)) →
      (∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supStopValue G ξ x = ⊤) ∧
      (¬ DoublyTransient G →
        ∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ x = ⊤)) ∧
    (extMean ν < 0 → ∀ p : ℝ, 3 < p → posMoment ν p ≠ ⊤ →
      ∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 → ∀ x : V,
        (∫⁻ z, supPayoff G z.1 z.2 ^ q ∂(jointLaw G ν x)) ≠ ⊤) := by
  rw [Bridge.supMeanPayoff_eq, Bridge.supStopValue_eq, Bridge.doublyTransient_eq,
    Bridge.jointLaw_eq]
  exact _root_.RWRS.optimalStopping hG d hd ν hν hdet

end RWRSAudit
