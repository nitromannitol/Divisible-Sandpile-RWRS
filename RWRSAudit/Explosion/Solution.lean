import Mathlib
import RWRS.MainTheorems
import RWRSAudit.Explosion.SolutionBasic
import RWRSAudit.Support.ExplosionBridge

/-!
# Solution: Explosion

The challenge module `RWRSAudit/Explosion/Challenge.lean` imports only Mathlib and states
the theorem with one intentional `sorry`.  This solution imports the repository
together with `RWRSAudit.Explosion.SolutionBasic`, a verbatim copy of the challenge's
vocabulary, and proves the byte-identical statement from `RWRS.explosion`.  Every
vocabulary constant in this statement is definitionally equal to its
repository counterpart (`RWRSAudit/Support/ExplosionBridge.lean` records each
identification), so the library theorem, applied to the transported
hypothesis, closes the goal by `exact`.
-/

namespace RWRSAudit

open MeasureTheory
open scoped ENNReal

universe u

/-- Theorem 1.2 (`thm:explosion`). -/
theorem explosion {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V]
    (hG : G.Connected)
    (d : ℕ) (hd : BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : HasExtMean ν) :
    (1 < extMean ν → iidLaw V ν {σ : V → ℝ | Stabilizes G σ} = 0) ∧
    (extMean ν = 1 →
      ((0 < evar ν ∧ evar ν < ⊤) ∨
        (ν ≠ Measure.dirac 1 ∧ IsSymmetric (ν.map (fun z => z - 1)))) →
      iidLaw V ν {σ : V → ℝ | Stabilizes G σ} = 0) := by
  exact _root_.RWRS.explosion hG d hd ν hν hdet

end RWRSAudit
