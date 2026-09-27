import Mathlib
import Audit.Support.Vocabulary

/-!
# The audited statements in the challenge environment

Each audited statement, elaborated as a proposition in exactly the environment
of the challenges: this module imports only Mathlib and the vocabulary.
`Audit/StatementRegression.lean` checks that each solution theorem has
exactly this type, so that no repository name or instance leaks into a
solution statement.
-/

namespace RWRSAudit.Statements

open RWRSAudit MeasureTheory
open scoped ENNReal

universe u

-- The hypothesis names are kept so that the text matches the challenges.
set_option linter.unusedVariables false

/-- The statement of `Audit/OptimalStopping/Challenge.lean`. -/
def optimalStopping : Prop :=
  ∀ {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : HasExtMean ν),
    (0 < extMean ν →
      ∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ x = ⊤) ∧
    (extMean ν = 0 →
      ((0 < evar ν ∧ evar ν < ⊤) ∨ (ν ≠ Measure.dirac 0 ∧ IsSymmetric ν)) →
      (∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supStopValue G ξ x = ⊤) ∧
      (¬ DoublyTransient G →
        ∀ x : V, ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ x = ⊤)) ∧
    (extMean ν < 0 → ∀ p : ℝ, 3 < p → posMoment ν p ≠ ⊤ →
      ∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 → ∀ x : V,
        (∫⁻ z, supPayoff G z.1 z.2 ^ q ∂(jointLaw G ν x)) ≠ ⊤)

/-- The statement of `Audit/Explosion/Challenge.lean`. -/
def explosion : Prop :=
  ∀ {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V]
    (hG : G.Connected)
    (d : ℕ) (hd : BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : HasExtMean ν),
    (1 < extMean ν → iidLaw V ν {σ : V → ℝ | Stabilizes G σ} = 0) ∧
    (extMean ν = 1 →
      ((0 < evar ν ∧ evar ν < ⊤) ∨
        (ν ≠ Measure.dirac 1 ∧ IsSymmetric (ν.map (fun z => z - 1)))) →
      iidLaw V ν {σ : V → ℝ | Stabilizes G σ} = 0)

/-- The statement of `Audit/Stabilization/Challenge.lean`. -/
def stabilization : Prop :=
  ∀ {V : Type u} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (hG : G.Connected)
    (d : ℕ) (hd : BoundedDegree G d) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν)
    (hdet : HasExtMean ν) (hmean : extMean ν < 1),
    (∀ p : ℝ, 3 < p → posMoment ν p ≠ ⊤ →
      (∀ q : ℝ, 1 ≤ q → q < (p - 1) / 2 →
        (⨆ v : V, ∫⁻ σ, odometerLimit G σ v ^ q ∂(iidLaw V ν)) ≠ ⊤) ∧
      iidLaw V ν {σ : V → ℝ | Stabilizes G σ} = 1) ∧
    (∀ (o : V) (C d_f : ℝ), 0 < C → 1 ≤ d_f → VolumeGrowthUpper G o C d_f →
      ∀ p : ℝ, d_f < p → posMoment ν p ≠ ⊤ →
        iidLaw V ν {σ : V → ℝ | Stabilizes G σ} = 1)

end RWRSAudit.Statements
