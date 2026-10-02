import Mathlib
import RWRS.MainTheorems
import RWRSAudit.OptimalStopping.SolutionBasic

/-!
# Bridge from the `OptimalStopping` vocabulary to the repository

The vocabulary of `RWRSAudit/OptimalStopping/Challenge.lean` (copied verbatim into
`RWRSAudit/OptimalStopping/SolutionBasic.lean`, which imports only Mathlib) is a statement-level
copy of the repository definitions. It contains no structure: every declaration is a definition
over Mathlib types, written token for token as in `RWRS/Basic.lean`, `RWRS/Walk.lean`,
`RWRS/Scenery.lean` and `RWRS/Setting.lean`. Each constant that the statement of
`optimalStopping` depends on is therefore definitionally equal to its repository counterpart,
and this file records each identification as an equation of constants. The non-recursive
definitions are identified by `rfl`, which the kernel checks by unfolding both sides. The three
recursive definitions `heat`, `walkExp` and `walkPath` are compiled by structural recursion into
distinct auxiliary constants, so they are identified by induction on the time index, and the
definitions built on them (`green`, `stopValues`, `walkLaw`, `meanPayoff`, `supMeanPayoff`,
`supStopValue`, `jointLaw`, `DoublyTransient`) by rewriting. Nothing is asserted.

**It is imported by the `Solution` file only.**  The `Challenge` and `SolutionBasic` files must
stay Mathlib-only: a repository import inside the vocabulary changes instance elaboration there
and breaks the comparator's constant-by-constant closure check.
-/

namespace RWRSAudit.Bridge

/-! ### Non-recursive definitions -/

theorem walkOp_eq : @RWRSAudit.walkOp = @RWRS.walkOp := rfl

theorem cons_eq : @RWRSAudit.cons = @RWRS.cons := rfl

theorem IsStopping_eq : @RWRSAudit.IsStopping = @RWRS.IsStopping := rfl

theorem payoff_eq : @RWRSAudit.payoff = @RWRS.payoff := rfl

theorem stepLaw_eq : @RWRSAudit.stepLaw = @RWRS.stepLaw := rfl

theorem driverLaw_eq : @RWRSAudit.driverLaw = @RWRS.driverLaw := rfl

theorem stepTo_eq : @RWRSAudit.stepTo = @RWRS.stepTo := rfl

theorem supPayoff_eq : @RWRSAudit.supPayoff = @RWRS.supPayoff := rfl

theorem iidLaw_eq : @RWRSAudit.iidLaw = @RWRS.iidLaw := rfl

theorem posPart_eq : @RWRSAudit.posPart = @RWRS.posPart := rfl

theorem negPart_eq : @RWRSAudit.negPart = @RWRS.negPart := rfl

theorem extMean_eq : @RWRSAudit.extMean = @RWRS.extMean := rfl

theorem HasExtMean_eq : @RWRSAudit.HasExtMean = @RWRS.HasExtMean := rfl

theorem posMoment_eq : @RWRSAudit.posMoment = @RWRS.posMoment := rfl

theorem IsSymmetric_eq : @RWRSAudit.IsSymmetric = @RWRS.IsSymmetric := rfl

theorem evar_eq : @RWRSAudit.evar = @RWRS.evar := rfl

theorem BoundedDegree_eq : @RWRSAudit.BoundedDegree = @RWRS.BoundedDegree := rfl

/-! ### The recursive definitions, by induction -/

section Recursive

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

theorem heat_apply : ∀ k : ℕ, RWRSAudit.heat G k = RWRS.heat G k
  | 0 => by
    funext x y
    simp only [RWRSAudit.heat, RWRS.heat]
  | k + 1 => by
    funext x y
    simp only [RWRSAudit.heat, RWRS.heat, heat_apply k]
    rfl

theorem walkExp_apply : ∀ (n : ℕ) (x : V) (F : (ℕ → V) → ℝ),
    RWRSAudit.walkExp G n x F = RWRS.walkExp G n x F
  | 0, x, F => by simp only [RWRSAudit.walkExp, RWRS.walkExp]
  | n + 1, x, F => by
    simp only [RWRSAudit.walkExp, RWRS.walkExp, walkExp_apply n]
    rfl

theorem walkPath_apply (x : V) (ω : ℕ → ℝ) :
    ∀ k : ℕ, RWRSAudit.walkPath G x ω k = RWRS.walkPath G x ω k
  | 0 => by simp only [RWRSAudit.walkPath, RWRS.walkPath]
  | k + 1 => by
    simp only [RWRSAudit.walkPath, RWRS.walkPath, walkPath_apply x ω k]
    rfl

end Recursive

theorem heat_eq : @RWRSAudit.heat = @RWRS.heat := by
  funext V G _ k
  exact heat_apply G k

theorem walkExp_eq : @RWRSAudit.walkExp = @RWRS.walkExp := by
  funext V G _ n x F
  exact walkExp_apply G n x F

theorem walkPath_eq : @RWRSAudit.walkPath = @RWRS.walkPath := by
  funext V G _ x ω k
  exact walkPath_apply G x ω k

/-! ### The definitions built on them, by rewriting -/

theorem green_eq : @RWRSAudit.green = @RWRS.green := by
  funext V G _ x v
  simp only [RWRSAudit.green, RWRS.green, heat_eq]

theorem stopValues_eq : @RWRSAudit.stopValues = @RWRS.stopValues := by
  funext V G _ ξ n x
  simp only [RWRSAudit.stopValues, RWRS.stopValues, walkExp_eq]
  rfl

theorem walkLaw_eq : @RWRSAudit.walkLaw = @RWRS.walkLaw := by
  funext V G _ _ x
  simp only [RWRSAudit.walkLaw, RWRS.walkLaw, walkPath_eq]
  rfl

theorem meanPayoff_eq : @RWRSAudit.meanPayoff = @RWRS.meanPayoff := by
  funext V G _ ξ n x
  simp only [RWRSAudit.meanPayoff, RWRS.meanPayoff, walkExp_eq]
  rfl

theorem supMeanPayoff_eq : @RWRSAudit.supMeanPayoff = @RWRS.supMeanPayoff := by
  funext V G _ ξ x
  simp only [RWRSAudit.supMeanPayoff, RWRS.supMeanPayoff, meanPayoff_eq]

theorem supStopValue_eq : @RWRSAudit.supStopValue = @RWRS.supStopValue := by
  funext V G _ ξ x
  simp only [RWRSAudit.supStopValue, RWRS.supStopValue, stopValues_eq]

theorem jointLaw_eq : @RWRSAudit.jointLaw = @RWRS.jointLaw := by
  funext V G _ _ ν x
  simp only [RWRSAudit.jointLaw, RWRS.jointLaw, walkLaw_eq]
  rfl

theorem doublyTransient_eq : @RWRSAudit.DoublyTransient = @RWRS.DoublyTransient := by
  funext V G _
  simp only [RWRSAudit.DoublyTransient, RWRS.DoublyTransient, green_eq]

end RWRSAudit.Bridge
