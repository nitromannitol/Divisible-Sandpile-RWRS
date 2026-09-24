/-
The voltage identity `eq:voltage-identity`: for a finite set `C` from which the
walk escapes,

    E_o[S_{τ_C}] = ∑_{v ∈ C} g_C(o,v) (σ(v) - 1) .

The payoff `S_{τ_C}` is the sum of `ζ(X_k) = (σ(X_k)-1)/deg(X_k)` over the steps
before the exit, and the library's occupation identity turns that expectation
into a sum against `∑_k p^C_k(o,·)`, which is `deg(v) g_C(o,v)`.  This is the
identity that Section 3 reads the finite-volume value through, and the one that
Sections 5 and 6 use to bound the odometer from below by an electrical
computation.
-/
import RWRS.Support.KilledGreen
import RWRS.Setting
import LatticeProb.Graph.ExitTime

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-! ### The walk on path space is the library's -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem stepTo_eq_lib (x : V) (u : ℝ) :
    RWRS.stepTo G x u = LatticeProb.Graph.stepTo G x u := rfl

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem walkPath_eq_lib (x : V) (ω : ℕ → ℝ) :
    ∀ k : ℕ, RWRS.walkPath G x ω k = LatticeProb.Graph.walkPath G x ω k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      show RWRS.stepTo G (RWRS.walkPath G x ω k) (ω k)
        = LatticeProb.Graph.stepTo G (LatticeProb.Graph.walkPath G x ω k) (ω k)
      rw [stepTo_eq_lib, ih]

omit [MeasurableSingletonClass V] [Countable V] in
theorem walkLaw_eq_lib (x : V) : RWRS.walkLaw G x = LatticeProb.Graph.walkLaw G x := by
  rw [RWRS.walkLaw, LatticeProb.Graph.walkLaw,
    show RWRS.driverLaw = LatticeProb.Graph.driverLaw from rfl]
  congr 1
  funext ω
  funext k
  exact walkPath_eq_lib x ω k

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
theorem exitTime_eq_lib (C : Set V) (X : ℕ → V) :
    RWRS.exitTime C X = LatticeProb.Graph.exitTime C X := rfl

/-- **The voltage identity.**  The expected payoff at the exit from `C` is the
sum of the killed Green function against the excess mass. -/
theorem integral_payoffAtExit_eq (hdeg : ∀ v : V, 0 < G.degree v) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (ξ : V → ℝ) (o : V) :
    ∫ X, RWRS.payoffAtExit G ξ (C : Set V) X ∂(RWRS.walkLaw G o)
      = ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * ξ v := by
  classical
  have hfun : (fun X : ℕ → V => RWRS.payoffAtExit G ξ (C : Set V) X)
      = fun X : ℕ → V =>
        ∑ k ∈ Finset.range (LatticeProb.Graph.exitTime (C : Set V) X).toNat,
          (fun v : V => ξ v / G.degree v) (X k) := by
    funext X
    rw [RWRS.payoffAtExit, RWRS.payoff, exitTime_eq_lib]
  rw [walkLaw_eq_lib o, hfun]
  rw [LatticeProb.Graph.integral_sum_range_exitNat hdeg C hesc (fun v : V => ξ v / G.degree v) o]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hg := killedGreenReal_eq_tsum_of_escape C hesc o v
  have hd : (G.degree v : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (hdeg v).ne'
  rw [hg]
  field_simp

end RWRS.Support
