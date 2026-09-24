/-
The trap family of `def:trap-family` as data, and the geometry that makes the
trap sets of far-apart centres disjoint.
-/
import RWRS.Support.DTBlocks

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

/-- **The uniform local trap condition as a choice of trap sets.** -/
theorem exists_trapFamily (htrap : RWRS.UniformLocalTrap G) (L : ℝ) (hL : 0 < L) :
    ∃ (r M : ℕ) (C : V → Finset V), ∀ y : V,
      y ∈ C y ∧ ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r ∧ (C y).card ≤ M ∧
        (G.induce ((C y : Finset V) : Set V)).Connected ∧
        ENNReal.ofReal L ≤ RWRS.thetaExit G (((C y : Finset V) : Set V)) y := by
  obtain ⟨r, M, h⟩ := htrap L hL
  choose C hC using h
  exact ⟨r, M, C, hC⟩

omit [G.LocallyFinite] in
/-- **Trap sets of centres more than `2r` apart are disjoint.** -/
theorem disjoint_trap_of_far {r : ℕ} {D E : Finset V} {y z : V}
    (hD : (D : Set V) ⊆ RWRS.closedBall G y r) (hE : (E : Set V) ⊆ RWRS.closedBall G z r)
    (h : ¬ G.edist y z ≤ (2 * r : ℕ)) : Disjoint (D : Set V) (E : Set V) := by
  rw [Set.disjoint_left]
  intro v hv hv'
  have h1 : G.edist v y ≤ r := hD hv
  have h2 : G.edist v z ≤ r := hE hv'
  have htri : G.edist y z ≤ G.edist y v + G.edist v z := SimpleGraph.edist_triangle
  have h1' : G.edist y v ≤ r := by rw [SimpleGraph.edist_comm]; exact h1
  refine h ?_
  have hsum : G.edist y v + G.edist v z ≤ r + r := add_le_add h1' h2
  have hcast : (2 * r : ℕ) = r + r := by ring
  rw [hcast]
  exact le_trans htri hsum

/-- **The trap event has probability at least `p₀^M`.** -/
theorem measure_trapEvent_ge (ν : Measure ℝ) [IsProbabilityMeasure ν] {C : Finset V} {M : ℕ}
    (hcard : C.card ≤ M) (ε : ℝ) :
    ν (Set.Iic (-ε)) ^ M ≤ RWRS.iidLaw V ν (trapEvent C ε) := by
  rw [measure_trapEvent]
  exact pow_le_pow_right_of_le_one' prob_le_one hcard

end RWRS.Support
