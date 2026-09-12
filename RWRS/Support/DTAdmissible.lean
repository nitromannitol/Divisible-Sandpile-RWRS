/-
The admissible set of `prop:doubly-transient-really-general` is co-finite.

Step 1 selects the centres of its traps along the walk, and a new centre is
admissible when it is far from the trap sets already used and its total Green
interaction with them is at most one.  Both restrictions delete a finite set of
vertices: the first because balls are finite, the second because double
transience makes `∑_z g(v,z)^2` finite for every `v`, so only finitely many `z`
carry a Green weight above a positive threshold.  The walk therefore reaches the
admissible set almost surely.
-/
import RWRS.Support.DTPotential

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **Only finitely many vertices carry a Green weight above a threshold.** -/
theorem finite_green_ge (hdt : RWRS.DoublyTransient G) (v : V) {c : ℝ≥0∞} (hc : c ≠ 0) :
    {z : V | c ≤ RWRS.green G v z}.Finite := by
  have h := ENNReal.finite_const_le_of_tsum_ne_top (a := fun z : V => RWRS.green G v z ^ 2)
    (hdt v) (ε := c ^ 2) (pow_ne_zero 2 hc)
  refine h.subset fun z hz => ?_
  have hz' : c ≤ RWRS.green G v z := hz
  exact pow_le_pow_left' hz' 2

/-- **The Green interaction with a finite set exceeds one only finitely often.** -/
theorem finite_interaction_gt (hdt : RWRS.DoublyTransient G) (F : Finset V) :
    {z : V | 1 < ∑ v ∈ F, RWRS.green G v z}.Finite := by
  classical
  have hcardne : ((F.card : ℝ≥0∞))⁻¹ ≠ 0 := by
    rw [Ne, ENNReal.inv_eq_zero]
    exact ENNReal.natCast_ne_top F.card
  have key : {z : V | 1 < ∑ v ∈ F, RWRS.green G v z}
      ⊆ ⋃ v ∈ (F : Set V), {z : V | ((F.card : ℝ≥0∞))⁻¹ ≤ RWRS.green G v z} := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    rcases F.eq_empty_or_nonempty with rfl | hne
    · simp at hz
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcon
    have hle : ∀ v ∈ F, RWRS.green G v z ≤ ((F.card : ℝ≥0∞))⁻¹ := by
      intro v hv
      exact (by simpa using hcon v hv : RWRS.green G v z < ((F.card : ℝ≥0∞))⁻¹).le
    have hsum : ∑ v ∈ F, RWRS.green G v z ≤ (F.card : ℝ≥0∞) * ((F.card : ℝ≥0∞))⁻¹ := by
      calc ∑ v ∈ F, RWRS.green G v z ≤ ∑ _v ∈ F, ((F.card : ℝ≥0∞))⁻¹ := Finset.sum_le_sum hle
        _ = (F.card : ℝ≥0∞) * ((F.card : ℝ≥0∞))⁻¹ := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hcard0 : (F.card : ℝ≥0∞) ≠ 0 := by
      simpa using (Finset.card_pos.2 hne).ne'
    rw [ENNReal.mul_inv_cancel hcard0 (ENNReal.natCast_ne_top F.card)] at hsum
    exact absurd hsum (not_le.2 hz)
  exact Set.Finite.subset (Set.Finite.biUnion F.finite_toSet
    fun v _ => finite_green_ge hdt v hcardne) key

/-! ### The admissible set -/

/-- `z` is admissible for the used set `F`: it lies more than `2r` from every site
of `F` and its total Green interaction with `F` is at most one. -/
def Admissible (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (F : Finset V) (z : V) : Prop :=
  (∀ w ∈ F, ¬ G.edist z w ≤ (2 * r : ℕ)) ∧ ∑ v ∈ F, RWRS.green G v z ≤ 1

/-- **Only finitely many vertices fail to be admissible.** -/
theorem finite_not_admissible (hdt : RWRS.DoublyTransient G) (r : ℕ) (F : Finset V) :
    {z : V | ¬ Admissible G r F z}.Finite := by
  classical
  have hcover : {z : V | ¬ Admissible G r F z}
      ⊆ (⋃ w ∈ (F : Set V), RWRS.closedBall G w (2 * r))
        ∪ {z : V | 1 < ∑ v ∈ F, RWRS.green G v z} := by
    intro z hz
    unfold Admissible at hz
    simp only [not_and_or, not_forall, not_not] at hz
    rcases hz with h | h
    · obtain ⟨w, hw, hle⟩ := h
      refine Or.inl ?_
      simp only [Set.mem_iUnion]
      exact ⟨w, hw, hle⟩
    · exact Or.inr (lt_of_not_ge h)
  refine Set.Finite.subset
    (Set.Finite.union
      (Set.Finite.biUnion F.finite_toSet fun w _ => finite_closedBall w (2 * r))
      (finite_interaction_gt hdt F)) hcover

end RWRS.Support
