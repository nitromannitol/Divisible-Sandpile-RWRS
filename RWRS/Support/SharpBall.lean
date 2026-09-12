/-
The ball of `lem:moment-sharpness`: it is reached within its radius, and
hypothesis (A3) reads on its cardinality.
-/
import RWRS.Support.BallWalk
import RWRS.Support.Countable
import RWRS.Setting

namespace RWRS.Support

open scoped Classical ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The ball of radius `r` is reached in `r` steps.** -/
theorem closedBall_subset_reach (o : V) :
    ∀ r : ℕ, RWRS.closedBall G o r ⊆ (reach G o r : Set V) := by
  intro r
  induction r with
  | zero =>
      intro v hv
      have hv' : G.edist v o ≤ (0 : ℕ∞) := by simpa [RWRS.closedBall] using hv
      have h0 : G.edist v o = 0 := le_antisymm hv' bot_le
      have : v = o := SimpleGraph.edist_eq_zero_iff.1 h0
      subst this
      simpa using self_mem_reach (G := G) v 0
  | succ r ih =>
      intro v hv
      by_cases hr : v ∈ RWRS.closedBall G o r
      · exact reach_subset_succ o r (ih hr)
      · have hle : G.edist v o ≤ ((r + 1 : ℕ) : ℕ∞) := hv
        have hgt : ((r : ℕ) : ℕ∞) < G.edist v o := not_le.1 hr
        have heq : G.edist v o = ((r + 1 : ℕ) : ℕ∞) := by
          refine le_antisymm hle ?_
          have : ((r : ℕ) : ℕ∞) + 1 ≤ G.edist v o := Order.add_one_le_of_lt hgt
          rwa [show ((r + 1 : ℕ) : ℕ∞) = ((r : ℕ) : ℕ∞) + 1 by push_cast; ring]
        obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe heq
        cases p with
        | nil => simp at hp
        | @cons _ w _ hadj q =>
            have hq : q.length = r := by
              simp only [SimpleGraph.Walk.length_cons] at hp
              omega
            have hwr : w ∈ RWRS.closedBall G o r := by
              have := q.edist_le
              rw [hq] at this
              exact this
            have hwreach : w ∈ reach G o r := ih hwr
            rw [reach]
            exact Finset.mem_biUnion.mpr ⟨w, hwreach,
              Finset.mem_insert_of_mem (by simpa using hadj.symm)⟩

/-- The ball as a `Finset`. -/
noncomputable def ballFinset (G : SimpleGraph V) [G.LocallyFinite] (o : V) (r : ℕ) : Finset V :=
  (finite_closedBall (G := G) o r).toFinset

theorem mem_ballFinset {o v : V} {r : ℕ} :
    v ∈ ballFinset G o r ↔ v ∈ RWRS.closedBall G o r := by
  rw [ballFinset, Set.Finite.mem_toFinset]

theorem ballFinset_subset_reach (o : V) (r : ℕ) : ballFinset G o r ⊆ reach G o r := by
  intro v hv
  exact closedBall_subset_reach (G := G) o r (mem_ballFinset.1 hv)

/-- **Hypothesis (A3) on the cardinality of the ball.** -/
theorem card_ballFinset_ge {o : V} {c d_f : ℝ} (hA3 : RWRS.VolumeGrowthLower G o c d_f)
    {r : ℕ} (hr : 1 ≤ r) : c * (r : ℝ) ^ d_f ≤ ((ballFinset G o r).card : ℝ) := by
  have h := hA3 r hr
  have hcard : (RWRS.closedBall G o r).encard = ((ballFinset G o r).card : ℕ∞) := by
    rw [ballFinset, Set.Finite.encard_eq_coe_toFinset_card]
  rw [hcard] at h
  have h2 : ENNReal.ofReal (c * (r : ℝ) ^ d_f) ≤ ENNReal.ofReal (((ballFinset G o r).card : ℝ)) := by
    refine le_trans h (le_of_eq ?_)
    simp [ENNReal.ofReal_natCast]
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  exact this

end RWRS.Support
