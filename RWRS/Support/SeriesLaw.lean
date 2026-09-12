import RWRS.Support.Transience
import LatticeProb.Network.Series

namespace RWRS.Support

open scoped Classical
open LatticeProb.Network LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem killedHeat_le_heat (C : Set V) :
    ∀ (k : ℕ) (x y : V), RWRS.killedHeat G C k x y ≤ RWRS.heat G k x y := by
  intro k
  induction k with
  | zero =>
      intro x y
      by_cases hx : x ∈ C
      · simp only [RWRS.killedHeat, RWRS.heat, if_pos hx]
        exact le_refl _
      · simp only [RWRS.killedHeat, RWRS.heat, if_neg hx]
        split <;> norm_num
  | succ k ih =>
      intro x y
      by_cases hx : x ∈ C
      · simp only [RWRS.killedHeat, RWRS.heat, if_pos hx]
        refine div_le_div_of_nonneg_right ?_ ?_ |>.trans_eq rfl
        · exact Finset.sum_le_sum fun z _ => ih z y
        · exact Nat.cast_nonneg _
      · simp only [RWRS.killedHeat, if_neg hx]
        exact RWRS.Support.heat_nonneg (k + 1) x y

theorem killedGreen_le_green (C : Set V) (x y : V) :
    RWRS.killedGreen G C x y ≤ RWRS.green G x y := by
  rw [RWRS.killedGreen, RWRS.green]
  refine ENNReal.div_le_div_right ?_ _
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  exact killedHeat_le_heat C k x y

/-- **Recurrence from an unbounded effective resistance.**  If the killed Green
function at the source is unbounded over the finite escapable sets, the walk is
recurrent there. -/
theorem recurrent_of_killedGreen_unbounded [Infinite V] (_hG : G.Connected) (o : V)
    (h : ∀ M : ℝ, ∃ C : Finset V,
        (∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V)) ∧
        M ≤ RWRS.killedGreenReal G (C : Set V) o o) :
    RWRS.Recurrent G o := by
  by_contra hrec
  rw [RWRS.Recurrent] at hrec
  obtain ⟨C, hesc, hM⟩ := h ((RWRS.green G o o).toReal + 1)
  have hle : RWRS.killedGreen G (C : Set V) o o ≤ RWRS.green G o o :=
    killedGreen_le_green (C : Set V) o o
  have hne : RWRS.killedGreen G (C : Set V) o o ≠ ⊤ := ne_top_of_le_ne_top hrec hle
  have hreal : RWRS.killedGreenReal G (C : Set V) o o ≤ (RWRS.green G o o).toReal :=
    ENNReal.toReal_mono hrec hle
  linarith

/-! ### The series law over a finite chain -/

/-- The series law of `LatticeProb.Network.nashWilliams_nested`, with the chain
asked for only up to the horizon `L`.  This is what a chain that exhausts an
infinite graph supplies: the sets grow forever, so no single finite set contains
them all, and the horizon has to be cut. -/
theorem nashWilliams_upto (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C)
    (hq : q ∉ C) (L : ℕ) (U : ℕ → Finset V) (hoU : ∀ k < L, o ∈ U k)
    (hUC : ∀ k < L, U k ⊆ C)
    (hgrow : ∀ k < L, ∀ x ∈ U k, G.neighborFinset x ⊆ U (k + 1))
    (hmono : ∀ a b, a ≤ b → b < L → U a ⊆ U b) :
    ∑ k ∈ Finset.range L, 1 / ((cutPairs G (U k)).card : ℝ) ≤ 2 * effRes G C o := by
  classical
  have hdisj : ((Finset.range L : Finset ℕ) : Set ℕ).PairwiseDisjoint
      fun k => cutPairs G (U k) := by
    intro k hk l hl hkl
    have key : ∀ a b : ℕ, a < b → b < L → Disjoint (cutPairs G (U a)) (cutPairs G (U b)) := by
      intro a b hab hbL
      refine Finset.disjoint_left.mpr fun p hpa hpb => ?_
      obtain ⟨ha1, ha2, ha3⟩ := mem_cutPairs.mp hpa
      obtain ⟨-, hb2, -⟩ := mem_cutPairs.mp hpb
      refine hb2 (hmono (a + 1) b (by omega) hbL ?_)
      exact hgrow a (by omega) p.1 ha1 ((SimpleGraph.mem_neighborFinset _ _ _).mpr ha3)
    simp only [Finset.coe_range, Set.mem_Iio] at hk hl
    simp only [Function.onFun]
    rcases lt_or_gt_of_ne hkl with h | h
    · exact key k l h hl
    · exact (key l k h hk).symm
  have hcut : ∀ k ∈ Finset.range L,
      1 ≤ ∑ p ∈ cutPairs G (U k),
        current G (unitCond G) (LatticeProb.Graph.killedGreenReal G (C : Set V) o) p.1 p.2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [← flux_eq_sum_cutPairs]
    refine le_of_eq (flux_eq_one isCond_unitCond _ (U k) (hoU k hk) ?_).symm
    intro x hx
    rw [netLaplacian_unitCond]
    by_cases hxo : x = o
    · subst hxo
      rw [if_pos rfl]
      exact laplacian_killedGreenReal_source hG C ho hq
    · rw [if_neg hxo, neg_zero]
      exact harmonic_killedGreenReal hG C ho hq (by exact_mod_cast hUC k hk hx) hxo
  have hmain := nashWilliams_le_effRes hG C ho hq (Finset.range L) (fun k => cutPairs G (U k))
    (fun k hk => cutPairs_subset_pairs (hUC k (Finset.mem_range.1 hk))) hdisj
    (fun k _ p hp => by
      rw [unitCond, if_pos (mem_cutPairs.mp hp).2.2]
      norm_num) hcut
  refine le_trans (le_of_eq ?_) hmain
  exact Finset.sum_congr rfl fun k _ => by rw [sum_unitCond_cutPairs]

end RWRS.Support
