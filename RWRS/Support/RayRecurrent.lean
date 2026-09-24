/-
The ray with the gadgets is recurrent.

The graph is one-ended: the only edge leaving the set of vertices at ray level
at most `k` is the backbone edge from `r_k` to `r_{k+1}`, because a gadget is
attached at a single ray vertex and therefore lies entirely at that vertex's
level.  The backbone edges are `k` pairwise disjoint cutsets of one edge each
inside the set at level `k`, so the series law bounds the effective resistance
from the root below by `k/2`, and an unbounded effective resistance is
recurrence.
-/
import RWRS.Support.RayDegree
import RWRS.Support.SeriesLaw

namespace RWRS.Support

open scoped Classical
open LatticeProb.Network

variable {B : ℕ} {L : ℕ → ℕ} {m s : ℕ → ℕ}

theorem gadgetSites_finite (M : ℕ) : (gadgetSites B L M).Finite := by
  classical
  refine Set.Finite.subset
    ((wordsLe B M ×ˢ Finset.range (maxLen L M + 1)).finite_toSet) ?_
  rintro v ⟨hval, hlen⟩
  refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨mem_wordsLe hlen, Finset.mem_range.2 ?_⟩)
  rcases hval with h0 | ⟨-, -, h2⟩
  · omega
  · have := le_maxLen L (j := v.1.length) hlen
    omega

instance gadgetSites_fintype (M : ℕ) : Finite (gadgetSites B L M) :=
  (gadgetSites_finite M).to_subtype

/-- The distance scale at which a vertex sits along the ray. -/
def rayLevel (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) : RayV B L m → ℕ
  | Sum.inl i => i
  | Sum.inr p => s p.1

/-- The vertices of the ray graph at ray level at most `k`. -/
def rayBallSet (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (k : ℕ) : Set (RayV B L m) :=
  {x | rayLevel B L m s x ≤ k}

theorem rayBallSet_finite (hs : StrictMono s) (k : ℕ) : (rayBallSet B L m s k).Finite := by
  classical
  refine Set.Finite.subset (Set.Finite.union
    (Set.Finite.image Sum.inl (Set.finite_Iic k))
    (Set.Finite.biUnion (Set.finite_Iic k)
      (fun j _ => Set.finite_range (rayEmb B L m s j)))) ?_
  rintro (i | ⟨j, ⟨v, hv⟩⟩) hx
  · exact Or.inl ⟨i, hx, rfl⟩
  · have hj : s j ≤ k := hx
    have hjle : j ≤ k := le_trans (hs.le_apply (x := j)) hj
    exact Or.inr (Set.mem_biUnion (show j ∈ Set.Iic k from hjle)
      ⟨v, rayEmb_of_ne (s := s) hv⟩)

noncomputable def rayBall (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (hs : StrictMono s) (k : ℕ) :
    Finset (RayV B L m) := (rayBallSet_finite (B := B) (L := L) (m := m) hs k).toFinset

theorem mem_rayBall (hs : StrictMono s) (k : ℕ) (x : RayV B L m) :
    x ∈ rayBall B L m s hs k ↔ rayLevel B L m s x ≤ k := by
  rw [rayBall, Set.Finite.mem_toFinset]
  rfl

theorem rayBall_mono (hs : StrictMono s) {a b : ℕ} (hab : a ≤ b) :
    rayBall B L m s hs a ⊆ rayBall B L m s hs b := by
  intro x hx
  rw [mem_rayBall] at hx ⊢
  omega

theorem rayLevel_adj_le {x y : RayV B L m} (h : (rayGraph B L m s).Adj x y) :
    rayLevel B L m s y ≤ rayLevel B L m s x + 1 := by
  rcases h with ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨k, v, w, hvw, h1, h2⟩
  · subst h1; subst h2; exact le_rfl
  · subst h1; subst h2; simp only [rayLevel, rayPt]; omega
  · subst h1; subst h2
    by_cases hv : v = gadgetRoot B L (m k) <;> by_cases hw : w = gadgetRoot B L (m k) <;>
      simp [rayEmb, hv, hw, rayLevel]

theorem rayLevel_adj_eq_succ {x y : RayV B L m} (h : (rayGraph B L m s).Adj x y)
    (hlt : rayLevel B L m s x < rayLevel B L m s y) :
    ∃ i, x = Sum.inl i ∧ y = Sum.inl (i + 1) := by
  rcases h with ⟨i, h1, h2⟩ | ⟨i, h1, h2⟩ | ⟨k, v, w, hvw, h1, h2⟩
  · exact ⟨i, h1, h2⟩
  · subst h1; subst h2; simp [rayLevel, rayPt] at hlt
  · subst h1; subst h2
    exfalso
    by_cases hv : v = gadgetRoot B L (m k) <;> by_cases hw : w = gadgetRoot B L (m k) <;>
      simp [rayEmb, hv, hw, rayLevel] at hlt

section
variable [inst : (rayGraph B L m s).LocallyFinite]

theorem cutPairs_rayBall (hs : StrictMono s) (k : ℕ) :
    cutPairs (rayGraph B L m s) (rayBall B L m s hs k)
      = {((Sum.inl k : RayV B L m), (Sum.inl (k + 1) : RayV B L m))} := by
  classical
  ext p
  rw [mem_cutPairs, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [mem_rayBall] at h1
    rw [mem_rayBall] at h2
    have hle := rayLevel_adj_le h3
    have hlt : rayLevel B L m s p.1 < rayLevel B L m s p.2 := by omega
    obtain ⟨i, hi1, hi2⟩ := rayLevel_adj_eq_succ h3 hlt
    have hik : i = k := by
      have e1 : rayLevel B L m s p.1 = i := by rw [hi1]; rfl
      have e2 : rayLevel B L m s p.2 = i + 1 := by rw [hi2]; rfl
      omega
    subst hik
    exact Prod.ext hi1 hi2
  · rintro rfl
    refine ⟨?_, ?_, Or.inl ⟨k, rfl, rfl⟩⟩
    · rw [mem_rayBall]; exact le_rfl
    · rw [mem_rayBall]; simp [rayLevel]

theorem recurrent_rayGraph (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s) :
    RWRS.Recurrent (rayGraph B L m s) (rayPt B L m 0) := by
  classical
  haveI : Infinite (RayV B L m) := infinite_rayV
  have hG : (rayGraph B L m s).Connected := rayGraph_connected hL
  refine recurrent_of_killedGreen_unbounded hG _ fun M => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * M)
  refine ⟨rayBall B L m s hs N, ?_, ?_⟩
  · intro x
    obtain ⟨w⟩ := hG.preconnected x (Sum.inl (N + 1))
    refine ⟨Sum.inl (N + 1), w, ?_⟩
    rw [Finset.mem_coe, mem_rayBall]
    simp [rayLevel]
  · have hq : (Sum.inl (N + 1) : RayV B L m) ∉ rayBall B L m s hs N := by
      rw [mem_rayBall]; simp [rayLevel]
    have ho : (rayPt B L m 0 : RayV B L m) ∈ rayBall B L m s hs N := by
      rw [mem_rayBall]; exact Nat.zero_le _
    have hmain := nashWilliams_upto hG (rayBall B L m s hs N) ho hq N
      (fun k => rayBall B L m s hs k) (fun k _ => by rw [mem_rayBall]; exact Nat.zero_le _)
      (fun k hk => rayBall_mono hs (le_of_lt hk))
      (fun k _ x hx y hy => by
        rw [mem_rayBall] at hx ⊢
        have := rayLevel_adj_le ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)
        omega)
      (fun a b hab _ => rayBall_mono hs hab)
    have hsum : ∑ k ∈ Finset.range N,
        1 / ((cutPairs (rayGraph B L m s) (rayBall B L m s hs k)).card : ℝ) = (N : ℝ) := by
      have hterm : ∀ k ∈ Finset.range N,
          1 / ((cutPairs (rayGraph B L m s) (rayBall B L m s hs k)).card : ℝ) = 1 := by
        intro k _
        rw [cutPairs_rayBall hs k, Finset.card_singleton]
        norm_num
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        mul_one]
    rw [hsum] at hmain
    rw [killedGreenReal_eq_lib]
    have : LatticeProb.Graph.killedGreenReal (rayGraph B L m s)
        ((rayBall B L m s hs N : Finset (RayV B L m)) : Set (RayV B L m))
        (rayPt B L m 0) (rayPt B L m 0)
        = effRes (rayGraph B L m s) (rayBall B L m s hs N) (rayPt B L m 0) := rfl
    rw [this]
    linarith
end

end RWRS.Support
