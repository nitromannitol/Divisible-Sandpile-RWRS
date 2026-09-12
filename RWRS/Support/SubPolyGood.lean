/-
The scenery levels and the good-walk event of `prop:poly-growth`.

`rwrs.tex:1267` fixes the level of the site `v` at `M_0 ∨ dist(o,v)^β`, and
`rwrs.tex:1288` fixes the good-walk event of the `k`-th block as the
intersection of the local-time event of `lem:good-walk` with the displacement
event `τ_{B(o,R_N)} > N`.  On that event the trajectory stays inside the ball of
radius `R_N` up to time `N`, so every level it meets is at most
`M_0 ∨ R_N^β`; off it the trajectory is still inside the ball of radius `N`,
because a walk moves one step at a time, so every level it meets is at most
`M_0 ∨ N^β`.  Those two bounds are the two regimes of Step 5.
-/
import RWRS.Support.SubPolyBound

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V}

/-- The level of a site: `M_0 ∨ dist(o,v)^β`. -/
noncomputable def polyLevel (G : SimpleGraph V) (o : V) (M0 β : ℝ) (v : V) : ℝ :=
  max M0 (((G.edist v o).toNat : ℝ) ^ β)

theorem le_polyLevel (G : SimpleGraph V) (o : V) (M0 β : ℝ) (v : V) :
    M0 ≤ polyLevel G o M0 β v := le_max_left _ _

theorem neg_le_polyLevel {M M0 : ℝ} (hM : -M ≤ M0) (β : ℝ) (o v : V) :
    -M ≤ polyLevel G o M0 β v := le_trans hM (le_polyLevel G o M0 β v)

/-- Inside a ball the level is at most the level of the radius. -/
theorem polyLevel_le_of_edist_le {M0 β : ℝ} (hβ : 0 ≤ β) {o v : V} {R : ℕ}
    (h : G.edist v o ≤ (R : ℕ∞)) : polyLevel G o M0 β v ≤ max M0 ((R : ℝ) ^ β) := by
  have hR : (G.edist v o).toNat ≤ R := by
    have hne : G.edist v o ≠ ⊤ := by
      intro hc
      rw [hc] at h
      exact absurd h (by simp)
    have := ENat.toNat_le_toNat h (by simp)
    simpa using this
  have hcast : (((G.edist v o).toNat : ℕ) : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  exact max_le_max le_rfl (Real.rpow_le_rpow (Nat.cast_nonneg _) hcast hβ)

variable [G.LocallyFinite]

/-- **The good-walk event of `prop:poly-growth`**: the local times are small and
the trajectory has not left the ball of radius `R` by time `2^{k+1}`. -/
def polyGood (G : SimpleGraph V) [G.LocallyFinite] (o : V) (α δ : ℝ)
    (k R : ℕ) : Set (ℕ → V) :=
  RWRS.goodWalk α δ k ∩
    {X : ℕ → V | ((2 ^ (k + 1) : ℕ) : ℕ∞) < RWRS.exitTime (RWRS.closedBall G o R) X}

theorem polyGood_subset_goodWalk (o : V) (α δ : ℝ) (k R : ℕ) :
    polyGood G o α δ k R ⊆ RWRS.goodWalk (V := V) α δ k := Set.inter_subset_left

/-- On the good-walk event the trajectory stays inside the ball. -/
theorem mem_closedBall_of_polyGood {o : V} {α δ : ℝ} {k R : ℕ} {X : ℕ → V}
    (hX : X ∈ polyGood G o α δ k R) {j : ℕ} (hj : j < 2 ^ (k + 1)) :
    X j ∈ RWRS.closedBall G o R := by
  have hlt : ((j : ℕ) : ℕ∞) < RWRS.exitTime (RWRS.closedBall G o R) X := by
    refine lt_of_lt_of_le ?_ (le_of_lt hX.2)
    exact_mod_cast hj
  exact mem_of_lt_exitTime (C := RWRS.closedBall G o R) hlt

omit [G.LocallyFinite] in
/-- Off the good-walk event the trajectory is still inside the ball of radius
`2^{k+1}`, because a walk moves one step at a time. -/
theorem edist_le_of_lt
    {o : V} {X : ℕ → V} (hX : ∀ k : ℕ, G.edist (X k) o ≤ (k : ℕ∞)) {j N : ℕ} (hj : j < N) :
    G.edist (X j) o ≤ (N : ℕ∞) := by
  refine le_trans (hX j) ?_
  exact_mod_cast hj.le

variable [MeasurableSpace V]

/-- The complement of the good-walk event is contained in the union of the
local-time failure and the displacement failure. -/
theorem walkLaw_polyGood_compl_le (o x : V) (α δ : ℝ) (k R : ℕ) :
    RWRS.walkLaw G x (polyGood G o α δ k R)ᶜ
      ≤ RWRS.walkLaw G x (RWRS.goodWalk (V := V) α δ k)ᶜ
        + RWRS.walkLaw G x {X : ℕ → V |
            RWRS.exitTime (RWRS.closedBall G o R) X ≤ ((2 ^ (k + 1) : ℕ) : ℕ∞)} := by
  have hset : (polyGood G o α δ k R)ᶜ
      = (RWRS.goodWalk (V := V) α δ k)ᶜ ∪ {X : ℕ → V |
          RWRS.exitTime (RWRS.closedBall G o R) X ≤ ((2 ^ (k + 1) : ℕ) : ℕ∞)} := by
    unfold polyGood
    rw [Set.compl_inter]
    congr 1
    ext X
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rw [hset]
  exact measure_union_le _ _

/-- **The displacement estimate of Step 3**, read off hypothesis `H3`. -/
theorem walkLaw_exit_le {d_w C_disp c_disp : ℝ}
    (hH3 : RWRS.WalkDimensionBound G d_w C_disp c_disp) (o : V) {R N : ℕ}
    (hN : 1 ≤ N) (hR : 1 ≤ R) :
    RWRS.walkLaw G o {X : ℕ → V | RWRS.exitTime (RWRS.closedBall G o R) X ≤ (N : ℕ∞)}
      ≤ ENNReal.ofReal (C_disp
          * Real.exp (-c_disp * ((R : ℝ) ^ d_w / N) ^ (1 / (d_w - 1)))) :=
  hH3 o N R hN hR

end RWRS.Support
