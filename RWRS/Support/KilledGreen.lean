/-
The killed Green function as a voltage, on a graph that need not be connected.

The shared library proves the boundary value problem `eq:gC-PDE` for `g_C(o,·)`
on a connected graph: it vanishes off `C`, is harmonic on `C` away from the
source, and has Laplacian `-1` at the source.  The tree of pipes of
`ssec:comb-estimates` is a graph on all pairs `(w,i)`, and a pair that carries no
meaning is an isolated vertex, so that graph is not connected and the library's
statements do not apply to it.  Connectivity is not what the proofs use: what
they use is that the walk leaves `C`, and that the vertices of `C` are not
isolated.  Both hold on the tree of pipes.  The two hypotheses

    hesc : ∀ x : V, ∃ (q : V) (p : G.Walk x q), q ∉ C
    hdeg : ∀ v ∈ C, 0 < G.degree v

replace connectivity here, and the library's own lemmas that do not mention it
carry the proofs.
-/
import RWRS.Basic
import LatticeProb.Network.KilledGreen

namespace RWRS.Support

open LatticeProb.Network LatticeProb.Graph
open scoped ENNReal
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The two constructions agree -/

theorem killedHeat_eq_lib (C : Set V) : ∀ (k : ℕ) (x y : V),
    RWRS.killedHeat G C k x y = LatticeProb.Graph.killedHeat G C k x y := by
  classical
  intro k
  induction k with
  | zero => intro x y; rfl
  | succ k ih =>
      intro x y
      have hfun : (fun z => RWRS.killedHeat G C k z y)
          = fun z => LatticeProb.Graph.killedHeat G C k z y := by
        funext z; exact ih z y
      show (if x ∈ C then RWRS.walkOp G (fun z => RWRS.killedHeat G C k z y) x else 0)
        = if x ∈ C then walkOp G (fun z => LatticeProb.Graph.killedHeat G C k z y) x else 0
      rw [hfun]

theorem killedGreen_eq_lib (C : Set V) (x y : V) :
    RWRS.killedGreen G C x y = LatticeProb.Graph.killedGreen G C x y := by
  rw [RWRS.killedGreen, LatticeProb.Graph.killedGreen]
  congr 1
  exact tsum_congr fun k => by rw [killedHeat_eq_lib C k x y]

theorem killedGreenReal_eq_lib (C : Set V) (x y : V) :
    RWRS.killedGreenReal G C x y = LatticeProb.Graph.killedGreenReal G C x y := by
  rw [RWRS.killedGreenReal, LatticeProb.Graph.killedGreenReal, killedGreen_eq_lib]

/-! ### Escape in place of connectivity -/

variable (C : Finset V)

theorem exists_uniform_survival_le_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) :
    ∃ (N : ℕ) (θ : ℝ), 0 < N ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ x : V, survival G C N x ≤ θ := by
  classical
  have hlen : ∀ x : V, ∃ n : ℕ, ∃ e : ℝ, 0 < e ∧ survival G C n x ≤ 1 - e := by
    intro x
    obtain ⟨q, p, hq⟩ := hesc x
    obtain ⟨e, he, hle⟩ := exists_survival_lt C p hq
    exact ⟨p.length, e, he, hle⟩
  choose l e he hle using hlen
  by_cases hC : C.Nonempty
  · refine ⟨C.sup l + 1, C.sup' hC (fun x => survival G C (C.sup l + 1) x),
      Nat.succ_pos _, ?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hC
      exact le_trans (survival_nonneg C _ x) (Finset.le_sup' _ hx)
    · rw [Finset.sup'_lt_iff]
      intro x hx
      have h1 : survival G C (C.sup l + 1) x ≤ survival G C (l x) x :=
        survival_antitone C (by have := Finset.le_sup (f := l) hx; omega) x
      linarith [hle x, he x]
    · intro x
      by_cases hx : x ∈ C
      · exact Finset.le_sup' _ hx
      · rw [survival_of_not_mem hx]
        obtain ⟨y, hy⟩ := hC
        exact le_trans (survival_nonneg C _ y) (Finset.le_sup' _ hy)
  · refine ⟨1, 0, Nat.one_pos, le_refl 0, zero_lt_one, ?_⟩
    intro x
    rw [Finset.not_nonempty_iff_eq_empty] at hC
    rw [survival, hC, Finset.sum_empty]

theorem summable_killedHeat_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    Summable (fun k => LatticeProb.Graph.killedHeat G (C : Set V) k x v) := by
  classical
  by_cases hv : v ∈ C
  · obtain ⟨N, θ, hN, hθ0, hθ1, hθ⟩ := exists_uniform_survival_le_of_escape C hesc
    refine summable_of_sum_range_le (c := (N : ℝ) / (1 - θ))
      (fun k => killedHeat_nonneg _ k x v) (fun n => ?_)
    calc ∑ k ∈ Finset.range n, LatticeProb.Graph.killedHeat G (C : Set V) k x v
        ≤ ∑ k ∈ Finset.range n, survival G C k x :=
          Finset.sum_le_sum fun k _ => killedHeat_le_survival C hv k x
      _ ≤ (N : ℝ) / (1 - θ) := sum_range_survival_le hN hθ0 hθ1 hθ x n
  · have : (fun k => LatticeProb.Graph.killedHeat G (C : Set V) k x v) = fun _ => (0 : ℝ) := by
      funext k
      exact killedHeat_of_target_not_mem (by exact_mod_cast hv) k x
    rw [this]
    exact summable_zero

theorem killedGreenReal_eq_tsum_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    RWRS.killedGreenReal G (C : Set V) x v
      = (∑' k : ℕ, LatticeProb.Graph.killedHeat G (C : Set V) k x v) / G.degree v := by
  have hsum := summable_killedHeat_of_escape C hesc x v
  have hnn : ∀ k, 0 ≤ LatticeProb.Graph.killedHeat G (C : Set V) k x v :=
    fun k => killedHeat_nonneg _ k x v
  have h1 : (∑' k : ℕ, ENNReal.ofReal (LatticeProb.Graph.killedHeat G (C : Set V) k x v))
      = ENNReal.ofReal (∑' k : ℕ, LatticeProb.Graph.killedHeat G (C : Set V) k x v) :=
    (ENNReal.ofReal_tsum_of_nonneg hnn hsum).symm
  rw [killedGreenReal_eq_lib, LatticeProb.Graph.killedGreenReal,
    LatticeProb.Graph.killedGreen, h1, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (tsum_nonneg hnn), ENNReal.toReal_natCast]

theorem killedGreenReal_eq_zero_of_not_mem_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) {v : V} (hv : v ∉ C) (x : V) :
    RWRS.killedGreenReal G (C : Set V) x v = 0 := by
  rw [killedGreenReal_eq_tsum_of_escape C hesc x v]
  have : (fun k => LatticeProb.Graph.killedHeat G (C : Set V) k x v) = fun _ => (0 : ℝ) := by
    funext k
    exact killedHeat_of_target_not_mem (by exact_mod_cast hv) k x
  rw [this, tsum_zero, zero_div]

theorem killedGreenReal_nonneg_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    0 ≤ RWRS.killedGreenReal G (C : Set V) x v := by
  rw [killedGreenReal_eq_tsum_of_escape C hesc x v]
  exact div_nonneg (tsum_nonneg fun k => killedHeat_nonneg _ k x v) (Nat.cast_nonneg _)

theorem killedGreenReal_symm_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    RWRS.killedGreenReal G (C : Set V) x v = RWRS.killedGreenReal G (C : Set V) v x := by
  rw [killedGreenReal_eq_tsum_of_escape C hesc x v,
    killedGreenReal_eq_tsum_of_escape C hesc v x, ← tsum_div_const, ← tsum_div_const]
  exact tsum_congr fun k => killedKer_symm (G := G) (C : Set V) k x v

theorem killedGreenReal_eq_reversed_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    RWRS.killedGreenReal G (C : Set V) x v
      = (∑' k : ℕ, LatticeProb.Graph.killedHeat G (C : Set V) k v x) / G.degree x := by
  rw [killedGreenReal_symm_of_escape C hesc x v,
    killedGreenReal_eq_tsum_of_escape C hesc v x]

theorem sum_tsum_killedHeat_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) (x : V) {v : V} (hv : v ∈ C) :
    ∑ w ∈ G.neighborFinset v, (∑' k : ℕ, LatticeProb.Graph.killedHeat G (C : Set V) k w x)
      = (G.degree v : ℝ) *
          ((∑' k : ℕ, LatticeProb.Graph.killedHeat G (C : Set V) k v x)
            - LatticeProb.Graph.killedHeat G (C : Set V) 0 v x) := by
  have hdv : 0 < G.degree v := hdeg v hv
  have hsum : ∀ w : V, Summable (fun k => LatticeProb.Graph.killedHeat G (C : Set V) k w x) :=
    fun w => summable_killedHeat_of_escape C hesc w x
  have hex : ∑ w ∈ G.neighborFinset v,
        (∑' k : ℕ, LatticeProb.Graph.killedHeat G (C : Set V) k w x)
      = ∑' k : ℕ, ∑ w ∈ G.neighborFinset v,
          LatticeProb.Graph.killedHeat G (C : Set V) k w x :=
    (Summable.tsum_finsetSum (fun w _ => hsum w)).symm
  have hstep : ∀ k : ℕ, ∑ w ∈ G.neighborFinset v,
        LatticeProb.Graph.killedHeat G (C : Set V) k w x
      = (G.degree v : ℝ) * LatticeProb.Graph.killedHeat G (C : Set V) (k + 1) v x := by
    intro k
    rw [killedHeat_succ, if_pos (by exact_mod_cast hv : v ∈ (C : Set V)),
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hdv.ne')]
  rw [hex, tsum_congr hstep, tsum_mul_left, (hsum v).tsum_eq_zero_add]
  ring

/-- **The boundary value problem `eq:gC-PDE`.**  Inside `C`, the Laplacian of
`g_C(o,·)` is `-1` at the source and `0` elsewhere. -/
theorem laplacian_killedGreenReal_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C) {v : V} (hv : v ∈ C) :
    RWRS.laplacian G (RWRS.killedGreenReal G (C : Set V) o) v
      = -(if v = o then (1 : ℝ) else 0) := by
  classical
  have hdo : 0 < G.degree o := hdeg o ho
  have hdoR : (G.degree o : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdo.ne'
  have hu : ∀ w : V, RWRS.killedGreenReal G (C : Set V) o w
      = (∑' k : ℕ, LatticeProb.Graph.killedHeat G (C : Set V) k w o) / (G.degree o : ℝ) :=
    fun w => killedGreenReal_eq_reversed_of_escape C hesc o w
  have hsum := sum_tsum_killedHeat_of_escape C hesc hdeg o hv
  have hzero : LatticeProb.Graph.killedHeat G (C : Set V) 0 v o
      = if v = o then (1 : ℝ) else 0 := by
    rw [killedHeat_zero, if_pos (by exact_mod_cast hv : v ∈ (C : Set V))]
  rw [RWRS.laplacian]
  simp only [hu]
  rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul, ← Finset.sum_div, hsum, hzero]
  by_cases hvo : v = o
  · subst hvo
    rw [if_pos rfl]
    field_simp
    ring
  · rw [if_neg hvo]
    field_simp
    ring

/-- The killed Green function is harmonic on `C` away from the source. -/
theorem harmonic_killedGreenReal_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C) {v : V} (hv : v ∈ C)
    (hvo : v ≠ o) :
    RWRS.laplacian G (RWRS.killedGreenReal G (C : Set V) o) v = 0 := by
  rw [laplacian_killedGreenReal_of_escape C hesc hdeg ho hv, if_neg hvo]
  norm_num

/-- The unit source at `o`. -/
theorem laplacian_killedGreenReal_source_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C) :
    RWRS.laplacian G (RWRS.killedGreenReal G (C : Set V) o) o = -1 := by
  rw [laplacian_killedGreenReal_of_escape C hesc hdeg ho ho, if_pos rfl]

end RWRS.Support
