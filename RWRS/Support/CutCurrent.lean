/-
Two properties of the voltage that `sec:recurrent-nonstab` uses before the
construction: Kirchhoff's node law across a separating cut, and the maximum
principle for dead ends.

The first is the sum of the Laplacian over a set: interior edges of the set
cancel in pairs, so what is left is the current leaving the set, and the
Laplacian sums to `-1` when the set contains the source and lies inside `C`.
The second says that a finite piece of `C` attached to the rest at a single
vertex and containing neither the source nor a boundary vertex carries the
constant voltage of its attachment point.
-/
import RWRS.Support.KilledGreen

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The interior edges cancel -/

omit [G.LocallyFinite] in
/-- The double sum of the increments over the ordered adjacent pairs inside a
finite set vanishes, because the swap of the pair changes its sign. -/
theorem sum_adj_antisym_zero (U : Finset V) (g : V → ℝ) :
    ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), (g y - g u) = 0 := by
  classical
  set P : Finset (V × V) := (U ×ˢ U).filter (fun p => G.Adj p.1 p.2) with hP
  have hrw : ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), (g y - g u)
      = ∑ p ∈ P, (g p.2 - g p.1) := by
    rw [hP, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_filter]
  have hswap : ∑ p ∈ P, (g p.2 - g p.1) = ∑ p ∈ P, (g p.1 - g p.2) := by
    refine Finset.sum_nbij' (i := Prod.swap) (j := Prod.swap) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
    · intro p hp
      rw [hP, Finset.mem_filter, Finset.mem_product] at hp ⊢
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
    · intro p _; simp
    · intro p _; simp
    · intro p _; simp
  have hpair : (∑ p ∈ P, (g p.2 - g p.1)) + (∑ p ∈ P, (g p.1 - g p.2)) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun p _ => by ring
  rw [← hswap] at hpair
  rw [hrw]
  linarith

/-! ### The current leaving a finite set -/

/-- **Kirchhoff's node law across a cut.**  The sum of the Laplacian over a
finite set is minus the current leaving it. -/
theorem sum_laplacian_eq (U : Finset V) (g : V → ℝ) :
    ∑ u ∈ U, laplacian G g u
      = ∑ u ∈ U, ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ U), (g y - g u) := by
  classical
  have hsplit : ∀ u : V, laplacian G g u
      = (∑ y ∈ (G.neighborFinset u).filter (fun y => y ∈ U), (g y - g u))
        + ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ U), (g y - g u) := by
    intro u
    rw [laplacian, ← Finset.sum_filter_add_sum_filter_not (G.neighborFinset u)
      (fun y => y ∈ U)]
  simp only [hsplit, Finset.sum_add_distrib]
  have hzero : ∑ u ∈ U, ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∈ U), (g y - g u)
      = 0 := by
    have hcongr : ∀ u ∈ U,
        (∑ y ∈ (G.neighborFinset u).filter (fun y => y ∈ U), (g y - g u))
          = ∑ y ∈ U.filter (fun y => G.Adj u y), (g y - g u) := by
      intro u _
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext y
      simp [Finset.mem_filter, SimpleGraph.mem_neighborFinset, and_comm]
    rw [Finset.sum_congr rfl hcongr]
    exact sum_adj_antisym_zero U g
  rw [hzero, zero_add]

/-- **The current across a separating cut is one.**  If the finite set `U` lies
inside `C` and contains the source, the total current leaving `U` is `1`. -/
theorem current_across_cut (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C)
    (U : Finset V) (hU : U ⊆ C) (hoU : o ∈ U) :
    ∑ u ∈ U, ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ U),
        (RWRS.killedGreenReal G (C : Set V) o u
          - RWRS.killedGreenReal G (C : Set V) o y) = 1 := by
  classical
  set g := RWRS.killedGreenReal G (C : Set V) o with hgdef
  have hlap : ∀ u ∈ U, laplacian G g u = -(if u = o then (1 : ℝ) else 0) := by
    intro u hu
    exact laplacian_killedGreenReal_of_escape C hesc hdeg ho (hU hu)
  have hsum : ∑ u ∈ U, laplacian G g u = -1 := by
    rw [Finset.sum_congr rfl hlap, Finset.sum_neg_distrib,
      Finset.sum_ite_eq' U o (fun _ => (1 : ℝ)), if_pos hoU]
  rw [sum_laplacian_eq U g] at hsum
  have hneg : ∑ u ∈ U, ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ U), (g u - g y)
      = -∑ u ∈ U, ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ U), (g y - g u) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hneg, hsum]
  norm_num

/-! ### The Dirichlet identity on a finite set -/

omit [G.LocallyFinite] in
/-- Swapping the two members of an adjacent ordered pair inside a finite set. -/
theorem sum_adj_swap (U : Finset V) (F : V → V → ℝ) :
    ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), F u y
      = ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), F y u := by
  classical
  set P : Finset (V × V) := (U ×ˢ U).filter (fun p => G.Adj p.1 p.2) with hP
  have hrw : ∀ K : V → V → ℝ,
      ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), K u y
        = ∑ p ∈ P, K p.1 p.2 := by
    intro K
    rw [hP, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_filter]
  rw [hrw F, hrw (fun a b => F b a)]
  refine Finset.sum_nbij' (i := Prod.swap) (j := Prod.swap) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  · intro p hp
    rw [hP, Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  · intro p _; simp
  · intro p _; simp
  · intro p _; simp

/-- **The Dirichlet identity.**  Twice the pairing of a function with its
Laplacian over a finite set is minus the energy of the interior edges plus twice
the flux through the boundary. -/
theorem two_mul_sum_mul_laplacian (U : Finset V) (h : V → ℝ) :
    2 * ∑ u ∈ U, h u * laplacian G h u
      = - (∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), (h u - h y) ^ 2)
        + 2 * ∑ u ∈ U, ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ U),
              h u * (h y - h u) := by
  classical
  have hsplit : ∀ u : V, h u * laplacian G h u
      = (∑ y ∈ U.filter (fun y => G.Adj u y), h u * (h y - h u))
        + ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ U), h u * (h y - h u) := by
    intro u
    rw [laplacian, Finset.mul_sum,
      ← Finset.sum_filter_add_sum_filter_not (G.neighborFinset u) (fun y => y ∈ U)]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp [Finset.mem_filter, SimpleGraph.mem_neighborFinset, and_comm]
  simp only [hsplit, Finset.sum_add_distrib]
  set A := ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), h u * (h y - h u) with hA
  have hswap : A = ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), h y * (h u - h y) :=
    sum_adj_swap U (fun a b => h a * (h b - h a))
  have htwo : 2 * A
      = - ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), (h u - h y) ^ 2 := by
    have hsum : A + A
        = ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y),
            (h u * (h y - h u) + h y * (h u - h y)) := by
      nth_rewrite 2 [hswap]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_add_distrib]
    have hterm : ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y),
          (h u * (h y - h u) + h y * (h u - h y))
        = - ∑ u ∈ U, ∑ y ∈ U.filter (fun y => G.Adj u y), (h u - h y) ^ 2 := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    linarith [hsum, hterm]
  linarith [htwo]

/-! ### The maximum principle for dead ends -/

omit [G.LocallyFinite] in
theorem eq_of_walk_induce {S : Set V} (h : V → ℝ)
    (hadj : ∀ a b : V, a ∈ S → b ∈ S → G.Adj a b → h a = h b) :
    ∀ {a b : ↥S} (_ : (G.induce S).Walk a b), h a.1 = h b.1 := by
  intro a b p
  induction p with
  | nil => rfl
  | @cons u v w hab _ ih => exact (hadj u.1 v.1 u.2 v.2 hab).trans ih

/-- **Dead-end subgraphs carry constant voltage.**  If the finite set `H` lies
inside `C`, is connected, misses the source, and only its vertex `x` has
neighbours outside `H`, then the voltage is constant on `H`, equal to its value
at `x`.  The proof is the Dirichlet identity: the flux term is carried by `x`
alone and vanishes because the voltage is measured from `g(x)`, so the energy of
the interior edges is zero. -/
theorem deadEnd_const (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C)
    (H : Finset V) (hHC : H ⊆ C) (hoH : o ∉ H) {x : V} (hx : x ∈ H)
    (hattach : ∀ u ∈ H, u ≠ x → ∀ y : V, G.Adj u y → y ∈ H)
    (hconn : (G.induce (H : Set V)).Connected) :
    ∀ u ∈ H, RWRS.killedGreenReal G (C : Set V) o u
      = RWRS.killedGreenReal G (C : Set V) o x := by
  classical
  set g := RWRS.killedGreenReal G (C : Set V) o with hgdef
  set h : V → ℝ := fun v => g v - g x with hhdef
  have hlap : ∀ u : V, laplacian G h u = laplacian G g u := by
    intro u
    rw [laplacian, laplacian]
    exact Finset.sum_congr rfl fun y _ => by simp only [hhdef]; ring
  have hharm : ∀ u ∈ H, laplacian G h u = 0 := by
    intro u hu
    rw [hlap u]
    exact harmonic_killedGreenReal_of_escape C hesc hdeg ho (hHC hu)
      (fun hcon => hoH (hcon ▸ hu))
  -- the flux through the boundary vanishes
  have hflux : ∑ u ∈ H, ∑ y ∈ (G.neighborFinset u).filter (fun y => y ∉ H),
      h u * (h y - h u) = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    rcases eq_or_ne u x with rfl | hux
    · have hzero : h u = 0 := by simp [hhdef]
      exact Finset.sum_eq_zero fun y _ => by rw [hzero]; ring
    · have hempty : (G.neighborFinset u).filter (fun y => y ∉ H) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun y hy => ?_
        exact not_not.2 (hattach u hu hux y ((SimpleGraph.mem_neighborFinset _ _ _).1 hy))
      rw [hempty, Finset.sum_empty]
  -- the energy of the interior edges vanishes
  have hdir := two_mul_sum_mul_laplacian (G := G) H h
  rw [Finset.sum_congr rfl (fun u hu => by rw [hharm u hu, mul_zero] :
      ∀ u ∈ H, h u * laplacian G h u = 0), Finset.sum_const, smul_zero, hflux] at hdir
  have henergy : ∑ u ∈ H, ∑ y ∈ H.filter (fun y => G.Adj u y), (h u - h y) ^ 2 = 0 := by
    linarith [hdir]
  have hnn : ∀ u ∈ H, (0 : ℝ) ≤ ∑ y ∈ H.filter (fun y => G.Adj u y), (h u - h y) ^ 2 :=
    fun u _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  have hterm : ∀ u ∈ H, ∀ y ∈ H, G.Adj u y → h u = h y := by
    intro u hu y hy hadj
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 henergy u hu
    have h2 : (h u - h y) ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => sq_nonneg _)).1 h1 y ?_
      exact Finset.mem_filter.2 ⟨hy, hadj⟩
    have : h u - h y = 0 := by nlinarith [h2]
    linarith
  -- connectivity carries the equality to every vertex of `H`
  intro u hu
  have hxS : x ∈ (H : Set V) := hx
  have huS : u ∈ (H : Set V) := hu
  obtain ⟨p⟩ := hconn.preconnected ⟨x, hxS⟩ ⟨u, huS⟩
  have := eq_of_walk_induce (S := (H : Set V)) h
    (fun a b ha hb hab => hterm a ha b hb hab) p
  simp only [hhdef] at this
  linarith

end RWRS.Support
