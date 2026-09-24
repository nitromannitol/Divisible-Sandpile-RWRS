/-
The killed Green function is the unique solution of its boundary value problem.

A function that vanishes off a finite escapable set `C` and whose Laplacian on
`C` is the unit source at `o` is `g_C(o,·)`.  The difference of two such
functions is harmonic on `C` and vanishes off it, so the maximum principle for a
network Laplacian, applied to the difference and to its negative, makes it zero.
This is the argument of `RWRS.Support.valueExit_eq_exitValue`, with the exit
payoff replaced by an arbitrary solution.
-/
import RWRS.Support.CutCurrent
import LatticeProb.Network.MaximumPrinciple

namespace RWRS.Support

open LatticeProb.Network
open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- The unit-conductance network Laplacian is the graph Laplacian. -/
theorem netLaplacian_unitCond_eq [G.LocallyFinite] (f : V → ℝ) (x : V) :
    netLaplacian G (unitCond G) f x = RWRS.laplacian G f x := by
  classical
  rw [netLaplacian, RWRS.laplacian]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [unitCond, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy), one_mul]

/-- **The maximum principle from an escape hypothesis.**  The connectedness of
the whole graph is more than the argument needs: what carries the maximum out of
`C` is a walk from a vertex of `C` to a vertex outside it, which is the same
hypothesis the killed Green function itself is built under. -/
theorem le_of_harmonicOn_escape {c : V → V → ℝ} (hc : IsCond G c)
    (C : Finset V) (S : Set V) (f : V → ℝ) (M : ℝ)
    (hesc : ∀ b ∈ C, ∃ (q : V) (_ : G.Walk b q), q ∉ C)
    (hharm : ∀ x ∈ C, x ∉ S → netLaplacian G c f x = 0)
    (hout : ∀ x, x ∉ C → f x ≤ M) (hS : ∀ x ∈ S, f x ≤ M) :
    ∀ x, f x ≤ M := by
  classical
  intro x
  by_contra hcon
  rw [not_le] at hcon
  have hxC : x ∈ C := by
    by_contra h
    exact absurd (hout x h) (not_le.mpr hcon)
  obtain ⟨b, hbC, hbmax⟩ := Finset.exists_max_image C f ⟨x, hxC⟩
  have hMb : M < f b := lt_of_lt_of_le hcon (hbmax x hxC)
  have hle : ∀ y : V, f y ≤ f b := by
    intro y
    by_cases hy : y ∈ C
    · exact hbmax y hy
    · exact le_trans (hout y hy) hMb.le
  have hstep : ∀ y : V, y ∈ C → f y = f b → ∀ z : V, G.Adj y z → z ∈ C ∧ f z = f b := by
    intro y hyC hyb z hyz
    have hyS : y ∉ S := fun h => absurd (hS y h) (not_le.mpr (hyb ▸ hMb))
    have hzero := hharm y hyC hyS
    have hnonpos : ∀ w ∈ G.neighborFinset y, c y w * (f w - f y) ≤ 0 := by
      intro w _
      exact mul_nonpos_of_nonneg_of_nonpos (hc.nonneg y w) (by
        have := hle w
        rw [hyb]
        linarith)
    have hall := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hzero
    have hz := hall z ((SimpleGraph.mem_neighborFinset _ _ _).mpr hyz)
    have hfz : f z = f y := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h (hc.pos hyz).ne'
      · linarith
    refine ⟨?_, by rw [hfz, hyb]⟩
    by_contra hzC
    have := hout z hzC
    rw [hfz, hyb] at this
    linarith
  have hwalk : ∀ {u v : V} (_ : G.Walk u v), u ∈ C → f u = f b → v ∈ C ∧ f v = f b := by
    intro u v p
    induction p with
    | nil => intro h1 h2; exact ⟨h1, h2⟩
    | @cons a d e hadj p' ih =>
        intro h1 h2
        obtain ⟨hd, hfd⟩ := hstep a h1 h2 d hadj
        exact ih hd hfd
  obtain ⟨q, p, hq⟩ := hesc b hbC
  exact hq (hwalk p hbC rfl).1

/-- **A function vanishing off `C` and harmonic on `C` is zero.** -/
theorem eq_zero_of_harmonicOn_of_vanishing (C : Finset V)
    (hesc : ∀ b ∈ C, ∃ (q : V) (_ : G.Walk b q), q ∉ C) (h : V → ℝ)
    (hharm : ∀ u ∈ C, RWRS.laplacian G h u = 0)
    (hout : ∀ u, u ∉ C → h u = 0) :
    ∀ u, h u = 0 := by
  have hle : ∀ u : V, h u ≤ 0 :=
    le_of_harmonicOn_escape isCond_unitCond C ∅ h 0 hesc
      (fun z hz _ => by rw [netLaplacian_unitCond_eq]; exact hharm z hz)
      (fun z hz => le_of_eq (hout z hz)) (by simp)
  have hge : ∀ u : V, (-h) u ≤ 0 := by
    refine le_of_harmonicOn_escape isCond_unitCond C ∅ (-h) 0 hesc (fun z hz _ => ?_)
      (fun z hz => by simp [hout z hz]) (by simp)
    rw [netLaplacian_unitCond_eq]
    have hneg : RWRS.laplacian G (-h) z = - RWRS.laplacian G h z := by
      simp only [RWRS.laplacian, Pi.neg_apply, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hneg, hharm z hz, neg_zero]
  intro u
  have := hge u
  simp only [Pi.neg_apply] at this
  linarith [hle u]

/-- **Uniqueness for the killed boundary value problem.**  A function that
vanishes off `C` and solves `Δf = -δ_o` on `C` is the killed Green function. -/
theorem eq_killedGreenReal_of_boundaryValue (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C) (f : V → ℝ)
    (hlap : ∀ u ∈ C, RWRS.laplacian G f u = -(if u = o then (1 : ℝ) else 0))
    (hout : ∀ u, u ∉ C → f u = 0) :
    ∀ u, f u = RWRS.killedGreenReal G (C : Set V) o u := by
  classical
  set g := RWRS.killedGreenReal G (C : Set V) o with hgdef
  set h : V → ℝ := fun v => f v - g v with hhdef
  have hgout : ∀ u, u ∉ C → g u = 0 := by
    intro u hu
    exact killedGreenReal_eq_zero_of_not_mem_of_escape C hesc
      (by exact_mod_cast hu : u ∉ (C : Set V)) o
  have hharm : ∀ u ∈ C, RWRS.laplacian G h u = 0 := by
    intro u hu
    have hsplit : RWRS.laplacian G h u = RWRS.laplacian G f u - RWRS.laplacian G g u := by
      simp only [RWRS.laplacian, hhdef, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [hsplit, hlap u hu, laplacian_killedGreenReal_of_escape C hesc hdeg ho hu]
    ring
  have := eq_zero_of_harmonicOn_of_vanishing C
    (fun b _ => by obtain ⟨r, p, hr⟩ := hesc b; exact ⟨r, p, by exact_mod_cast hr⟩) h hharm
    (fun u hu => by simp only [hhdef, hout u hu, hgout u hu, sub_zero])
  intro u
  have hu := this u
  simp only [hhdef] at hu
  linarith

/-- Every vertex of a connected graph with at least two vertices has a neighbour. -/
theorem degree_pos_of_connected [Nontrivial V] (hG : G.Connected) (v : V) :
    0 < G.degree v := by
  rw [SimpleGraph.degree_pos_iff_exists_adj]
  obtain ⟨u, hu⟩ := exists_ne v
  obtain ⟨p⟩ := hG.preconnected v u
  rcases p with _ | ⟨hadj, q⟩
  · exact absurd rfl hu
  · exact ⟨_, hadj⟩

omit [G.LocallyFinite] in
/-- On an infinite connected graph the walk can leave every finite set. -/
theorem escape_of_finite [Infinite V] (hG : G.Connected) (C : Finset V) (x : V) :
    ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V) := by
  obtain ⟨q, hq⟩ : ∃ q : V, q ∉ C := by
    by_contra hcon
    push Not at hcon
    exact absurd (Set.Finite.subset C.finite_toSet fun z _ => hcon z)
      (Set.infinite_univ (α := V))
  obtain ⟨p⟩ := hG.preconnected x q
  exact ⟨q, p, by exact_mod_cast hq⟩

/-- **The voltage is largest at the source.** -/
theorem killedGreenReal_le_source (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C) (x : V) :
    RWRS.killedGreenReal G (C : Set V) o x ≤ RWRS.killedGreenReal G (C : Set V) o o := by
  classical
  refine le_of_harmonicOn_escape isCond_unitCond C {o}
    (RWRS.killedGreenReal G (C : Set V) o) _
    (fun b _ => by obtain ⟨r, p, hr⟩ := hesc b; exact ⟨r, p, by exact_mod_cast hr⟩)
    (fun z hz hzo => ?_) (fun z hz => ?_) (fun z hz => ?_) x
  · rw [netLaplacian_unitCond_eq]
    exact harmonic_killedGreenReal_of_escape C hesc hdeg ho hz
      (fun hcon => hzo (by rw [hcon]; exact rfl))
  · rw [killedGreenReal_eq_zero_of_not_mem_of_escape C hesc
      (by exact_mod_cast hz : z ∉ (C : Set V)) o]
    exact killedGreenReal_nonneg_of_escape C hesc o o
  · rw [Set.mem_singleton_iff] at hz
    exact le_of_eq (by rw [hz])

end RWRS.Support
