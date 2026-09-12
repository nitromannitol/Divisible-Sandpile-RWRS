/-
The comb `D_{w,n}` of `ssec:comb-estimates`: the trunk from the root of the tree
of pipes to the terminal pipe indexed by `w`, together with the sibling pipes at
each trunk branching vertex, with the far endpoints excluded.

What is proved here is the combinatorics the electrical estimates rest on: the
comb is a finite set of sites, it misses at least one site, and it is exactly the
union of the trunk pipes with the sibling pipes hanging off the trunk branching
vertices.
-/
import RWRS.Support.RayGadget
import RWRS.Support.KilledGreen

namespace RWRS.Support

open scoped ENNReal

variable {B : ℕ} {L : ℕ → ℕ}

/-! ### The comb is finite -/

/-- A bound for the pipe lengths up to level `n`. -/
noncomputable def maxLen (L : ℕ → ℕ) (n : ℕ) : ℕ := (Finset.range (n + 1)).sup L

theorem le_maxLen (L : ℕ → ℕ) {j n : ℕ} (h : j ≤ n) : L j ≤ maxLen L n :=
  Finset.le_sup (f := L) (Finset.mem_range.2 (by omega))

theorem mem_combSet_bounds {n : ℕ} {w : List (Fin B)} {v : List (Fin B) × ℕ}
    (hv : v ∈ combSet B L n w) : v.1.length ≤ n ∧ v.2 ≤ maxLen L n := by
  obtain ⟨hval, hlen, -, -⟩ := hv
  refine ⟨hlen, ?_⟩
  rcases hval with h0 | ⟨-, -, h2⟩
  · omega
  · have := le_maxLen L (j := v.1.length) hlen
    omega

open scoped Classical in
theorem combSet_subset (n : ℕ) (w : List (Fin B)) :
    combSet B L n w
      ⊆ (↑((wordsLe B n) ×ˢ Finset.range (maxLen L n + 1)) : Set (List (Fin B) × ℕ)) := by
  intro v hv
  obtain ⟨hlen, hsnd⟩ := mem_combSet_bounds hv
  exact Finset.mem_coe.2 (Finset.mem_product.2
    ⟨mem_wordsLe hlen, Finset.mem_range.2 (by omega)⟩)

open scoped Classical in
/-- **The comb is a finite set of sites.** -/
theorem combSet_finite (n : ℕ) (w : List (Fin B)) : (combSet B L n w).Finite :=
  Set.Finite.subset ((wordsLe B n) ×ˢ Finset.range (maxLen L n + 1)).finite_toSet
    (combSet_subset n w)

/-- The far endpoint of the terminal pipe is a site of the tree of pipes that the
comb misses, so the comb is a proper subset. -/
theorem combSet_proper {n : ℕ} (w : List (Fin B)) (hw : w.length = n) :
    (w, 0) ∉ combSet B L n w := by
  rintro ⟨-, -, -, h⟩
  rcases h with h1 | ⟨-, h2⟩
  · exact absurd h1 (by simp)
  · simp only at h2
    omega

/-! ### Every site walks to the root -/

theorem pipeGraph_adj_pred (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    {v : List (Fin B) × ℕ} (hv : PipeValid B L v) (hne : v ≠ pipeRoot B) :
    (pipeGraph B L e).Adj v (pipePred B L v) :=
  ⟨Or.inl hv, Or.inl (pipePred_valid hv), (pipePred_ne_self hL hv hne).symm, Or.inl rfl⟩

theorem exists_walk_to_root (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool) :
    ∀ (n : ℕ) (v : List (Fin B) × ℕ), PipeValid B L v → pipeDepth L v ≤ n →
      Nonempty ((pipeGraph B L e).Walk v (pipeRoot B)) := by
  intro n
  induction n with
  | zero =>
      intro v hv hd
      have : v = pipeRoot B := eq_root_of_pipeDepth_zero hL hv (Nat.le_zero.1 hd)
      subst this
      exact ⟨SimpleGraph.Walk.nil⟩
  | succ n ih =>
      intro v hv hd
      by_cases hz : v = pipeRoot B
      · subst hz; exact ⟨SimpleGraph.Walk.nil⟩
      · have hdrop := pipeDepth_pred_lt hL hv hz
        obtain ⟨p⟩ := ih (pipePred B L v) (pipePred_valid hv) (by omega)
        exact ⟨SimpleGraph.Walk.cons (pipeGraph_adj_pred hL e hv hz) p⟩

/-! ### The comb is escapable -/

theorem escape_combSet (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool) {n : ℕ}
    {w : List (Fin B)} (hw : w.length = n) (x : List (Fin B) × ℕ) :
    ∃ (q : List (Fin B) × ℕ) (_ : (pipeGraph B L e).Walk x q), q ∉ combSet B L n w := by
  classical
  by_cases hx : x ∈ combSet B L n w
  · have hvx : PipeValid B L x := hx.1
    obtain ⟨p⟩ := exists_walk_to_root hL e (pipeDepth L x) x hvx le_rfl
    have hvw : PipeValid B L (w, 0) := Or.inl rfl
    obtain ⟨r⟩ := exists_walk_to_root hL e (pipeDepth L (w, 0)) (w, 0) hvw le_rfl
    exact ⟨(w, 0), p.append r.reverse, combSet_proper w hw⟩
  · exact ⟨x, SimpleGraph.Walk.nil, hx⟩

/-! ### No site of the tree of pipes is isolated -/

theorem exists_adj_root (hB : 1 ≤ B) (e : Bool) :
    ∃ u, (pipeGraph B L e).Adj (pipeRoot B) u := by
  have hc : Nonempty (Fin B) := ⟨⟨0, by omega⟩⟩
  obtain ⟨c⟩ := hc
  have hlen : ([c] : List (Fin B)).length = 1 := rfl
  have hne : ([c] : List (Fin B)) ≠ [] := by simp
  by_cases hL2 : 2 ≤ L 1
  · refine ⟨([c], 1), ?_⟩
    have hval : PipeValid B L (([c] : List (Fin B)), 1) :=
      Or.inr ⟨hne, le_rfl, by rw [hlen]; omega⟩
    have hpred : pipePred B L (([c] : List (Fin B)), 1) = pipeRoot B := by
      simp [pipePred, pipeRoot]
    exact ⟨Or.inl (Or.inl rfl), Or.inl hval, by simp [pipeRoot], Or.inr hpred.symm⟩
  · refine ⟨([c], 0), ?_⟩
    have hval : PipeValid B L (([c] : List (Fin B)), 0) := Or.inl rfl
    have hpred : pipePred B L (([c] : List (Fin B)), 0) = pipeRoot B := by
      simp [pipePred, pipeRoot, hne, hlen, hL2]
    exact ⟨Or.inl (Or.inl rfl), Or.inl hval, by simp [pipeRoot], Or.inr hpred.symm⟩

theorem degree_pos_of_valid (hB : 1 ≤ B) (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    {v : List (Fin B) × ℕ} (hv : PipeValid B L v) : 0 < (pipeGraph B L e).degree v := by
  rw [SimpleGraph.degree_pos_iff_exists_adj]
  by_cases hz : v = pipeRoot B
  · subst hz
    exact exists_adj_root hB e
  · exact ⟨pipePred B L v, pipeGraph_adj_pred hL e hv hz⟩

theorem degree_pos_of_mem_combSet (hB : 1 ≤ B) (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    {n : ℕ} {w : List (Fin B)} {v : List (Fin B) × ℕ} (hv : v ∈ combSet B L n w) :
    0 < (pipeGraph B L e).degree v :=
  degree_pos_of_valid hB hL e hv.1

end RWRS.Support
