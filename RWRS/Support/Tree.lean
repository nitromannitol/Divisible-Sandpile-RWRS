/-
The spherically symmetric tree in which a vertex at depth `n` has `b n`
children, built as the words whose entry at position `i` is a child index at
depth `i`.  Adjacency is appending one letter, so the graph is a tree: a cut
function separates the two ends of any edge, and every edge is therefore a
bridge.
-/
import RWRS.Support.Countable
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace RWRS.Support

open scoped Classical

/-! ### A cut function makes an edge a bridge -/

theorem mem_edges_of_cut {V : Type*} {G : SimpleGraph V} {u v : V} (φ : V → Bool)
    (hcut : ∀ a c : V, G.Adj a c → φ a ≠ φ c → s(a, c) = s(u, v)) :
    ∀ {a c : V} (p : G.Walk a c), φ a ≠ φ c → s(u, v) ∈ p.edges := by
  intro a c p
  induction p with
  | nil => intro h; exact absurd rfl h
  | @cons a m c hadj q ih =>
      intro h
      by_cases hac : φ a = φ m
      · exact List.mem_cons_of_mem _ (ih (by rw [← hac]; exact h))
      · rw [SimpleGraph.Walk.edges_cons, ← hcut a m hadj hac]
        exact List.mem_cons_self

theorem isBridge_of_cut {V : Type*} {G : SimpleGraph V} {u v : V} (φ : V → Bool)
    (hu : φ u = false) (hv : φ v = true)
    (hcut : ∀ a c : V, G.Adj a c → φ a ≠ φ c → s(a, c) = s(u, v)) :
    G.IsBridge s(u, v) := by
  rw [SimpleGraph.isBridge_iff_forall_walk_mem_edges]
  intro p
  exact mem_edges_of_cut φ hcut p (by rw [hu, hv]; exact Bool.false_ne_true)

/-! ### The tree of words -/

variable (b : ℕ → ℕ)

/-- A word is a vertex when its letter at position `i` is a child index at
depth `i`. -/
def ValidWord (w : List ℕ) : Prop := ∀ i (h : i < w.length), w[i] < b i

/-- A vertex of the spherically symmetric tree with `b n` children at depth `n`. -/
abbrev TreeV : Type := {w : List ℕ // ValidWord b w}

theorem valid_nil : ValidWord b [] := by
  intro i h
  simp at h

theorem valid_append {w : List ℕ} (hw : ValidWord b w) {j : ℕ} (hj : j < b w.length) :
    ValidWord b (w ++ [j]) := by
  intro i h
  rw [List.length_append, List.length_singleton] at h
  rcases Nat.lt_or_ge i w.length with hi | hi
  · rw [List.getElem_append_left hi]
    exact hw i hi
  · have hiw : i = w.length := by omega
    subst hiw
    simp only [List.getElem_append_right (le_refl w.length), Nat.sub_self]
    simpa using hj

/-- The tree of words. -/
def treeGraph : SimpleGraph (TreeV b) where
  Adj p q := (∃ j, q.1 = p.1 ++ [j]) ∨ (∃ j, p.1 = q.1 ++ [j])
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun p h => by
    rcases h with ⟨j, hj⟩ | ⟨j, hj⟩ <;>
      · have := congrArg List.length hj
        simp at this⟩

theorem treeGraph_adj_iff {p q : TreeV b} :
    (treeGraph b).Adj p q ↔ (∃ j, q.1 = p.1 ++ [j]) ∨ (∃ j, p.1 = q.1 ++ [j]) := Iff.rfl

theorem valid_dropLast {w : List ℕ} (hw : ValidWord b w) : ValidWord b w.dropLast := by
  intro i h
  have hlen : w.dropLast.length = w.length - 1 := @List.length_dropLast _ w
  have hi : i < w.length := by omega
  rw [List.getElem_dropLast]
  exact hw i hi

noncomputable instance treeLocallyFinite : (treeGraph b).LocallyFinite := fun p => by
  classical
  refine Set.Finite.fintype (Set.Finite.subset (s := Subtype.val ⁻¹'
      (insert p.1.dropLast ((fun j => p.1 ++ [j]) '' Set.Iio (b p.1.length)))) ?_ ?_)
  · refine Set.Finite.preimage (Subtype.val_injective.injOn) ?_
    exact (Set.finite_Iio _).image _ |>.insert _
  · rintro q (⟨j, hj⟩ | ⟨j, hj⟩)
    · refine Set.mem_preimage.mpr (Set.mem_insert_iff.mpr (Or.inr ⟨j, ?_, hj.symm⟩))
      have hlen : p.1.length < q.1.length := by
        rw [hj]; simp
      have hq := q.2 p.1.length hlen
      have hval : q.1[p.1.length] = j := by
        simp [hj, List.getElem_append_right (le_refl p.1.length)]
      rw [hval] at hq
      exact hq
    · refine Set.mem_preimage.mpr (Set.mem_insert_iff.mpr (Or.inl ?_))
      rw [hj]
      simp

theorem reachable_root : ∀ (n : ℕ) (p : TreeV b), p.1.length = n →
    (treeGraph b).Reachable ⟨[], valid_nil b⟩ p := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have : p.1 = [] := List.eq_nil_of_length_eq_zero hp
      exact (Subtype.ext this : p = ⟨[], valid_nil b⟩) ▸ SimpleGraph.Reachable.refl _
  | succ n ih =>
      intro p hp
      have hne : p.1 ≠ [] := by
        intro h; rw [h] at hp; simp at hp
      set w : TreeV b := ⟨p.1.dropLast, valid_dropLast b p.2⟩ with hw
      have hlen : w.1.length = n := by
        have hd : p.1.dropLast.length = p.1.length - 1 := @List.length_dropLast _ p.1
        simp only [hw]
        omega
      have hadj : (treeGraph b).Adj w p :=
        Or.inl ⟨p.1.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      exact (ih w hlen).trans hadj.reachable

theorem treeInfinite (hb : ∀ i, 0 < b i) : Infinite (TreeV b) := by
  refine Infinite.of_injective (fun n : ℕ => (⟨List.replicate n 0, ?_⟩ : TreeV b)) ?_
  · intro i hi
    rw [List.getElem_replicate]
    exact hb i
  · intro a c hac
    have := congrArg (fun w => w.1.length) hac
    simpa using this

theorem treeConnected : (treeGraph b).Connected := by
  haveI : Nonempty (TreeV b) := ⟨⟨[], valid_nil b⟩⟩
  refine ⟨fun p q => ?_⟩
  exact ((reachable_root b p.1.length p rfl).symm).trans (reachable_root b q.1.length q rfl)

theorem treeAcyclic : (treeGraph b).IsAcyclic := by
  classical
  have key : ∀ (p q : TreeV b) (j : ℕ), q.1 = p.1 ++ [j] →
      (treeGraph b).IsBridge s(p, q) := by
    intro p q j hq
    have step : ∀ (a c : TreeV b) (k : ℕ), c.1 = a.1 ++ [k] →
        ¬(q.1 <+: a.1) → q.1 <+: c.1 → a = p ∧ c = q := by
      intro a c k hc hna hqc
      have hlen : q.1.length ≤ c.1.length := hqc.length_le
      have hclen : c.1.length = a.1.length + 1 := by rw [hc]; simp
      have hgt : a.1.length < q.1.length := by
        by_contra hcon
        rw [not_lt] at hcon
        exact hna (List.prefix_of_prefix_length_le hqc (hc ▸ List.prefix_append a.1 [k]) hcon)
      have heq : q.1.length = c.1.length := by omega
      have hqc' : q.1 = c.1 := hqc.eq_of_length heq
      have hcq : c = q := Subtype.ext hqc'.symm
      refine ⟨Subtype.ext ?_, hcq⟩
      have : a.1 ++ [k] = p.1 ++ [j] := by rw [← hc, ← hqc', ← hq]
      exact (List.append_inj' this rfl).1
    refine isBridge_of_cut (fun r => decide (q.1 <+: r.1)) ?_ (by simp) ?_
    · simp only [decide_eq_false_iff_not]
      intro hpre
      have h1 := hpre.length_le
      rw [hq] at h1
      simp at h1
    · intro a c hadj hne
      rcases hadj with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hqa : ¬(q.1 <+: a.1) := by
          intro hp
          exact hne (by
            have : q.1 <+: c.1 := hk ▸ hp.trans (List.prefix_append a.1 [k])
            simp [hp, this])
        have hqc : q.1 <+: c.1 := by
          by_contra hcon
          exact hne (by simp [hqa, hcon])
        obtain ⟨ha, hc⟩ := step a c k hk hqa hqc
        rw [ha, hc]
      · have hqc : ¬(q.1 <+: c.1) := by
          intro hp
          exact hne (by
            have : q.1 <+: a.1 := hk ▸ hp.trans (List.prefix_append c.1 [k])
            simp [hp, this])
        have hqa : q.1 <+: a.1 := by
          by_contra hcon
          exact hne (by simp [hqc, hcon])
        obtain ⟨hc, ha⟩ := step c a k hk hqc hqa
        rw [ha, hc, Sym2.eq_swap]
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro p q hadj
  rcases hadj with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact key p q j hj
  · rw [Sym2.eq_swap]
    exact key q p j hj

theorem treeIsTree : (treeGraph b).IsTree :=
  ⟨treeConnected b, treeAcyclic b⟩

/-! ### The neighbours of a vertex -/

/-- The `j`-th child of `v`, and `v` itself when `j` is not a child index. -/
noncomputable def childOf (v : TreeV b) (j : ℕ) : TreeV b :=
  if h : j < b v.1.length then ⟨v.1 ++ [j], valid_append b v.2 h⟩ else v

theorem childOf_val {v : TreeV b} {j : ℕ} (h : j < b v.1.length) :
    (childOf b v j).1 = v.1 ++ [j] := by
  rw [childOf, dif_pos h]

/-- The parent of `v`, and the root itself at the root. -/
def parentOf (v : TreeV b) : TreeV b := ⟨v.1.dropLast, valid_dropLast b v.2⟩

theorem adj_iff_child_or_parent {v w : TreeV b} :
    (treeGraph b).Adj v w ↔
      ((∃ j, j < b v.1.length ∧ w = childOf b v j) ∨ (v.1 ≠ [] ∧ w = parentOf b v)) := by
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · refine Or.inl ⟨j, ?_, ?_⟩
      · have hlen : v.1.length < w.1.length := by rw [hj]; simp
        have hw := w.2 v.1.length hlen
        have hval : w.1[v.1.length] = j := by
          simp [hj, List.getElem_append_right (le_refl v.1.length)]
        rw [hval] at hw
        exact hw
      · refine Subtype.ext ?_
        rw [hj, childOf_val]
        have hlen : v.1.length < w.1.length := by rw [hj]; simp
        have hw := w.2 v.1.length hlen
        have hval : w.1[v.1.length] = j := by
          simp [hj, List.getElem_append_right (le_refl v.1.length)]
        rwa [hval] at hw
    · refine Or.inr ⟨?_, ?_⟩
      · intro h
        rw [h] at hj
        simp at hj
      · refine Subtype.ext ?_
        show w.1 = v.1.dropLast
        rw [hj]
        simp
  · rintro (⟨j, hj, rfl⟩ | ⟨hne, rfl⟩)
    · exact Or.inl ⟨j, childOf_val b hj⟩
    · exact Or.inr ⟨v.1.getLast hne, by
        rw [parentOf]
        exact (List.dropLast_append_getLast hne).symm⟩

noncomputable def nbrFinsetTree (v : TreeV b) : Finset (TreeV b) :=
  (Finset.range (b v.1.length)).image (childOf b v)
    ∪ (if v.1 = [] then (∅ : Finset (TreeV b)) else {parentOf b v})

theorem mem_nbrFinsetTree {v w : TreeV b} :
    w ∈ nbrFinsetTree b v ↔ (treeGraph b).Adj v w := by
  classical
  rw [nbrFinsetTree, Finset.mem_union, Finset.mem_image, adj_iff_child_or_parent]
  constructor
  · rintro (⟨j, hj, rfl⟩ | hp)
    · exact Or.inl ⟨j, Finset.mem_range.mp hj, rfl⟩
    · by_cases hv : v.1 = []
      · rw [if_pos hv] at hp; simp at hp
      · rw [if_neg hv, Finset.mem_singleton] at hp
        exact Or.inr ⟨hv, hp⟩
  · rintro (⟨j, hj, rfl⟩ | ⟨hv, rfl⟩)
    · exact Or.inl ⟨j, Finset.mem_range.mpr hj, rfl⟩
    · exact Or.inr (by rw [if_neg hv]; exact Finset.mem_singleton_self _)

theorem neighborFinset_eq (v : TreeV b) :
    (treeGraph b).neighborFinset v = nbrFinsetTree b v := by
  ext w
  rw [SimpleGraph.mem_neighborFinset, ← mem_nbrFinsetTree]

theorem childOf_injOn (v : TreeV b) :
    Set.InjOn (childOf b v) (Finset.range (b v.1.length)) := by
  intro j hj k hk hjk
  have h1 := childOf_val b (Finset.mem_range.mp (by exact_mod_cast hj))
  have h2 := childOf_val b (Finset.mem_range.mp (by exact_mod_cast hk))
  have : v.1 ++ [j] = v.1 ++ [k] := by rw [← h1, ← h2, hjk]
  simpa using this

theorem disjoint_children_parent (v : TreeV b) :
    Disjoint ((Finset.range (b v.1.length)).image (childOf b v))
      (if v.1 = [] then (∅ : Finset (TreeV b)) else {parentOf b v}) := by
  classical
  by_cases hv : v.1 = []
  · rw [if_pos hv]; exact Finset.disjoint_empty_right _
  · rw [if_neg hv]
    rw [Finset.disjoint_singleton_right]
    rintro hmem
    obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hmem
    have hlen : (parentOf b v).1.length = v.1.length - 1 := @List.length_dropLast _ v.1
    have hlen2 : (childOf b v j).1.length = v.1.length + 1 := by
      rw [childOf_val b (Finset.mem_range.mp hj)]; simp
    have hne : v.1.length ≠ 0 := fun h => hv (List.eq_nil_of_length_eq_zero h)
    rw [hjc] at hlen2
    omega

theorem degree_eq (v : TreeV b) :
    (treeGraph b).degree v = b v.1.length + (if v.1 = [] then 0 else 1) := by
  classical
  rw [SimpleGraph.degree, neighborFinset_eq, nbrFinsetTree,
    Finset.card_union_of_disjoint (disjoint_children_parent b v),
    Finset.card_image_of_injOn (childOf_injOn b v), Finset.card_range]
  by_cases hv : v.1 = [] <;> simp [hv]

theorem sum_over_neighbors (v : TreeV b) (ψ : ℕ → ℝ) :
    ∑ y ∈ (treeGraph b).neighborFinset v, ψ y.1.length
      = b v.1.length * ψ (v.1.length + 1)
        + (if v.1 = [] then 0 else ψ (v.1.length - 1)) := by
  classical
  rw [neighborFinset_eq, nbrFinsetTree,
    Finset.sum_union (disjoint_children_parent b v),
    Finset.sum_image (fun j hj k hk h => childOf_injOn b v hj hk h)]
  have hchild : ∀ j ∈ Finset.range (b v.1.length),
      ψ (childOf b v j).1.length = ψ (v.1.length + 1) := by
    intro j hj
    rw [childOf_val b (Finset.mem_range.mp hj)]
    simp
  rw [Finset.sum_congr rfl hchild, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  by_cases hv : v.1 = []
  · rw [if_pos hv, if_pos hv, Finset.sum_empty]
  · rw [if_neg hv, if_neg hv, Finset.sum_singleton]
    have hp : (parentOf b v).1.length = v.1.length - 1 := @List.length_dropLast _ v.1
    rw [hp]

end RWRS.Support
