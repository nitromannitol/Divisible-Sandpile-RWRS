/-
The connected component `D_K(o)` of `prop:finite-vol`: its elementary
properties, and the connectedness of the graph it induces.
-/
import RWRS.Setting

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V}

/-- The component of `o` is contained in the set. -/
theorem compIn_subset (D : Set V) (o : V) : RWRS.compIn G D o ⊆ D := by
  rintro x ⟨-, hx, -⟩
  exact hx

/-- The base point belongs to its own component. -/
theorem mem_compIn_self {D : Set V} {o : V} (ho : o ∈ D) : o ∈ RWRS.compIn G D o :=
  ⟨ho, ho, SimpleGraph.Reachable.refl _⟩

/-- The component is closed under taking a neighbour inside the set. -/
theorem mem_compIn_of_adj {D : Set V} {o x y : V} (hx : x ∈ RWRS.compIn G D o)
    (hadj : G.Adj x y) (hy : y ∈ D) : y ∈ RWRS.compIn G D o := by
  obtain ⟨ho, hxD, hreach⟩ := hx
  refine ⟨ho, hy, hreach.trans ?_⟩
  exact SimpleGraph.Adj.reachable (by exact hadj)

/-- A walk inside `D` starting in the component of `o` stays in it, and is a
walk of the graph the component induces. -/
theorem reachable_compIn_of_walk {D : Set V} {o : V} :
    ∀ {a b : (D : Set V)} (_p : (G.induce D).Walk a b) (ha : (a : V) ∈ RWRS.compIn G D o),
      ∃ hb : (b : V) ∈ RWRS.compIn G D o,
        (G.induce (RWRS.compIn G D o)).Reachable ⟨(a : V), ha⟩ ⟨(b : V), hb⟩ := by
  intro a b p
  induction p with
  | nil => exact fun ha => ⟨ha, SimpleGraph.Reachable.refl _⟩
  | @cons u v w hadj p' ih =>
      intro ha
      have hadj' : G.Adj (u : V) (v : V) := hadj
      have hv : (v : V) ∈ RWRS.compIn G D o := mem_compIn_of_adj ha hadj' v.2
      obtain ⟨hb, hreach⟩ := ih hv
      refine ⟨hb, SimpleGraph.Reachable.trans ?_ hreach⟩
      exact SimpleGraph.Adj.reachable (show (G.induce (RWRS.compIn G D o)).Adj
        ⟨(u : V), ha⟩ ⟨(v : V), hv⟩ from hadj')

/-- **The component induces a connected graph.** -/
theorem connected_induce_compIn {D : Set V} {o : V} (ho : o ∈ D) :
    (G.induce (RWRS.compIn G D o)).Connected := by
  have hoc : o ∈ RWRS.compIn G D o := mem_compIn_self ho
  haveI : Nonempty (RWRS.compIn G D o : Set V) := ⟨⟨o, hoc⟩⟩
  refine ⟨?_⟩
  intro u v
  have key : ∀ w : (RWRS.compIn G D o : Set V),
      (G.induce (RWRS.compIn G D o)).Reachable ⟨o, hoc⟩ w := by
    rintro ⟨w, hw⟩
    obtain ⟨-, hwD, hreach⟩ := hw
    obtain ⟨p⟩ := hreach
    obtain ⟨hb, hr⟩ := reachable_compIn_of_walk (o := o) p hoc
    exact hr
  exact (key u).symm.trans (key v)

end RWRS.Support
