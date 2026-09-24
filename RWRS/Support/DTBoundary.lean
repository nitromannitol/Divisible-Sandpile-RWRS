/-
The component of the complement of the non-admissible set that contains the
stage centre, and the fact that its boundary lies in the non-admissible set.

Step 1 of `prop:doubly-transient-really-general` restarts the walk at the
stage centre `Y_i` inside the component `D_i` of `V ∖ A_i`; the exit time of
`D_i` is the next stage time because every neighbour of `D_i` outside `D_i`
fails to be admissible (`rwrs.tex:900`).
-/
import RWRS.Support.DTAdmissible

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The finite component of the complement of the non-admissible set, seen
from `y`: the vertices reachable from `y` without passing through a
non-admissible site. -/
def trapComponent (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (F : Finset V)
    (y : V) : Set V :=
  {z : V | ∃ p : G.Walk y z, ∀ v ∈ p.support, Admissible G r F v}

/-- **The boundary of the component lies in the non-admissible set.** -/
theorem not_admissible_of_adjacent_notMem_trapComponent (r : ℕ) (F : Finset V)
    {y z w : V} (hz : z ∈ trapComponent G r F y)
    (hadj : G.Adj z w) (hw : w ∉ trapComponent G r F y) :
    ¬ Admissible G r F w := by
  intro hadm
  obtain ⟨p, hp⟩ := hz
  refine hw ⟨p.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_append] at hv
  rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hv
  simp only [List.tail_cons, List.mem_append, List.mem_singleton] at hv
  rcases hv with hv | hv
  · exact hp v hv
  · rw [hv]; exact hadm

end RWRS.Support
