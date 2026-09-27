import RWRS.Support.DTAdmissible
import LatticeProb.Graph.ExitTime

/-!
# Exit from the non-admissible set

This module records that the walk almost surely reaches the admissible set:
for a doubly transient graph, the vertices failing `Admissible G r F` for a
fixed finite used set `F` form a finite set, and an infinite connected graph
escapes every finite set almost surely, so the exit time of the
non-admissible set is finite almost surely.
-/

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

/-- **The walk reaches the admissible set of a fixed used set almost surely.**
The sites that fail to be admissible for `F` form a finite set, and from every
vertex of an infinite connected graph some vertex outside that finite set is
reachable, so the exit time of the non-admissible set is finite almost surely. -/
theorem ae_exitTime_notAdmissible_ne_top [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (hdt : RWRS.DoublyTransient G) (r : ℕ) (F : Finset V)
    (x : V) :
    ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G x),
      RWRS.exitTime {z : V | ¬ Admissible G r F z} X ≠ ⊤ := by
  classical
  obtain ⟨C, hC⟩ := (finite_not_admissible hdt r F).exists_finset_coe
  rw [← hC]
  have hinf := (finite_not_admissible hdt r F).infinite_compl
  exact LatticeProb.Graph.ae_exitTime_ne_top hdeg C (fun y => by
    obtain ⟨q, hq⟩ := hinf.nonempty
    exact ⟨q, (hG.preconnected y q).some, by rw [hC]; exact hq⟩) x

end RWRS.Support