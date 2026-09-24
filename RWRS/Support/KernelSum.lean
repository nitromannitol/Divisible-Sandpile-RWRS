/-
The iterate of the averaging operator is the transition kernel against the
function: `(P^k h)(x) = ∑_v p_k(x,v) h(v)`, a finite sum because the kernel is
supported on the vertices reachable in `k` steps.
-/
import RWRS.Support.Countable
import RWRS.Support.Green

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem heat_eq_zero_of_notMem_reach :
    ∀ (k : ℕ) (x v : V), v ∉ reach G x k → heat G k x v = 0 := by
  intro k
  induction k with
  | zero =>
      intro x v hv
      have : x ≠ v := by
        intro h; exact hv (by rw [← h]; exact self_mem_reach x 0)
      simp [heat, this]
  | succ k ih =>
      intro x v hv
      rw [heat_succ, walkOp]
      have : ∀ z ∈ G.neighborFinset x, heat G k z v = 0 := by
        intro z hz
        refine ih z v fun hc => hv ?_
        have hz1 : z ∈ reach G x 1 :=
          Finset.mem_biUnion.mpr ⟨x, self_mem_reach x 0,
            Finset.mem_insert_of_mem hz⟩
        exact (by rw [Nat.add_comm] at *; exact reach_trans hz1 k hc :
          v ∈ reach G x (k + 1))
      rw [Finset.sum_congr rfl this]
      simp

theorem walkOp_iterate_eq_sum (h : V → ℝ) :
    ∀ (k : ℕ) (x : V),
      (walkOp G)^[k] h x = ∑ v ∈ reach G x k, heat G k x v * h v := by
  intro k
  induction k with
  | zero =>
      intro x
      simp [reach, heat]
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', walkOp]
      have hleft : ∀ z ∈ G.neighborFinset x,
          (walkOp G)^[k] h z = ∑ v ∈ reach G x (k + 1), heat G k z v * h v := by
        intro z hz
        rw [ih z]
        refine Finset.sum_subset ?_ ?_
        · intro v hv
          have hz1 : z ∈ reach G x 1 :=
            Finset.mem_biUnion.mpr ⟨x, self_mem_reach x 0, Finset.mem_insert_of_mem hz⟩
          exact (by rw [Nat.add_comm]; exact reach_trans hz1 k hv :
            v ∈ reach G x (k + 1))
        · intro v _ hv
          rw [heat_eq_zero_of_notMem_reach k z v hv, zero_mul]
      rw [Finset.sum_congr rfl hleft, Finset.sum_comm]
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [heat_succ, walkOp, div_mul_eq_mul_div, ← Finset.sum_mul]

end RWRS.Support
