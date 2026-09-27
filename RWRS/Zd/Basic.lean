/-
The specialization of the general-graph setting to the nearest-neighbour
lattice `ℤ^d` of the shared library, in the vocabulary the dependent
formalizations use: the graph is `LatticeProb.lattice d`, every vertex has
degree `2d`, and the averaging operator is `LatticeProb.walkOp`.
-/
import RWRS.Support.HeatBasic
import RWRS.Support.Green
import LatticeProb.Site

namespace RWRS.Zd

open LatticeProb

variable {d : ℕ}

/-- `y` lies in the explicit neighbor `Finset` of `x` iff it is `x` shifted by a unit
vector `± unit i` in some coordinate `i`. -/
theorem mem_nbrFinset {x y : Site d} :
    y ∈ nbrFinset x ↔ ∃ i : Fin d, y = x + unit i ∨ y = x - unit i := by
  simp [nbrFinset]

/-- Adjacency on `lattice d` is exactly differing from `x` by a unit vector `± unit i` in
one coordinate `i`. -/
theorem adj_iff {x y : Site d} :
    (lattice d).Adj x y ↔ ∃ i : Fin d, y = x + unit i ∨ y = x - unit i := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, Or.inl hi⟩
    · exact ⟨i, Or.inr (by rw [hi]; abel)⟩

/-- The graph's `neighborSet` of `x` coincides with the explicit `Finset` `nbrFinset x`, by
`adj_iff`. -/
theorem neighborSet_eq (x : Site d) :
    (lattice d).neighborSet x = ↑(nbrFinset x) := by
  ext y
  simp only [SimpleGraph.mem_neighborSet, Finset.mem_coe, mem_nbrFinset]
  exact adj_iff

/-- `lattice d` is locally finite, since `neighborSet_eq` identifies each neighbor set with
the finite set `nbrFinset x`. -/
noncomputable instance latticeLocallyFinite (d : ℕ) : (lattice d).LocallyFinite := fun x =>
  Set.Finite.fintype (by rw [neighborSet_eq]; exact (nbrFinset x).finite_toSet)

/-- The graph's `neighborFinset` of `x` equals the explicit `nbrFinset x`, by `adj_iff`. -/
theorem neighborFinset_eq (x : Site d) :
    (lattice d).neighborFinset x = nbrFinset x := by
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  exact adj_iff.trans mem_nbrFinset.symm

/-- `nbrFinset x` has exactly `2 * d` elements: the `d` coordinate directions each contribute
two distinct neighbors `x ± unit i`. -/
theorem card_nbrFinset (x : Site d) : (nbrFinset x).card = 2 * d := by
  classical
  rw [nbrFinset, Finset.card_biUnion]
  · have : ∀ i : Fin d, ({x + unit i, x - unit i} : Finset (Site d)).card = 2 := by
      intro i
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp only [Finset.mem_singleton]
      intro h
      have := congrFun h i
      simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
      omega
    simp [this, Finset.sum_const, mul_comm]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-- Every site of `lattice d` has degree `2 * d`, from `neighborFinset_eq` and the count
`card_nbrFinset`. -/
theorem degree_eq (x : Site d) : (lattice d).degree x = 2 * d := by
  rw [SimpleGraph.degree, neighborFinset_eq, card_nbrFinset]

/-- `RWRS.walkOp` on `lattice d` agrees with the library's `LatticeProb.walkOp`: both average
`f` over the same `2 * d` neighbors, transferred via `neighborFinset_eq` and `degree_eq`. -/
theorem walkOp_eq (f : Site d → ℝ) (x : Site d) :
    RWRS.walkOp (lattice d) f x = LatticeProb.walkOp f x := by
  classical
  rw [RWRS.walkOp, LatticeProb.walkOp, degree_eq, neighborFinset_eq, LatticeProb.nbrSum,
    nbrFinset, Finset.sum_biUnion]
  · rw [show ((2 * d : ℕ) : ℝ) = 2 * (d : ℝ) from by push_cast; ring]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_insert, Finset.sum_singleton]
    simp only [Finset.mem_singleton]
    intro h
    have := congrFun h i
    simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same] at this
    omega
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl) (h | h) <;>
      · have h1 := congrFun h i
        have h2 := congrFun h j
        simp [unit, Pi.single_eq_same, Pi.single_eq_of_ne, hij] at h1 h2

/-! ### The lattice is infinite and connected -/

/-- `Site d` is infinite when `d ≠ 0`, injecting `ℤ` into a fixed coordinate of the site. -/
instance latticeInfinite (d : ℕ) [NeZero d] : Infinite (Site d) :=
  Infinite.of_injective (fun n : ℤ => (Pi.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩ n : Site d))
    (fun a b h => by
      have := congrFun h ⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩
      simpa using this)

/-- Any integer multiple `k • unit i` of a unit vector is reachable from `x` on `lattice d`,
by induction on `k` stepping one lattice edge at a time. -/
theorem reachable_add_zsmul (x : Site d) (i : Fin d) (k : ℤ) :
    (lattice d).Reachable x (x + k • unit i) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      refine adj_iff.mpr ⟨i, Or.inl ?_⟩
      module
  | pred n ih =>
      refine ih.trans (SimpleGraph.Adj.reachable ?_)
      refine adj_iff.mpr ⟨i, Or.inr ?_⟩
      module

/-- Any finite integer combination `∑ i ∈ s, c i • unit i` of unit vectors is reachable from
`x`, by induction on the finite set `s` using `reachable_add_zsmul` at each step. -/
theorem reachable_add_sum (x : Site d) (c : Fin d → ℤ) (s : Finset (Fin d)) :
    (lattice d).Reachable x (x + ∑ i ∈ s, c i • unit i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi,
        show x + (c i • unit i + ∑ j ∈ s, c j • unit j)
          = (x + ∑ j ∈ s, c j • unit j) + c i • unit i from by abel]
      exact ih.trans (reachable_add_zsmul _ i _)

/-- `lattice d` is connected: every site `y` is `x` plus an integer combination of unit
vectors, reachable from `x` by `reachable_add_sum`. -/
theorem latticeConnected (d : ℕ) [NeZero d] : (lattice d).Connected := by
  classical
  have hpre : ∀ x y : Site d, (lattice d).Reachable x y := by
    intro x y
    have hy : y = x + ∑ i : Fin d, (y i - x i) • unit i := by
      funext j
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, unit, Pi.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j (fun i => y i - x i)]
      simp
    rw [hy]
    exact reachable_add_sum x _ _
  exact ⟨hpre⟩

end RWRS.Zd
