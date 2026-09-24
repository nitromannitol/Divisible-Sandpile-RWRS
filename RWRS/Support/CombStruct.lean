/-
Which sites belong to the comb `D_{w,n}`.

The comb consists of the trunk branching vertices `b_0, …, b_{n-1}`, the interior
sites of the `n` trunk pipes, and the interior sites of the sibling pipes hanging
off each trunk branching vertex.  The far endpoints are excluded: the terminal
vertex `(w,0)` of the trunk and the far endpoint of every sibling pipe.
-/
import RWRS.Support.CombPipe

namespace RWRS.Support

variable {B : ℕ} {L : ℕ → ℕ} {n : ℕ} {w : List (Fin B)}

theorem take_ne_nil (hwn : w.length = n) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    (w.take j) ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [List.length_take, hwn] at this
  simp at this
  omega

theorem length_take_eq (hwn : w.length = n) {j : ℕ} (hjn : j ≤ n) :
    (w.take j).length = j := by
  rw [List.length_take, hwn]
  omega

theorem take_prefix_w (j : ℕ) : (w.take j) <+: w := List.take_prefix j w

theorem dropLast_take_prefix (j : ℕ) : (w.take j).dropLast <+: w :=
  (List.dropLast_prefix _).trans (take_prefix_w j)

/-- The interior sites of the `j`-th trunk pipe belong to the comb. -/
theorem mem_combSet_trunk (hwn : w.length = n) {j i : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n)
    (hi : 1 ≤ i) (hiL : i ≤ L j - 1) :
    ((w.take j : List (Fin B)), i) ∈ combSet B L n w := by
  have hlen : (w.take j).length = j := length_take_eq hwn hjn
  refine ⟨Or.inr ⟨take_ne_nil hwn hj hjn, hi, ?_⟩, ?_, dropLast_take_prefix j, Or.inl hi⟩
  · simp only [hlen]; exact hiL
  · simp only [hlen]; exact hjn

/-- The trunk branching vertices `b_j` for `j < n` belong to the comb. -/
theorem mem_combSet_branch (hwn : w.length = n) {j : ℕ} (hjn : j < n) :
    ((w.take j : List (Fin B)), 0) ∈ combSet B L n w := by
  have hlen : (w.take j).length = j := length_take_eq hwn (by omega)
  exact ⟨Or.inl rfl, by simp only [hlen]; omega, dropLast_take_prefix j,
    Or.inr ⟨take_prefix_w j, by simp only [hlen]; exact hjn⟩⟩

/-- The interior sites of a pipe hanging at a trunk branching vertex belong to
the comb. -/
theorem mem_combSet_child (hwn : w.length = n) {j i : ℕ} (hjn : j < n) (c : Fin B)
    (hi : 1 ≤ i) (hiL : i ≤ L (j + 1) - 1) :
    (((w.take j ++ [c] : List (Fin B))), i) ∈ combSet B L n w := by
  have hlen : (w.take j ++ [c]).length = j + 1 := by
    rw [List.length_append, length_take_eq hwn (by omega)]; simp
  refine ⟨Or.inr ⟨by simp, hi, ?_⟩, ?_, ?_, Or.inl hi⟩
  · simp only [hlen]; exact hiL
  · simp only [hlen]; omega
  · simp only [List.dropLast_concat]; exact take_prefix_w j

/-- The far endpoint of the terminal trunk pipe is not in the comb. -/
theorem not_mem_combSet_terminal (hwn : w.length = n) :
    ((w.take n : List (Fin B)), 0) ∉ combSet B L n w := by
  rw [show w.take n = w by rw [← hwn]; simp]
  exact combSet_proper w hwn

/-- The far endpoint of a sibling pipe, one whose letter leaves the trunk, is not
in the comb. -/
theorem not_mem_combSet_sibling (hwn : w.length = n) {j : ℕ} (hjn : j < n) {c : Fin B}
    (hc : w.take j ++ [c] ≠ w.take (j + 1)) :
    (((w.take j ++ [c] : List (Fin B))), 0) ∉ combSet B L n w := by
  rintro ⟨-, -, -, hlast⟩
  rcases hlast with h1 | ⟨hpre, -⟩
  · exact absurd h1 (by simp)
  · apply hc
    have hlen : (w.take j ++ [c]).length = j + 1 := by
      rw [List.length_append, length_take_eq hwn (by omega)]; simp
    have := (List.prefix_iff_eq_take.1 hpre)
    rw [hlen] at this
    exact this

/-- The letters at a trunk branching vertex split into the one that continues the
trunk and the `B - 1` that leave it. -/
theorem take_succ_eq (hwn : w.length = n) {j : ℕ} (hjn : j < n) :
    ∃ c : Fin B, w.take (j + 1) = w.take j ++ [c] := by
  have hjw : j < w.length := by omega
  refine ⟨w.get ⟨j, hjw⟩, ?_⟩
  rw [List.take_add_one]
  congr 1
  simp [List.getElem?_eq_getElem hjw]

end RWRS.Support
