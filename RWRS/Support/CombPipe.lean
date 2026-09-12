/-
The voltage along a pipe of the comb.

`combVoltage_increment` says that the increments of the voltage between
consecutive sites of a pipe are all equal, so the voltage is an arithmetic
progression along the pipe.  Here that is turned into the closed form: with
`d` the drop across the first edge, the voltage at the `i`-th site of the pipe
is `g(parent) - i d`, and at the far endpoint it is `g(parent) - L d`, where `L`
is the length of the pipe.  Reading the closed form at the terminal pipe of the
comb, whose far endpoint carries voltage zero, gives `V_{n-1} = I_n L_n`; at a
sibling pipe it gives the side current `V_j / L_{j+1}`.
-/
import RWRS.Support.CombNode

namespace RWRS.Support

variable {B : ℕ} {L : ℕ → ℕ}

/-- The `i`-th site of the pipe with word `u`, numbered from the parent end:
site `0` is the branching vertex of the parent, sites `1` to `L_{|u|}-1` are the
interior sites, and the far endpoint `(u,0)` is site `L_{|u|}`. -/
def pipeAt (B : ℕ) (u : List (Fin B)) (i : ℕ) : List (Fin B) × ℕ :=
  if i = 0 then (u.dropLast, 0) else (u, i)

/-- The drop of the voltage across the first edge of the pipe with word `u`. -/
noncomputable def pipeDrop (B : ℕ) (L : ℕ → ℕ) (e : Bool) (n : ℕ) (w : List (Fin B))
    (u : List (Fin B)) : ℝ :=
  combVoltage B L e n w (u.dropLast, 0) - combVoltage B L e n w (u, 1)

theorem pipePred_pipeAt {u : List (Fin B)} (i : ℕ) :
    pipePred B L ((u : List (Fin B)), i + 1) = pipeAt B u i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp [pipePred, pipeAt]
  · have hi : i ≠ 0 := by omega
    simp [pipePred, pipeAt, hi]

theorem pipeUp_lt {u : List (Fin B)} {i : ℕ} (h : i + 1 ≤ L u.length - 1) :
    pipeUp B L ((u : List (Fin B)), i) = (u, i + 1) := by
  simp [pipeUp, h]

theorem pipeUp_top {u : List (Fin B)} {i : ℕ} (h : ¬ (i + 1 ≤ L u.length - 1)) :
    pipeUp B L ((u : List (Fin B)), i) = (u, 0) := by
  simp [pipeUp, h]

section

variable {n : ℕ} {w : List (Fin B)}

/-- **The voltage is affine along a pipe.** -/
theorem pipe_affine (hB : 1 ≤ B) (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) {u : List (Fin B)} (hu : u ≠ [])
    (hmem : ∀ i, 1 ≤ i → i ≤ L u.length - 1 → ((u : List (Fin B)), i) ∈ combSet B L n w) :
    ∀ i, i ≤ L u.length - 1 →
      combVoltage B L e n w (pipeAt B u i)
        = combVoltage B L e n w (u.dropLast, 0) - i * pipeDrop B L e n w u := by
  set g := combVoltage B L e n w with hg
  set d := pipeDrop B L e n w u with hd
  have key : ∀ i : ℕ,
      (i ≤ L u.length - 1 → g (pipeAt B u i) = g (u.dropLast, 0) - i * d) ∧
      (i + 1 ≤ L u.length - 1 → g (pipeAt B u (i + 1)) = g (u.dropLast, 0) - (i + 1) * d) := by
    intro i
    induction i with
    | zero =>
        constructor
        · intro _
          simp [pipeAt]
        · intro _
          simp only [pipeAt, Nat.zero_add, if_neg (by omega : ¬ (1 : ℕ) = 0)]
          rw [hd, pipeDrop]
          push_cast
          ring
    | succ i ih =>
        refine ⟨fun h => by have := ih.2 h; push_cast at this ⊢; linarith, ?_⟩
        intro hle
        have h1 : i + 1 ≤ L u.length - 1 := by omega
        have hinc := combVoltage_increment hB hL e hwn hn hu (i := i + 1)
          (by omega) h1 (hmem (i + 1) (by omega) h1)
        rw [pipeUp_lt (by omega : i + 1 + 1 ≤ L u.length - 1), pipePred_pipeAt] at hinc
        have e1 := ih.1 (by omega)
        have e2 := ih.2 h1
        have hA : pipeAt B u (i + 1 + 1) = ((u : List (Fin B)), i + 1 + 1) := by
          simp [pipeAt]
        rw [hA]
        have hB2 : pipeAt B u (i + 1) = ((u : List (Fin B)), i + 1) := by
          simp [pipeAt]
        rw [hB2] at e2
        push_cast at e1 e2 ⊢
        linarith
  intro i hi
  exact (key i).1 hi

/-- **The voltage at the far endpoint of a pipe.** -/
theorem pipe_far (hB : 1 ≤ B) (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    (hwn : w.length = n) (hn : 1 ≤ n) {u : List (Fin B)} (hu : u ≠ [])
    (hL2 : 2 ≤ L u.length)
    (hmem : ∀ i, 1 ≤ i → i ≤ L u.length - 1 → ((u : List (Fin B)), i) ∈ combSet B L n w) :
    combVoltage B L e n w ((u : List (Fin B)), 0)
      = combVoltage B L e n w (u.dropLast, 0) - (L u.length : ℝ) * pipeDrop B L e n w u := by
  set g := combVoltage B L e n w with hg
  set d := pipeDrop B L e n w u with hd
  obtain ⟨m, hm⟩ : ∃ m, L u.length = m + 2 := ⟨L u.length - 2, by omega⟩
  have hinc := combVoltage_increment hB hL e hwn hn hu (i := m + 1)
    (by omega) (by omega) (hmem (m + 1) (by omega) (by omega))
  rw [pipeUp_top (by omega : ¬ (m + 1 + 1 ≤ L u.length - 1)), pipePred_pipeAt] at hinc
  have e1 := pipe_affine hB hL e hwn hn hu hmem (m + 1) (by omega)
  have e2 := pipe_affine hB hL e hwn hn hu hmem m (by omega)
  have hA : pipeAt B u (m + 1) = ((u : List (Fin B)), m + 1) := by simp [pipeAt]
  rw [hA] at e1
  rw [hm]
  push_cast at e1 e2 ⊢
  linarith

end

end RWRS.Support
