/-
The stage sequence of the trap selection, at a horizon and inside a finite set.

The centres of the traps are selected along the walk, and the selection reads the
WALK ALONE: the scenery never enters it.  So, conditionally on the walk, the trap
sets are fixed pairwise disjoint finite sets and the events that the scenery is
uniformly negative on them are independent block events.

Everything here is at a finite horizon `N` and inside a finite set `K`, which is
what makes the stage times ordinary `ℕ`-valued stopping times: the recursion looks
for the first later time at which the walk is still inside `K` and admissible for
the sites already used, and takes the horizon when there is none.
-/
import RWRS.Support.DTTrapFamily

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

open scoped Classical in
/-- The times at which the next stage may fire: the horizon, and every later time
at which the walk is still inside `K` and admissible for the sites used so far. -/
def stageSet (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (K : Finset V) (N : ℕ)
    (X : ℕ → V) (p : ℕ × Finset V) : Set ℕ :=
  {m : ℕ | m = N ∨ (p.1 < m ∧ m < N ∧ (∀ j ≤ m, X j ∈ K) ∧ Admissible G r p.2 (X m))}

open scoped Classical in
/-- One step of the stage recursion. -/
noncomputable def stageStep (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (K : Finset V) (N : ℕ) (X : ℕ → V) (p : ℕ × Finset V) : ℕ × Finset V :=
  (sInf (stageSet G r K N X p), p.2 ∪ C (X (sInf (stageSet G r K N X p))))

open scoped Classical in
/-- The `i`-th stage time and the trap sites used up to it. -/
noncomputable def stageState (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (K : Finset V) (N : ℕ) (X : ℕ → V) : ℕ → ℕ × Finset V
  | 0 => (0, C (X 0))
  | i + 1 => stageStep G r C K N X (stageState G r C K N X i)

theorem stageSet_nonempty (r : ℕ) (K : Finset V) (N : ℕ) (X : ℕ → V) (p : ℕ × Finset V) :
    N ∈ stageSet G r K N X p := Or.inl rfl

theorem sInf_stageSet_le (r : ℕ) (K : Finset V) (N : ℕ) (X : ℕ → V) (p : ℕ × Finset V) :
    sInf (stageSet G r K N X p) ≤ N :=
  Nat.sInf_le (stageSet_nonempty r K N X p)

theorem stageState_le (r : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ} (hN : 0 < N)
    (X : ℕ → V) : ∀ i, (stageState G r C K N X i).1 ≤ N := by
  intro i
  cases i with
  | zero => exact hN.le
  | succ i => exact sInf_stageSet_le r K N X _

/-- **The stage times are nondecreasing.** -/
theorem stageState_mono (r : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ} (hN : 0 < N)
    (X : ℕ → V) (i : ℕ) :
    (stageState G r C K N X i).1 ≤ (stageState G r C K N X (i + 1)).1 := by
  set p := stageState G r C K N X i with hp
  have hmem : sInf (stageSet G r K N X p) ∈ stageSet G r K N X p :=
    Nat.sInf_mem ⟨N, stageSet_nonempty r K N X p⟩
  simp only [stageState, stageStep]
  rcases hmem with h | h
  · rw [h]; exact stageState_le r C K hN X i
  · exact h.1.le

theorem stageState_mono' (r : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ} (hN : 0 < N)
    (X : ℕ → V) : Monotone fun i => (stageState G r C K N X i).1 :=
  monotone_nat_of_le_succ fun i => stageState_mono r C K hN X i

open scoped Classical in
/-- The trap sites used up to stage `i` are the union of the trap sets of the
centres of the stages up to `i`. -/
theorem stageState_snd (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ) (X : ℕ → V) :
    ∀ i, (stageState G r C K N X i).2
      = (Finset.range (i + 1)).biUnion fun j => C (X (stageState G r C K N X j).1) := by
  classical
  intro i
  induction i with
  | zero => simp [stageState]
  | succ i ih =>
      have h1 : (stageState G r C K N X (i + 1)).2
          = (stageState G r C K N X i).2 ∪ C (X (stageState G r C K N X (i + 1)).1) := rfl
      have h2 : (Finset.range (i + 1 + 1)).biUnion (fun j => C (X (stageState G r C K N X j).1))
          = C (X (stageState G r C K N X (i + 1)).1)
            ∪ (Finset.range (i + 1)).biUnion (fun j => C (X (stageState G r C K N X j).1)) := by
        rw [Finset.range_add_one, Finset.biUnion_insert]
      rw [h1, ih, h2]
      exact Finset.union_comm _ _

/-- **The stage sequence is decided by the walk up to the stage time.** -/
theorem stageState_prefix (r : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ} (hN : 0 < N)
    {X Y : ℕ → V} {k : ℕ} (h : ∀ j ≤ k, X j = Y j) :
    ∀ i, (stageState G r C K N X i).1 ≤ k →
      stageState G r C K N X i = stageState G r C K N Y i := by
  intro i
  induction i with
  | zero =>
      intro _
      simp only [stageState]
      rw [h 0 (Nat.zero_le k)]
  | succ i ih =>
      intro hle
      have hi : (stageState G r C K N X i).1 ≤ k :=
        le_trans (stageState_mono r C K hN X i) hle
      have hp := ih hi
      set p := stageState G r C K N X i with hpdef
      have hagree : ∀ m, m ≤ k → (m ∈ stageSet G r K N X p ↔ m ∈ stageSet G r K N Y p) := by
        intro m hm
        simp only [stageSet, Set.mem_setOf_eq]
        constructor
        · rintro (hEq | ⟨h1, h2, h3, h4⟩)
          · exact Or.inl hEq
          · refine Or.inr ⟨h1, h2, fun j hj => ?_, ?_⟩
            · rw [← h j (le_trans hj hm)]; exact h3 j hj
            · rw [← h m hm]; exact h4
        · rintro (hEq | ⟨h1, h2, h3, h4⟩)
          · exact Or.inl hEq
          · refine Or.inr ⟨h1, h2, fun j hj => ?_, ?_⟩
            · rw [h j (le_trans hj hm)]; exact h3 j hj
            · rw [h m hm]; exact h4
      have hXmem : sInf (stageSet G r K N X p) ∈ stageSet G r K N X p :=
        Nat.sInf_mem ⟨N, stageSet_nonempty r K N X p⟩
      have hXle : sInf (stageSet G r K N X p) ≤ k := hle
      have hYmem : sInf (stageSet G r K N X p) ∈ stageSet G r K N Y p :=
        (hagree _ hXle).1 hXmem
      have h1 : sInf (stageSet G r K N Y p) ≤ sInf (stageSet G r K N X p) := Nat.sInf_le hYmem
      have h2 : sInf (stageSet G r K N X p) ≤ sInf (stageSet G r K N Y p) := by
        by_contra hc
        have hlt : sInf (stageSet G r K N Y p) < sInf (stageSet G r K N X p) :=
          Nat.lt_of_not_le hc
        have hYmem' : sInf (stageSet G r K N Y p) ∈ stageSet G r K N Y p :=
          Nat.sInf_mem ⟨N, stageSet_nonempty r K N Y p⟩
        have hYk : sInf (stageSet G r K N Y p) ≤ k := le_trans hlt.le hXle
        exact absurd (Nat.sInf_le ((hagree _ hYk).2 hYmem')) (not_le.2 hlt)
      have heq : sInf (stageSet G r K N X p) = sInf (stageSet G r K N Y p) :=
        le_antisymm h2 h1
      have hXY : X (sInf (stageSet G r K N X p)) = Y (sInf (stageSet G r K N X p)) :=
        h _ hXle
      show stageStep G r C K N X p = stageStep G r C K N Y (stageState G r C K N Y i)
      rw [← hp]
      classical
      have hsnd : (stageStep G r C K N X p).2 = (stageStep G r C K N Y p).2 := by
        show p.2 ∪ C (X (sInf (stageSet G r K N X p)))
          = p.2 ∪ C (Y (sInf (stageSet G r K N Y p)))
        rw [← heq, hXY]
      exact Prod.ext heq hsnd

/-! ### The stopping rule -/

open scoped Classical in
/-- The times at which the rule may fire: the horizon, a time at which the walk
has left `K`, and a stage time whose trap carries a scenery at most `-ε`. -/
def ruleSet (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V) (K : Finset V)
    (N : ℕ) (ε : ℝ) (ξ : V → ℝ) (X : ℕ → V) : Set ℕ :=
  {m : ℕ | m = N ∨ (m < N ∧ ((X m ∉ K) ∨
    (∃ i, (stageState G r C K N X i).1 = m ∧ (∀ j ≤ m, X j ∈ K) ∧ ∀ v ∈ C (X m), ξ v ≤ -ε)))}

open scoped Classical in
/-- **The rule of Step 1**: stop at the first stage whose trap is good, at the exit
from `K`, or at the horizon, whichever comes first. -/
noncomputable def trapRule (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (K : Finset V) (N : ℕ) (ε : ℝ) (ξ : V → ℝ) (X : ℕ → V) : ℕ :=
  sInf (ruleSet G r C K N ε ξ X)

theorem ruleSet_nonempty (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ) (ε : ℝ)
    (ξ : V → ℝ) (X : ℕ → V) : N ∈ ruleSet G r C K N ε ξ X := Or.inl rfl

theorem trapRule_le (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ) (ε : ℝ)
    (ξ : V → ℝ) (X : ℕ → V) : trapRule G r C K N ε ξ X ≤ N :=
  Nat.sInf_le (ruleSet_nonempty r C K N ε ξ X)

/-- **The rule is a stopping time.** -/
theorem isStopping_trapRule (r : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ} (hN : 0 < N)
    (ε : ℝ) (ξ : V → ℝ) : RWRS.IsStopping (trapRule G r C K N ε ξ) := by
  classical
  intro k X Y hXY hk
  have hagree : ∀ m, m ≤ k →
      (m ∈ ruleSet G r C K N ε ξ X ↔ m ∈ ruleSet G r C K N ε ξ Y) := by
    intro m hm
    have hmem : ∀ j ≤ m, X j = Y j := fun j hj => hXY j (le_trans hj hm)
    simp only [ruleSet, Set.mem_setOf_eq]
    constructor
    · rintro (hEq | ⟨h1, h2 | ⟨i, hi1, hi2, hi3⟩⟩)
      · exact Or.inl hEq
      · exact Or.inr ⟨h1, Or.inl (by rw [← hmem m le_rfl]; exact h2)⟩
      · refine Or.inr ⟨h1, Or.inr ⟨i, ?_, ?_, ?_⟩⟩
        · rw [← stageState_prefix r C K hN hmem i (le_of_eq hi1)]; exact hi1
        · intro j hj; rw [← hmem j hj]; exact hi2 j hj
        · rw [← hmem m le_rfl]; exact hi3
    · rintro (hEq | ⟨h1, h2 | ⟨i, hi1, hi2, hi3⟩⟩)
      · exact Or.inl hEq
      · exact Or.inr ⟨h1, Or.inl (by rw [hmem m le_rfl]; exact h2)⟩
      · refine Or.inr ⟨h1, Or.inr ⟨i, ?_, ?_, ?_⟩⟩
        · have hsym : stageState G r C K N Y i = stageState G r C K N X i :=
            stageState_prefix r C K hN (fun j hj => (hmem j hj).symm) i (le_of_eq hi1)
          rw [← hsym]; exact hi1
        · intro j hj; rw [hmem j hj]; exact hi2 j hj
        · rw [hmem m le_rfl]; exact hi3
  have hXmem : trapRule G r C K N ε ξ X ∈ ruleSet G r C K N ε ξ X :=
    Nat.sInf_mem ⟨N, ruleSet_nonempty r C K N ε ξ X⟩
  have hXk : trapRule G r C K N ε ξ X ≤ k := le_of_eq hk
  have hYmem : k ∈ ruleSet G r C K N ε ξ Y := by
    rw [hk] at hXmem
    exact (hagree k le_rfl).1 hXmem
  refine le_antisymm (Nat.sInf_le hYmem) ?_
  by_contra hc
  have hlt : sInf (ruleSet G r C K N ε ξ Y) < k := Nat.lt_of_not_le hc
  have hYm : sInf (ruleSet G r C K N ε ξ Y) ∈ ruleSet G r C K N ε ξ Y :=
    Nat.sInf_mem ⟨N, ruleSet_nonempty r C K N ε ξ Y⟩
  have : sInf (ruleSet G r C K N ε ξ Y) ∈ ruleSet G r C K N ε ξ X :=
    (hagree _ hlt.le).2 hYm
  have := Nat.sInf_le this
  rw [← hk] at hlt
  exact absurd this (not_le.2 hlt)

theorem trapRule_mem (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ) (ε : ℝ)
    (ξ : V → ℝ) (X : ℕ → V) :
    trapRule G r C K N ε ξ X ∈ ruleSet G r C K N ε ξ X :=
  Nat.sInf_mem ⟨N, ruleSet_nonempty r C K N ε ξ X⟩

/-- **The walk is inside `K` before the rule fires.**  This is the hypothesis
`walkExp_payoff_add_trapPotential` asks for, with `D = K`. -/
theorem mem_of_lt_trapRule (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ) (ε : ℝ)
    (ξ : V → ℝ) (X : ℕ → V) {k : ℕ} (hk : k < trapRule G r C K N ε ξ X) : X k ∈ K := by
  classical
  by_contra hc
  have hkN : k < N := lt_of_lt_of_le hk (trapRule_le r C K N ε ξ X)
  have hmem : k ∈ ruleSet G r C K N ε ξ X := Or.inr ⟨hkN, Or.inl hc⟩
  exact absurd (Nat.sInf_le hmem) (not_le.2 hk)

/-- **The trap sets of two distinct stages are disjoint**, as soon as the later
one is a genuine stage and not the horizon. -/
theorem disjoint_stage_traps (r : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ}
    (hCball : ∀ y : V, ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r)
    (hCself : ∀ y : V, y ∈ C y) (X : ℕ → V) {i j : ℕ} (hij : i < j)
    (hj : (stageState G r C K N X j).1 < N) :
    Disjoint ((C (X (stageState G r C K N X i).1) : Finset V) : Set V)
      ((C (X (stageState G r C K N X j).1) : Finset V) : Set V) := by
  classical
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  set p := stageState G r C K N X j' with hp
  have hTj : (stageState G r C K N X (j' + 1)).1 = sInf (stageSet G r K N X p) := rfl
  have hmem : sInf (stageSet G r K N X p) ∈ stageSet G r K N X p :=
    Nat.sInf_mem ⟨N, stageSet_nonempty r K N X p⟩
  rcases hmem with hEq | ⟨h1, h2, h3, h4⟩
  · rw [hTj, hEq] at hj
    exact absurd hj (lt_irrefl N)
  · have hYi : X (stageState G r C K N X i).1 ∈ p.2 := by
      rw [hp, stageState_snd]
      exact Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (by omega), hCself _⟩
    have hfar := h4.1 _ hYi
    rw [hTj]
    exact (disjoint_trap_of_far (hCball _) (hCball _) hfar).symm

end RWRS.Support
