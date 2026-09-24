/-
The Step-1 rule capped at `ℓ` stages, matching the paper's `τ_m = T_{J_m}`
with `J_m ≤ ℓ`: stop at the first stage among the first `ℓ` whose trap is
good, at the exit from `K`, or at the horizon, whichever comes first.

Capping at `ℓ` is what makes the failure case harmless: if none of the
first `ℓ` traps is good the rule stops at the exit from `K` or at the
horizon, where the trap potential vanishes or the walk is outside `K`, so
no late-stage term enters the bias estimate.
-/
import RWRS.Support.DTStages
import RWRS.Support.DTBlocks
import RWRS.Support.DTRuleMeas

open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

open scoped Classical in
/-- The times at which the capped rule may fire: the horizon, a time at which
the walk has left `K`, and a stage time among the first `ℓ` whose trap carries
a scenery at most `-ε`. -/
def ruleSetCapped (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (ℓ : ℕ) (K : Finset V) (N : ℕ) (ε : ℝ) (ξ : V → ℝ) (X : ℕ → V) : Set ℕ :=
  {m : ℕ | m = N ∨ (m < N ∧ ((X m ∉ K) ∨
    (∃ i, i ≤ ℓ ∧ (stageState G r C K N X i).1 = m ∧ (∀ j ≤ m, X j ∈ K) ∧
      (stageState G r C K N X i).2 ⊆ K ∧
      ∀ v ∈ C (X m), ξ v ≤ -ε)))}

open scoped Classical in
/-- **The capped rule of Step 1.** -/
noncomputable def trapRuleCapped (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ) (ε : ℝ) (ξ : V → ℝ)
    (X : ℕ → V) : ℕ :=
  sInf (ruleSetCapped G r C ℓ K N ε ξ X)

theorem ruleSetCapped_nonempty (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ)
    (ε : ℝ) (ξ : V → ℝ) (X : ℕ → V) : N ∈ ruleSetCapped G r C ℓ K N ε ξ X := Or.inl rfl

theorem trapRuleCapped_le (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ)
    (ε : ℝ) (ξ : V → ℝ) (X : ℕ → V) : trapRuleCapped G r C ℓ K N ε ξ X ≤ N :=
  Nat.sInf_le (ruleSetCapped_nonempty r C ℓ K N ε ξ X)

theorem trapRuleCapped_mem (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ)
    (ε : ℝ) (ξ : V → ℝ) (X : ℕ → V) :
    trapRuleCapped G r C ℓ K N ε ξ X ∈ ruleSetCapped G r C ℓ K N ε ξ X :=
  Nat.sInf_mem ⟨N, ruleSetCapped_nonempty r C ℓ K N ε ξ X⟩

/-- **The walk is inside `K` before the capped rule fires.** -/
theorem mem_of_lt_trapRuleCapped (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V)
    (N : ℕ) (ε : ℝ) (ξ : V → ℝ) (X : ℕ → V) {k : ℕ}
    (hk : k < trapRuleCapped G r C ℓ K N ε ξ X) : X k ∈ K := by
  by_contra hout
  rcases lt_or_ge k N with hkN | hkN
  · have : k ∈ ruleSetCapped G r C ℓ K N ε ξ X :=
      Or.inr ⟨hkN, Or.inl hout⟩
    exact absurd (Nat.sInf_le this) (not_le.2 hk)
  · exact absurd (le_trans (trapRuleCapped_le r C ℓ K N ε ξ X) hkN) (not_le.2 hk)

/-- **The capped rule is a stopping time.** -/
theorem isStopping_trapRuleCapped (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V)
    {N : ℕ} (hN : 0 < N) (ε : ℝ) (ξ : V → ℝ) :
    RWRS.IsStopping (trapRuleCapped G r C ℓ K N ε ξ) := by
  classical
  intro k X Y hXY hk
  have hagree : ∀ m, m ≤ k →
      (m ∈ ruleSetCapped G r C ℓ K N ε ξ X ↔ m ∈ ruleSetCapped G r C ℓ K N ε ξ Y) := by
    intro m hm
    have hmem : ∀ j ≤ m, X j = Y j := fun j hj => hXY j (le_trans hj hm)
    simp only [ruleSetCapped, Set.mem_setOf_eq]
    constructor
    · rintro (hEq | ⟨h1, h2 | ⟨i, hi1, hi2, hi3, hi5, hi4⟩⟩)
      · exact Or.inl hEq
      · exact Or.inr ⟨h1, Or.inl (by rw [← hmem m le_rfl]; exact h2)⟩
      · have hpre : stageState G r C K N X i = stageState G r C K N Y i :=
          stageState_prefix r C K hN hmem i (le_of_eq hi2)
        refine Or.inr ⟨h1, Or.inr ⟨i, ?_, ?_, ?_, ?_, ?_⟩⟩
        · exact hi1
        · rw [← hpre]; exact hi2
        · intro j hj; rw [← hmem j hj]; exact hi3 j hj
        · rw [← hpre]; exact hi5
        · rw [← hmem m le_rfl]; exact hi4
    · rintro (hEq | ⟨h1, h2 | ⟨i, hi1, hi2, hi3, hi5, hi4⟩⟩)
      · exact Or.inl hEq
      · exact Or.inr ⟨h1, Or.inl (by rw [hmem m le_rfl]; exact h2)⟩
      · have hsym : stageState G r C K N Y i = stageState G r C K N X i :=
          stageState_prefix r C K hN (fun j hj => (hmem j hj).symm) i (le_of_eq hi2)
        refine Or.inr ⟨h1, Or.inr ⟨i, ?_, ?_, ?_, ?_, ?_⟩⟩
        · exact hi1
        · rw [← hsym]; exact hi2
        · intro j hj; rw [hmem j hj]; exact hi3 j hj
        · rw [← hsym]; exact hi5
        · rw [hmem m le_rfl]; exact hi4
  have hXmem : trapRuleCapped G r C ℓ K N ε ξ X ∈ ruleSetCapped G r C ℓ K N ε ξ X :=
    Nat.sInf_mem ⟨N, ruleSetCapped_nonempty r C ℓ K N ε ξ X⟩
  have hXk : trapRuleCapped G r C ℓ K N ε ξ X ≤ k := le_of_eq hk
  have hYmem : k ∈ ruleSetCapped G r C ℓ K N ε ξ Y := by
    rw [hk] at hXmem
    exact (hagree k le_rfl).1 hXmem
  refine le_antisymm (Nat.sInf_le hYmem) ?_
  by_contra hc
  have hlt : sInf (ruleSetCapped G r C ℓ K N ε ξ Y) < k := Nat.lt_of_not_le hc
  have hYm : sInf (ruleSetCapped G r C ℓ K N ε ξ Y) ∈ ruleSetCapped G r C ℓ K N ε ξ Y :=
    Nat.sInf_mem ⟨N, ruleSetCapped_nonempty r C ℓ K N ε ξ Y⟩
  have : sInf (ruleSetCapped G r C ℓ K N ε ξ Y) ∈ ruleSetCapped G r C ℓ K N ε ξ X :=
    (hagree _ hlt.le).2 hYm
  have hle2 := Nat.sInf_le this
  rw [← hk] at hlt
  exact absurd hle2 (not_le.2 (by
    have : trapRuleCapped G r C ℓ K N ε ξ X ≤ sInf (ruleSetCapped G r C ℓ K N ε ξ Y) :=
      hle2
    exact hlt))

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The capped rule's level sets are measurable in the scenery.** -/
theorem measurableSet_trapRuleCapped_le (r : ℕ) (C : V → Finset V) (ℓ : ℕ)
    (K : Finset V) (N : ℕ) (ε : ℝ) (X : ℕ → V) (k : ℕ) :
    MeasurableSet {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X ≤ k} := by
  by_cases hkN : N ≤ k
  · have : {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X ≤ k} = Set.univ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_trans (trapRuleCapped_le r C ℓ K N ε ξ X) hkN
    rw [this]
    exact MeasurableSet.univ
  · have hsplit : {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X ≤ k}
        = ⋃ m ∈ Finset.range (k + 1), {ξ : V → ℝ | m ∈ ruleSetCapped G r C ℓ K N ε ξ X} := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro hle
        have hmem : trapRuleCapped G r C ℓ K N ε ξ X ∈ ruleSetCapped G r C ℓ K N ε ξ X :=
          trapRuleCapped_mem r C ℓ K N ε ξ X
        exact ⟨trapRuleCapped G r C ℓ K N ε ξ X, by omega, hmem⟩
      · rintro ⟨m, hm, hmem⟩
        exact le_trans (Nat.sInf_le hmem) (by omega)
    rw [hsplit]
    refine MeasurableSet.biUnion (Finset.countable_toSet _) ?_
    intro m _
    by_cases h1 : m = N
    · have : {ξ : V → ℝ | m ∈ ruleSetCapped G r C ℓ K N ε ξ X} = Set.univ := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact Or.inl h1
      rw [this]
      exact MeasurableSet.univ
    by_cases h2 : m < N ∧ X m ∉ (K : Set V)
    · have : {ξ : V → ℝ | m ∈ ruleSetCapped G r C ℓ K N ε ξ X} = Set.univ := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact Or.inr ⟨h2.1, Or.inl h2.2⟩
      rw [this]
      exact MeasurableSet.univ
    by_cases h3 : m < N ∧ ∃ i, i ≤ ℓ ∧ (stageState G r C K N X i).1 = m ∧
        (∀ j ≤ m, X j ∈ (K : Set V)) ∧ (stageState G r C K N X i).2 ⊆ K
    · obtain ⟨hmN, i, _, hi1, hi2, hi5⟩ := h3
      have hset : {ξ : V → ℝ | m ∈ ruleSetCapped G r C ℓ K N ε ξ X}
          = trapEvent (C (X m)) ε := by
        ext ξ
        simp only [Set.mem_setOf_eq, ruleSetCapped]
        constructor
        · rintro (hEq | ⟨hlt, (hX : X m ∉ (K : Set V)) | ⟨i', _, hi1', hi2', hi5', hi3'⟩⟩)
          · exact absurd hEq h1
          · exact absurd ⟨hlt, hX⟩ h2
          · exact hi3'
        · intro hξ
          exact Or.inr ⟨hmN, Or.inr ⟨i, ‹i ≤ ℓ›, hi1, hi2, hi5, hξ⟩⟩
      rw [hset]
      exact measurableSet_trapEvent _ _
    · have : {ξ : V → ℝ | m ∈ ruleSetCapped G r C ℓ K N ε ξ X} = ∅ := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, ruleSetCapped]
        intro hmem
        rcases hmem with hEq | ⟨hlt, (hX : X m ∉ (K : Set V)) | hexi⟩
        · exact h1 hEq
        · exact h2 ⟨hlt, hX⟩
        · obtain ⟨i', hi1', hi2', hi3', hi5', hi4'⟩ := hexi
          exact h3 ⟨hlt, ⟨i', hi1', hi2', hi3', hi5'⟩⟩
      rw [this]
      exact MeasurableSet.empty

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The payoff at the capped rule is measurable in the scenery.** -/
theorem measurable_payoff_trapRuleCapped (r : ℕ) (C : V → Finset V) (ℓ : ℕ)
    (K : Finset V) (N : ℕ) (ε : ℝ) (X : ℕ → V) :
    Measurable fun ξ : V → ℝ =>
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X := by
  have hle : ∀ ξ : V → ℝ, trapRuleCapped G r C ℓ K N ε ξ X ≤ N := fun ξ =>
    trapRuleCapped_le r C ℓ K N ε ξ X
  have hrewrite : ∀ ξ : V → ℝ,
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
        = ∑ k ∈ Finset.range N, (if k < trapRuleCapped G r C ℓ K N ε ξ X
            then ξ (X k) / G.degree (X k) else 0) := by
    intro ξ
    unfold RWRS.payoff
    exact sum_range_eq_sum_ite _ _ _ (hle ξ)
  have hfun : (fun ξ : V → ℝ =>
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X)
      = fun ξ : V → ℝ => ∑ k ∈ Finset.range N, (if k < trapRuleCapped G r C ℓ K N ε ξ X
            then ξ (X k) / G.degree (X k) else 0) := funext hrewrite
  rw [hfun]
  refine Finset.measurable_sum _ fun k _ => ?_
  have hSetEq : {ξ : V → ℝ | k < trapRuleCapped G r C ℓ K N ε ξ X}
      = {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X ≤ k}ᶜ := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hS : MeasurableSet {ξ : V → ℝ | k < trapRuleCapped G r C ℓ K N ε ξ X} := by
    rw [hSetEq]
    exact (measurableSet_trapRuleCapped_le r C ℓ K N ε X k).compl
  have hind : Measurable
      fun ξ : V → ℝ => ({ξ : V → ℝ | k < trapRuleCapped G r C ℓ K N ε ξ X}).indicator
        (fun _ => (1 : ℝ)) ξ :=
    Measurable.indicator measurable_const hS
  have hcoord : Measurable fun ξ : V → ℝ => ξ (X k) / G.degree (X k) :=
    (measurable_pi_apply (X k)).div_const _
  have heq : (fun ξ : V → ℝ => if k < trapRuleCapped G r C ℓ K N ε ξ X
      then ξ (X k) / G.degree (X k) else 0)
      = fun ξ : V → ℝ => ({ξ : V → ℝ | k < trapRuleCapped G r C ℓ K N ε ξ X}).indicator
        (fun _ => (1 : ℝ)) ξ * (ξ (X k) / G.degree (X k)) := by
    funext ξ
    by_cases h : k < trapRuleCapped G r C ℓ K N ε ξ X
    · simp [h, Set.indicator_of_mem]
    · simp [h, Set.indicator_of_notMem]
  rw [heq]
  exact hind.mul hcoord

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The capped rule is measurable in the scenery.** -/
theorem measurable_trapRuleCapped (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V)
    (N : ℕ) (ε : ℝ) (X : ℕ → V) :
    Measurable fun ξ : V → ℝ => trapRuleCapped G r C ℓ K N ε ξ X := by
  refine measurable_to_countable' fun n => ?_
  match n with
  | 0 =>
      show MeasurableSet {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X = 0}
      have : {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X = 0}
          = {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X ≤ 0} := by
        ext ξ
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h; exact Nat.le_zero.mpr h
        · intro h; exact Nat.le_antisymm h (Nat.zero_le _)
      rw [this]
      exact measurableSet_trapRuleCapped_le r C ℓ K N ε X 0
  | n + 1 =>
      show MeasurableSet {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X = n + 1}
      have : {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X = n + 1}
          = {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X ≤ n + 1}
              ∩ {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X ≤ n}ᶜ := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
        omega
      rw [this]
      exact (measurableSet_trapRuleCapped_le r C ℓ K N ε X (n + 1)).inter
        (measurableSet_trapRuleCapped_le r C ℓ K N ε X n).compl

/-- **The trap potential at the capped rule is measurable in the scenery.** -/
theorem measurable_trapPotential_trapRuleCapped (r : ℕ) (C : V → Finset V) (ℓ : ℕ)
    (K : Finset V) (N : ℕ) (ε : ℝ) (X : ℕ → V) :
    Measurable fun ξ : V → ℝ =>
      trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X)) := by
  have hpos : Measurable fun ξ : V → ℝ => X (trapRuleCapped G r C ℓ K N ε ξ X) := by
    refine measurable_to_countable' fun v => ?_
    show MeasurableSet {ξ : V → ℝ | X (trapRuleCapped G r C ℓ K N ε ξ X) = v}
    have hfiber : ∀ n : ℕ,
        MeasurableSet {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X = n} :=
      fun n => measurable_trapRuleCapped r C ℓ K N ε X (measurableSet_singleton n)
    have hset : {ξ : V → ℝ | X (trapRuleCapped G r C ℓ K N ε ξ X) = v}
        = ⋃ (n : ℕ), {ξ : V → ℝ | X n = v} ∩
            {ξ : V → ℝ | trapRuleCapped G r C ℓ K N ε ξ X = n} := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨trapRuleCapped G r C ℓ K N ε ξ X, h, rfl⟩
      · rintro ⟨n, hn, hτ⟩; exact hτ ▸ hn
    rw [hset]
    refine MeasurableSet.iUnion fun n => ?_
    by_cases hXv : X n = v
    · have hu : {ξ : V → ℝ | X n = v} = Set.univ := by ext; simp [hXv]
      rw [hu]
      exact MeasurableSet.univ.inter (hfiber n)
    · have he : {ξ : V → ℝ | X n = v} = ∅ := by ext; simp [hXv]
      rw [he]
      exact MeasurableSet.empty.inter (hfiber n)
  have hjoint : Measurable fun p : (V → ℝ) × V =>
      ∑ v ∈ K, p.1 v * RWRS.killedGreenReal G (K : Set V) v p.2 :=
    Finset.measurable_sum _ fun v _ =>
      ((measurable_pi_apply v).comp measurable_fst).mul
        ((measurable_of_countable (f := fun y : V =>
          RWRS.killedGreenReal G (K : Set V) v y)).comp measurable_snd)
  have hpair : Measurable fun ξ : V → ℝ => (ξ, X (trapRuleCapped G r C ℓ K N ε ξ X)) :=
    Measurable.prod measurable_id hpos
  exact hjoint.comp hpair

end RWRS.Support