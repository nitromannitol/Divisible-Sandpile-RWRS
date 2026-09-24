/-
Measurability of the Step-1 rule in the scenery: for a fixed trajectory, the
level sets of the rule are measurable, because membership in the rule set
is, in the scenery, a single trap event.
-/
import RWRS.Support.DTStages
import RWRS.Support.DTBlocks

open MeasureTheory

namespace RWRS.Support

/-- A sum up to a bounded index is the truncated sum: for `τ ≤ N`,
`∑_{k<τ} f k = ∑_{k<N} if k < τ then f k else 0`. -/
theorem sum_range_eq_sum_ite {M : Type*} [AddCommMonoid M] (f : ℕ → M) (τ N : ℕ)
    (hτ : τ ≤ N) :
    ∑ k ∈ Finset.range τ, f k
      = ∑ k ∈ Finset.range N, if k < τ then f k else 0 := by
  revert hτ
  induction N with
  | zero =>
      intro hτ
      have h0 : τ = 0 := by omega
      subst h0
      simp
  | succ N ih =>
      intro hτ
      by_cases hτN : τ ≤ N
      · rw [Finset.sum_range_succ, ih hτN]
        have hnl : ¬ N < τ := by omega
        simp [hnl]
      · have hτeq : τ = N + 1 := by omega
        subst hτeq
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hlt : N < N + 1 := by omega
        simp only [if_pos hlt]
        refine congrArg (· + f N) ?_
        refine Finset.sum_congr rfl ?_
        intro x hx
        have hxl : x < N + 1 := (Finset.mem_range.mp hx).trans (by omega)
        simp only [if_pos hxl]


variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
open scoped Classical in
/-- **The rule's level sets are measurable in the scenery.**  For a fixed
trajectory `X`, the event `{ξ : τ(ξ) X ≤ k}` is measurable: the rule is the
least element of a set whose membership in `ξ` is a single trap event. -/
theorem measurableSet_trapRule_le (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ) (ε : ℝ)
    (X : ℕ → V) (k : ℕ) :
    MeasurableSet {ξ : V → ℝ | trapRule G r C K N ε ξ X ≤ k} := by
  by_cases hkN : N ≤ k
  · have : {ξ : V → ℝ | trapRule G r C K N ε ξ X ≤ k} = Set.univ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact le_trans (trapRule_le r C K N ε ξ X) hkN
    rw [this]
    exact MeasurableSet.univ
  · have hsplit : {ξ : V → ℝ | trapRule G r C K N ε ξ X ≤ k}
        = ⋃ m ∈ Finset.range (k + 1), {ξ : V → ℝ | m ∈ ruleSet G r C K N ε ξ X} := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro hle
        have hmem : trapRule G r C K N ε ξ X ∈ ruleSet G r C K N ε ξ X :=
          trapRule_mem r C K N ε ξ X
        have hle2 : trapRule G r C K N ε ξ X ≤ k := hle
        exact ⟨trapRule G r C K N ε ξ X, by omega, hmem⟩
      · rintro ⟨m, hm, hmem⟩
        exact le_trans (Nat.sInf_le hmem) (by omega)
    rw [hsplit]
    refine MeasurableSet.biUnion (Finset.countable_toSet _) ?_
    intro m _
    by_cases h1 : m = N
    · have : {ξ : V → ℝ | m ∈ ruleSet G r C K N ε ξ X} = Set.univ := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact Or.inl h1
      rw [this]
      exact MeasurableSet.univ
    by_cases h2 : m < N ∧ X m ∉ (K : Set V)
    · have : {ξ : V → ℝ | m ∈ ruleSet G r C K N ε ξ X} = Set.univ := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact Or.inr ⟨h2.1, Or.inl h2.2⟩
      rw [this]
      exact MeasurableSet.univ
    by_cases h3 : m < N ∧ ∃ i, (stageState G r C K N X i).1 = m ∧
        ∀ j ≤ m, X j ∈ (K : Set V)
    · obtain ⟨hmN, i, hi1, hi2⟩ := h3
      have hset : {ξ : V → ℝ | m ∈ ruleSet G r C K N ε ξ X}
          = trapEvent (C (X m)) ε := by
        ext ξ
        simp only [Set.mem_setOf_eq, ruleSet]
        constructor
        · rintro (hEq | ⟨hlt, (hX : X m ∉ (K : Set V)) | ⟨i', hi1', hi2', hi3'⟩⟩)
          · exact absurd hEq h1
          · exact absurd ⟨hlt, hX⟩ h2
          · exact hi3'
        · intro hξ
          exact Or.inr ⟨hmN, Or.inr ⟨i, hi1, hi2, hξ⟩⟩
      rw [hset]
      exact measurableSet_trapEvent _ _
    · have : {ξ : V → ℝ | m ∈ ruleSet G r C K N ε ξ X} = ∅ := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, ruleSet]
        intro hmem
        rcases hmem with hEq | ⟨hlt, (hX : X m ∉ (K : Set V)) | hexi⟩
        · exact h1 hEq
        · exact h2 ⟨hlt, hX⟩
        · obtain ⟨i', hrest⟩ := hexi
          obtain ⟨hi1', hi2', hi3'⟩ := hrest
          exact h3 ⟨hlt, ⟨i', hi1', hi2'⟩⟩
      rw [this]
      exact MeasurableSet.empty


omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The payoff at the rule is measurable in the scenery.**  For a fixed
trajectory, the payoff collected by the rule is a finite sum of coordinate
terms cut off at the rule's level sets. -/
theorem measurable_payoff_trapRule (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ)
    (ε : ℝ) (X : ℕ → V) :
    Measurable fun ξ : V → ℝ =>
      RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X := by
  have hle : ∀ ξ : V → ℝ, trapRule G r C K N ε ξ X ≤ N := fun ξ =>
    trapRule_le r C K N ε ξ X
  have hrewrite : ∀ ξ : V → ℝ,
      RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X
        = ∑ k ∈ Finset.range N, (if k < trapRule G r C K N ε ξ X
            then ξ (X k) / G.degree (X k) else 0) := by
    intro ξ
    unfold RWRS.payoff
    exact sum_range_eq_sum_ite _ _ _ (hle ξ)
  have hfun : (fun ξ : V → ℝ =>
      RWRS.payoff G ξ (trapRule G r C K N ε ξ X) X)
      = fun ξ : V → ℝ => ∑ k ∈ Finset.range N, (if k < trapRule G r C K N ε ξ X
            then ξ (X k) / G.degree (X k) else 0) := funext hrewrite
  rw [hfun]
  refine Finset.measurable_sum _ fun k _ => ?_
  have hSetEq : {ξ : V → ℝ | k < trapRule G r C K N ε ξ X}
      = {ξ : V → ℝ | trapRule G r C K N ε ξ X ≤ k}ᶜ := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hS : MeasurableSet {ξ : V → ℝ | k < trapRule G r C K N ε ξ X} := by
    rw [hSetEq]
    exact (measurableSet_trapRule_le r C K N ε X k).compl
  have hind : Measurable
      fun ξ : V → ℝ => ({ξ : V → ℝ | k < trapRule G r C K N ε ξ X}).indicator
        (fun _ => (1 : ℝ)) ξ :=
    Measurable.indicator measurable_const hS
  have hcoord : Measurable fun ξ : V → ℝ => ξ (X k) / G.degree (X k) :=
    (measurable_pi_apply (X k)).div_const _
  have heq : (fun ξ : V → ℝ => if k < trapRule G r C K N ε ξ X
      then ξ (X k) / G.degree (X k) else 0)
      = fun ξ : V → ℝ => ({ξ : V → ℝ | k < trapRule G r C K N ε ξ X}).indicator
        (fun _ => (1 : ℝ)) ξ * (ξ (X k) / G.degree (X k)) := by
    funext ξ
    by_cases h : k < trapRule G r C K N ε ξ X
    · simp [h, Set.indicator_of_mem]
    · simp [h, Set.indicator_of_notMem]
  rw [heq]
  exact hind.mul hcoord

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The rule is measurable in the scenery.**  For a fixed trajectory, the
rule is a measurable function of the scenery: its fibres are differences of
level sets. -/
theorem measurable_trapRule (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ)
    (ε : ℝ) (X : ℕ → V) :
    Measurable fun ξ : V → ℝ => trapRule G r C K N ε ξ X := by
  refine measurable_to_countable' fun n => ?_
  match n with
  | 0 =>
      show MeasurableSet {ξ : V → ℝ | trapRule G r C K N ε ξ X = 0}
      have : {ξ : V → ℝ | trapRule G r C K N ε ξ X = 0}
          = {ξ : V → ℝ | trapRule G r C K N ε ξ X ≤ 0} := by
        ext ξ
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h; exact Nat.le_zero.mpr h
        · intro h; exact Nat.le_antisymm h (Nat.zero_le _)
      rw [this]
      exact measurableSet_trapRule_le r C K N ε X 0
  | n + 1 =>
      show MeasurableSet {ξ : V → ℝ | trapRule G r C K N ε ξ X = n + 1}
      have : {ξ : V → ℝ | trapRule G r C K N ε ξ X = n + 1}
          = {ξ : V → ℝ | trapRule G r C K N ε ξ X ≤ n + 1}
              ∩ {ξ : V → ℝ | trapRule G r C K N ε ξ X ≤ n}ᶜ := by
        ext ξ
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
        omega
      rw [this]
      exact (measurableSet_trapRule_le r C K N ε X (n + 1)).inter
        (measurableSet_trapRule_le r C K N ε X n).compl

omit [MeasurableSingletonClass V] in
/-- **The position at the rule is measurable in the scenery.** -/
theorem measurable_rulePosition (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ)
    (ε : ℝ) (X : ℕ → V) :
    Measurable fun ξ : V → ℝ => X (trapRule G r C K N ε ξ X) := by
  refine measurable_to_countable' fun v => ?_
  show MeasurableSet {ξ : V → ℝ | X (trapRule G r C K N ε ξ X) = v}
  have hfiber : ∀ n : ℕ, MeasurableSet {ξ : V → ℝ | trapRule G r C K N ε ξ X = n} :=
    fun n => measurable_trapRule r C K N ε X (measurableSet_singleton n)
  have hset : {ξ : V → ℝ | X (trapRule G r C K N ε ξ X) = v}
      = ⋃ (n : ℕ), {ξ : V → ℝ | X n = v} ∩ {ξ : V → ℝ | trapRule G r C K N ε ξ X = n} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨trapRule G r C K N ε ξ X, h, rfl⟩
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


/-- **The trap potential at the rule is measurable in the scenery.** -/
theorem measurable_trapPotential_rule (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ)
    (ε : ℝ) (X : ℕ → V) :
    Measurable fun ξ : V → ℝ =>
      trapPotential G K ξ (X (trapRule G r C K N ε ξ X)) := by
  have hpos : Measurable fun ξ : V → ℝ => X (trapRule G r C K N ε ξ X) := by
    refine measurable_to_countable' fun v => ?_
    show MeasurableSet {ξ : V → ℝ | X (trapRule G r C K N ε ξ X) = v}
    have hfiber : ∀ n : ℕ, MeasurableSet {ξ : V → ℝ | trapRule G r C K N ε ξ X = n} :=
      fun n => measurable_trapRule r C K N ε X (measurableSet_singleton n)
    have hset : {ξ : V → ℝ | X (trapRule G r C K N ε ξ X) = v}
        = ⋃ (n : ℕ), {ξ : V → ℝ | X n = v} ∩ {ξ : V → ℝ | trapRule G r C K N ε ξ X = n} := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro h; exact ⟨trapRule G r C K N ε ξ X, h, rfl⟩
      · rintro ⟨n, hn, hτ⟩; exact hτ ▸ hn
    rw [hset]
    refine MeasurableSet.iUnion fun n => ?_
    by_cases hXv : X n = v
    · have hu : {ξ : V → ℝ | X n = v} = Set.univ := by ext; simp [hXv]
      rw [hu]; exact MeasurableSet.univ.inter (hfiber n)
    · have he : {ξ : V → ℝ | X n = v} = ∅ := by ext; simp [hXv]
      rw [he]; exact MeasurableSet.empty.inter (hfiber n)
  have hjoint : Measurable fun p : (V → ℝ) × V =>
      ∑ v ∈ K, p.1 v * RWRS.killedGreenReal G (K : Set V) v p.2 :=
    Finset.measurable_sum _ fun v _ =>
      ((measurable_pi_apply v).comp measurable_fst).mul ((measurable_of_countable (f := fun y : V => RWRS.killedGreenReal G (K : Set V) v y)).comp measurable_snd)
  have hpair : Measurable fun ξ : V → ℝ => (ξ, X (trapRule G r C K N ε ξ X)) :=
    Measurable.prod measurable_id hpos
  exact hjoint.comp hpair


end RWRS.Support