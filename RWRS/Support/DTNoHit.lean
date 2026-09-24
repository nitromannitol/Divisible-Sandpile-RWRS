/-
The failure probability of Step 1 of `prop:doubly-transient-really-general`
(`rwrs.tex:926`): conditionally on the walk, the trap events of the selected
centres read disjoint blocks of scenery coordinates, so they are independent,
and the probability that none of the first `ℓ` fires is at most
`(1 - p₀ ^ M) ^ ℓ`, where `p₀ = ν(ξ ≤ -ε)` and `M` bounds the block size.
-/
import RWRS.Support.DTStageEvents

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

omit [DecidableEq V] in
/-- **The no-hit event splits at the last index.** -/
theorem noHitEvent_succ (C : ℕ → Finset V) (ε : ℝ) (ℓ : ℕ) :
    {ξ : V → ℝ | ∀ i < ℓ + 1, ξ ∉ trapEvent (C i) ε}
      = {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε}
        ∩ (trapEvent (C ℓ) ε)ᶜ := by
  ext ξ
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), fun htrap => h ℓ (by omega) htrap⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact h1 i hlt
    · subst heq
      exact fun htrap => h2 htrap

/-- **The no-hit event reads only the coordinates of the first `ℓ` blocks.** -/
theorem noHitEvent_dependsOn (C : ℕ → Finset V) (ε : ℝ) (ℓ : ℕ) (ξ η : V → ℝ)
    (h : ∀ w ∈ ((Finset.range ℓ).biUnion C : Finset V), ξ w = η w) :
    ξ ∈ {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε}
      ↔ η ∈ {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε} := by
  constructor
  · intro hmem i hi htrap
    exact hmem i hi
      ((trapEvent_dependsOn (C i) ε η ξ (fun w hw => (h w
        (Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, hw⟩)).symm)).mp htrap)
  · intro hmem i hi htrap
    exact hmem i hi
      ((trapEvent_dependsOn (C i) ε ξ η (fun w hw => h w
        (Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 hi, hw⟩))).mp htrap)

omit [DecidableEq V] in
/-- **The no-hit event is measurable.** -/
theorem measurableSet_noHit (C : ℕ → Finset V) (ε : ℝ) (ℓ : ℕ) :
    MeasurableSet {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε} := by
  have : {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε}
      = ⋂ i ∈ Finset.range ℓ, (trapEvent (C i) ε)ᶜ := by
    ext ξ
    simp
  rw [this]
  exact MeasurableSet.biInter (Finset.countable_toSet _)
    (fun i _ => MeasurableSet.compl (measurableSet_trapEvent _ _))

/-- **The failure probability of Step 1** (`rwrs.tex:926`): conditionally on the
walk, the probability that none of the first `ℓ` trap events fires is at most
`(1 - p ^ M) ^ ℓ`, where `p = ν(ξ ≤ -ε)`.  The events read disjoint blocks, so
they are independent, and each fails with probability at most `1 - p ^ M`. -/
theorem measure_noHit_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : ℕ → Finset V) (ε : ℝ) (ℓ : ℕ) (M : ℕ)
    (hcard : ∀ i < ℓ, (C i).card ≤ M)
    (hdisj : ∀ i < ℓ, ∀ j < ℓ, i ≠ j → Disjoint ((C i : Set V)) ((C j : Set V))) :
    (RWRS.iidLaw V ν) {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε}
      ≤ (1 - ν (Set.Iic (-ε)) ^ M) ^ ℓ := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
      have hsplit : {ξ : V → ℝ | ∀ i < ℓ + 1, ξ ∉ trapEvent (C i) ε}
          = {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε} ∩ (trapEvent (C ℓ) ε)ᶜ :=
        noHitEvent_succ C ε ℓ
      rw [hsplit]
      have hdisj' : Disjoint (((Finset.range ℓ).biUnion C : Set V)) ((C ℓ : Set V)) := by
        rw [Set.disjoint_left]
        intro w hw1 hw2
        obtain ⟨i, hi, hwC⟩ := Finset.mem_biUnion.1 hw1
        have hne : i ≠ ℓ := fun he => by
          subst he
          have := hi
          simp at this
        have hiℓ : i < ℓ := Finset.mem_range.1 hi
        exact absurd (Set.disjoint_left.1 (hdisj i (by omega) ℓ (by omega) hne)
          (by exact_mod_cast hwC) (by exact_mod_cast hw2)) (by simp)
      have hfac := measure_inter_of_disjoint ν hdisj'
        (A := {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε})
        (B := (trapEvent (C ℓ) ε)ᶜ)
        (measurableSet_noHit C ε ℓ) (MeasurableSet.compl (measurableSet_trapEvent _ _))
        (fun ξ η h => noHitEvent_dependsOn C ε ℓ ξ η
          (fun w hw => h w (by
            exact_mod_cast hw)))
        (fun ξ η h => Iff.not (trapEvent_dependsOn (C ℓ) ε ξ η
          (fun w hw => h w (by
            exact_mod_cast hw))))
      rw [hfac]
      have hbase : ν (Set.Iic (-ε)) ≤ 1 := prob_le_one
      have hp1 : ν (Set.Iic (-ε)) ^ M ≤ 1 := by
        have h := pow_le_pow_right_of_le_one' hbase (Nat.zero_le M)
        simpa using h
      have hcompl : (RWRS.iidLaw V ν) (trapEvent (C ℓ) ε)ᶜ ≤ 1 - ν (Set.Iic (-ε)) ^ M := by
        have h1 : (RWRS.iidLaw V ν) (trapEvent (C ℓ) ε)ᶜ
            = 1 - (RWRS.iidLaw V ν) (trapEvent (C ℓ) ε) := by
          have hfin : (RWRS.iidLaw V ν) (trapEvent (C ℓ) ε) ≠ ∞ := by
            rw [measure_trapEvent]
            have h := pow_le_pow_right_of_le_one' hbase (Nat.zero_le (C ℓ).card)
            simp
          rw [measure_compl (measurableSet_trapEvent _ _) hfin]
          simp
        rw [h1, measure_trapEvent ν (C ℓ) ε]
        have hge : ν (Set.Iic (-ε)) ^ M ≤ ν (Set.Iic (-ε)) ^ (C ℓ).card :=
          pow_le_pow_right_of_le_one' hbase (hcard ℓ (by omega))
        exact tsub_le_tsub_left hge 1
      calc (RWRS.iidLaw V ν) {ξ : V → ℝ | ∀ i < ℓ, ξ ∉ trapEvent (C i) ε}
          * (RWRS.iidLaw V ν) (trapEvent (C ℓ) ε)ᶜ
          ≤ (1 - ν (Set.Iic (-ε)) ^ M) ^ ℓ * (1 - ν (Set.Iic (-ε)) ^ M) :=
            mul_le_mul' (ih (fun i hi => hcard i (by omega))
              (fun i hi j hj hij => hdisj i (by omega) j (by omega) hij)) hcompl
        _ = (1 - ν (Set.Iic (-ε)) ^ M) ^ (ℓ + 1) := by rw [pow_succ]

omit [DecidableEq V] in
/-- **The stage hit events and the no-hit event partition the scenery space.**
For fixed blocks, every scenery either lies in no trap event among the first
`ℓ + 1`, or in exactly one stage hit event (the first trap event that fires). -/
theorem indicator_sum_hitEvent_add_noHit (C : ℕ → Finset V) (ε : ℝ) (ℓ : ℕ)
    (ξ : V → ℝ) :
    (∑ i ∈ Finset.range (ℓ + 1),
        (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ)
      + {ξ' : V → ℝ | ∀ i < ℓ + 1, ξ' ∉ trapEvent (C i) ε}.indicator
          (fun _ => (1 : ℝ)) ξ = 1 := by
  classical
  by_cases hex : ∃ i, i < ℓ + 1 ∧ ξ ∈ trapEvent (C i) ε
  · obtain ⟨i₁, h₁⟩ := hex
    set F : Finset ℕ := (Finset.range (ℓ + 1)).filter (fun i => ξ ∈ trapEvent (C i) ε) with hF
    have hFne : F.Nonempty := ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_range.2 h₁.1, h₁.2⟩⟩
    set i₀ := F.min' hFne with hi₀
    have hi₀mem : i₀ ∈ F := Finset.min'_mem F hFne
    obtain ⟨hi₀lt, hi₀trap⟩ := Finset.mem_filter.1 hi₀mem
    have hi₀lt' : i₀ < ℓ + 1 := Finset.mem_range.1 hi₀lt
    have hmin : ∀ j < i₀, ξ ∉ trapEvent (C j) ε := by
      intro j hj htrap
      have : F.min' hFne ≤ j := Finset.min'_le F j
        (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), htrap⟩)
      omega
    have hhit : ∀ i ∈ Finset.range (ℓ + 1),
        (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
          = if i = i₀ then (1 : ℝ) else 0 := by
      intro i hi
      rcases eq_or_ne i i₀ with rfl | hne
      · rw [if_pos rfl]
        exact Set.indicator_of_mem
          (Set.mem_inter hi₀trap
            (Set.mem_setOf.2 fun j hj => hmin j hj)) _
      · rw [if_neg hne]
        by_cases hlt : i < i₀
        · exact Set.indicator_of_notMem (fun h => hmin i hlt h.1) _
        · exact Set.indicator_of_notMem (fun h => h.2 i₀ (by omega) hi₀trap) _
    rw [Finset.sum_congr rfl (fun i hi => hhit i hi)]
    rw [Finset.sum_ite_eq' (Finset.range (ℓ + 1)) i₀ (fun _ => (1 : ℝ))]
    have hnohit : ξ ∉ {ξ' : V → ℝ | ∀ i < ℓ + 1, ξ' ∉ trapEvent (C i) ε} :=
      fun h => h i₀ (Finset.mem_range.1 hi₀lt) hi₀trap
    rw [Set.indicator_of_notMem hnohit, if_pos hi₀lt]
    ring
  · push Not at hex
    have hzero : ∀ i ∈ Finset.range (ℓ + 1),
        (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ = 0 :=
      fun i hi => Set.indicator_of_notMem (fun h => hex i (Finset.mem_range.1 hi) h.1) _
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    rw [Set.indicator_of_mem (Set.mem_setOf.2 fun i _ => hex i (by omega)) _]
    ring


end RWRS.Support
