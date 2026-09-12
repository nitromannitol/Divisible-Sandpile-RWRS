import RWRS.Support.DTStageEvents
import RWRS.Support.DTTrapFamily

/-!
# The stage-union bound of Step 1

The intersection of the complements of the first `ℓ` trap events factors
over pairwise-disjoint blocks, and the union of the trap events therefore
covers all but `(1 - p₀^M)^ℓ` of the scenery measure.
-/

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal BigOperators Classical

variable {V : Type*} [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The complements of finitely many block-disjoint trap events factor.** -/
theorem measure_inter_compl_trapEvent_prod (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : ℕ → Finset V) (ε : ℝ) (ℓ : ℕ)
    (hdisj : ∀ a < ℓ, ∀ b < ℓ, a ≠ b → Disjoint (C a) (C b)) :
    (RWRS.iidLaw V ν) (⋂ i, {ξ : V → ℝ | i ∈ Finset.range ℓ → ξ ∈ (trapEvent (C i) ε)ᶜ})
      = ∏ i ∈ Finset.range ℓ, (RWRS.iidLaw V ν) ((trapEvent (C i) ε)ᶜ) := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have hsplit :
        (⋂ i, {ξ : V → ℝ | i ∈ Finset.range (ℓ+1) → ξ ∈ (trapEvent (C i) ε)ᶜ})
        = (⋂ i, {ξ : V → ℝ | i ∈ Finset.range ℓ → ξ ∈ (trapEvent (C i) ε)ᶜ})
          ∩ (trapEvent (C ℓ) ε)ᶜ := by
      ext ξ
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq,
        Finset.mem_range_succ_iff]
      constructor
      · intro h
        refine ⟨fun i hi => h i (by have := Finset.mem_range.1 hi; omega), h ℓ le_rfl⟩
      · rintro ⟨h, hℓ⟩ i hi
        by_cases hie : i = ℓ
        · exact hie ▸ hℓ
        · exact h i (Finset.mem_range.2 (by omega))
    have hB : MeasurableSet ((trapEvent (C ℓ) ε)ᶜ) :=
      (measurableSet_trapEvent (C ℓ) ε).compl
    have hA : MeasurableSet
        (⋂ i, {ξ : V → ℝ | i ∈ Finset.range ℓ → ξ ∈ (trapEvent (C i) ε)ᶜ}) := by
      refine MeasurableSet.iInter fun i => ?_
      by_cases hi : i ∈ Finset.range ℓ
      · have : {ξ : V → ℝ | i ∈ Finset.range ℓ → ξ ∈ (trapEvent (C i) ε)ᶜ}
            = (trapEvent (C i) ε)ᶜ := by ext ξ; simp [hi]
        rw [this]
        exact (measurableSet_trapEvent (C i) ε).compl
      · have : {ξ : V → ℝ | i ∈ Finset.range ℓ → ξ ∈ (trapEvent (C i) ε)ᶜ}
            = Set.univ := by ext ξ; simp [hi]
        rw [this]
        exact MeasurableSet.univ
    have hd : Disjoint (⋃ i ∈ Finset.range ℓ, ↑(C i)) (↑(C ℓ) : Set V) := by
      refine Set.disjoint_left.mpr ?_
      rintro x hx hxℓ
      simp only [Set.mem_iUnion] at hx
      obtain ⟨a, ha⟩ := hx
      obtain ⟨ha, hxa⟩ := ha
      have hda := hdisj a (by have := Finset.mem_range.1 ha; omega) ℓ (Nat.lt_succ_self ℓ) (by have := Finset.mem_range.1 ha; omega)
      exact absurd (hda.le_bot (Finset.mem_inter.2 ⟨hxa, hxℓ⟩)) (by simp)
    have hAS : ∀ ξ η : V → ℝ, (∀ w ∈ ⋃ i ∈ Finset.range ℓ, ↑(C i), ξ w = η w) →
        (ξ ∈ ⋂ i, {ξ : V → ℝ | i ∈ Finset.range ℓ → ξ ∈ (trapEvent (C i) ε)ᶜ} ↔
         η ∈ ⋂ i, {η : V → ℝ | i ∈ Finset.range ℓ → η ∈ (trapEvent (C i) ε)ᶜ}) := by
      intro ξ η hxy
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h i hi
        exact (compl_trapEvent_dependsOn (C i) ε ξ η
          (fun w hw => hxy w (Set.mem_iUnion₂.2 ⟨i, hi, hw⟩))).mp (h i hi)
      · intro h i hi
        exact (compl_trapEvent_dependsOn (C i) ε η ξ
          (fun w hw => (hxy w (Set.mem_iUnion₂.2 ⟨i, hi, hw⟩)).symm)).mp (h i hi)
    have hBT : ∀ ξ η : V → ℝ, (∀ w ∈ (↑(C ℓ) : Set V), ξ w = η w) →
        (ξ ∈ (trapEvent (C ℓ) ε)ᶜ ↔ η ∈ (trapEvent (C ℓ) ε)ᶜ) :=
      compl_trapEvent_dependsOn (C ℓ) ε
    rw [hsplit, measure_inter_of_disjoint ν hd hA hB hAS hBT,
      ih (fun a ha b hb hab => hdisj a (by omega) b (by omega) hab),
      Finset.prod_range_succ]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The union of `ℓ` disjoint trap events covers all but `(1 - p₀^M)^ℓ`.** -/
theorem measure_union_trapEvent_ge (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : ℕ → Finset V) (ε : ℝ) (ℓ : ℕ) (M : ℕ)
    (hdisj : ∀ a < ℓ, ∀ b < ℓ, a ≠ b → Disjoint (C a) (C b))
    (hcard : ∀ i < ℓ, (C i).card ≤ M) :
    1 - (1 - (ν (Set.Iic (-ε))) ^ M) ^ ℓ
      ≤ RWRS.iidLaw V ν (⋃ i ∈ Finset.range ℓ, trapEvent (C i) ε) := by
  have hcompl : (⋃ i ∈ Finset.range ℓ, trapEvent (C i) ε)ᶜ
      = ⋂ i, {ξ : V → ℝ | i ∈ Finset.range ℓ → ξ ∈ (trapEvent (C i) ε)ᶜ} := by
    rw [Set.compl_iUnion]
    ext ξ
    simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_iUnion]

    exact ⟨fun h i hi hxi => h i ⟨hi, hxi⟩, fun h i ⟨hi, hxi⟩ => h i hi hxi⟩
  have hprod := measure_inter_compl_trapEvent_prod ν C ε ℓ hdisj
  have hfac : ∀ i ∈ Finset.range ℓ,
      (1 : ℝ≥0∞) - RWRS.iidLaw V ν (trapEvent (C i) ε)
        ≤ 1 - (ν (Set.Iic (-ε))) ^ M :=
    fun i hi => tsub_le_tsub_left (measure_trapEvent_ge ν (hcard i (Finset.mem_range.mp hi)) ε) 1
  have hprodle : Finset.prod (Finset.range ℓ)
      (fun i => (1 : ℝ≥0∞) - RWRS.iidLaw V ν (trapEvent (C i) ε))
      ≤ (1 - (ν (Set.Iic (-ε))) ^ M) ^ ℓ := by
    have h0 : ∀ i ∈ Finset.range ℓ,
        (0:ℝ≥0∞) ≤ (1:ℝ≥0∞) - RWRS.iidLaw V ν (trapEvent (C i) ε) := fun i _ => by norm_num
    have h1 := Finset.prod_le_prod h0 hfac
    rw [Finset.prod_const, Finset.card_range] at h1
    exact h1
  have hunion : RWRS.iidLaw V ν (⋃ i ∈ Finset.range ℓ, trapEvent (C i) ε)
      = 1 - RWRS.iidLaw V ν ((⋃ i ∈ Finset.range ℓ, trapEvent (C i) ε)ᶜ) := by
    have hm : MeasurableSet (⋃ i ∈ Finset.range ℓ, trapEvent (C i) ε) :=
      MeasurableSet.biUnion (Set.to_countable _) fun i _ => measurableSet_trapEvent _ _
    have hne : RWRS.iidLaw V ν (⋃ i ∈ Finset.range ℓ, trapEvent (C i) ε) ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt prob_le_one (by norm_num))
    rw [measure_compl hm hne, measure_univ]
    exact (ENNReal.sub_sub_cancel (by norm_num) prob_le_one).symm
  have hcomplprod : RWRS.iidLaw V ν ((⋃ i ∈ Finset.range ℓ, trapEvent (C i) ε)ᶜ)
      = Finset.prod (Finset.range ℓ)
      (fun i => (1 : ℝ≥0∞) - RWRS.iidLaw V ν (trapEvent (C i) ε)) := by
    rw [hcompl, hprod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [measure_compl (measurableSet_trapEvent _ _) (by measurability), measure_univ]
  rw [hunion, hcomplprod]
  exact tsub_le_tsub_left hprodle 1

end RWRS.Support
