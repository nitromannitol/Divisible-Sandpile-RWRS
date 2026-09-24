/-
The stage events of Step 1 of `prop:doubly-transient-really-general`, and the
bound on the potential the walk collects at the stage where the rule fires.

Conditionally on the walk the trap sets `C 0, C 1, …` are fixed pairwise disjoint
finite sets, so the events "the scenery is at most `-ε` on `C j`" read disjoint
blocks of coordinates and are independent.  The event that stage `i` is the FIRST
whose trap is good is the intersection of the `i`-th block event with the
complements of the earlier ones, and everything here is the algebra of that
intersection: it is read by the sites of the stages up to `i`, and for each
earlier `j` it re-associates as the complement of the `j`-th block event
intersected with an event of the OTHER blocks.

The potential at the site the rule stops at then splits into three pieces: the
current block, where the scenery is at most `-ε` and the bound is pathwise; the
earlier blocks, where the bias of a coordinate is at most `E|ξ|` and the total
weight is at most one by admissibility; and the rest, which the event does not
read and which is centred, so contributes nothing.
-/
import RWRS.Support.DTBlocks

namespace RWRS.Support

open MeasureTheory

variable {V : Type*} {ν : Measure ℝ}

/-! ### The stage events -/

open scoped Classical in
/-- The sites of the stages up to `i`. -/
noncomputable def stageSites (C : ℕ → Finset V) (i : ℕ) : Finset V :=
  (Finset.range (i + 1)).biUnion C

open scoped Classical in
/-- The sites of the stages strictly before `i`. -/
noncomputable def stageSitesBelow (C : ℕ → Finset V) (i : ℕ) : Finset V :=
  (Finset.range i).biUnion C

open scoped Classical in
/-- The sites of the stages up to `i` other than the `j`-th. -/
noncomputable def stageSitesExcept (C : ℕ → Finset V) (i j : ℕ) : Finset V :=
  ((Finset.range (i + 1)).erase j).biUnion C

/-- **The event that the trap of stage `i` is the first good one.** -/
def hitEvent (C : ℕ → Finset V) (ε : ℝ) (i : ℕ) : Set (V → ℝ) :=
  trapEvent (C i) ε ∩ {ξ : V → ℝ | ∀ j < i, ξ ∉ trapEvent (C j) ε}

/-- The part of `hitEvent` that the blocks other than the `j`-th decide. -/
def restEvent (C : ℕ → Finset V) (ε : ℝ) (i j : ℕ) : Set (V → ℝ) :=
  trapEvent (C i) ε ∩ {ξ : V → ℝ | ∀ l < i, l ≠ j → ξ ∉ trapEvent (C l) ε}

theorem hitEvent_subset_trapEvent (C : ℕ → Finset V) (ε : ℝ) (i : ℕ) :
    hitEvent C ε i ⊆ trapEvent (C i) ε := Set.inter_subset_left

theorem measurableSet_hitEvent (C : ℕ → Finset V) (ε : ℝ) (i : ℕ) :
    MeasurableSet (hitEvent (V := V) C ε i) := by
  rw [hitEvent]
  refine (measurableSet_trapEvent _ _).inter ?_
  have h : {ξ : V → ℝ | ∀ j < i, ξ ∉ trapEvent (C j) ε}
      = ⋂ j ∈ Finset.range i, (trapEvent (C j) ε)ᶜ := by
    ext ξ
    simp [Set.mem_iInter, Finset.mem_range]
  rw [h]
  exact MeasurableSet.biInter (Set.to_countable _) fun j _ => (measurableSet_trapEvent _ _).compl

theorem measurableSet_restEvent (C : ℕ → Finset V) (ε : ℝ) (i j : ℕ) :
    MeasurableSet (restEvent (V := V) C ε i j) := by
  classical
  rw [restEvent]
  refine (measurableSet_trapEvent _ _).inter ?_
  have h : {ξ : V → ℝ | ∀ l < i, l ≠ j → ξ ∉ trapEvent (C l) ε}
      = ⋂ l ∈ Finset.range i, (if l = j then Set.univ else (trapEvent (C l) ε)ᶜ) := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
    constructor
    · intro h l hl
      by_cases hlj : l = j
      · simp [hlj]
      · simp only [hlj, if_false]
        exact h l hl hlj
    · intro h l hl hlj
      have h2 := h l hl
      simp only [hlj, if_false] at h2
      exact h2
  rw [h]
  refine MeasurableSet.biInter (Set.to_countable _) fun l _ => ?_
  by_cases hlj : l = j
  · simp [hlj]
  · simp only [hlj, if_false]
    exact (measurableSet_trapEvent _ _).compl

/-- **The re-association**: for an earlier stage `j`, the hit event at `i` is the
complement of the `j`-th block event intersected with an event of the others. -/
theorem hitEvent_eq_compl_inter_rest (C : ℕ → Finset V) (ε : ℝ) {i j : ℕ} (hji : j < i) :
    hitEvent (V := V) C ε i = (trapEvent (C j) ε)ᶜ ∩ restEvent C ε i j := by
  ext ξ
  simp only [hitEvent, restEvent, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2 j hji, h1, fun l hl _ => h2 l hl⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨h1, fun l hl => ?_⟩
    by_cases hlj : l = j
    · rw [hlj]; exact h0
    · exact h2 l hl hlj

/-! ### What each event reads -/

theorem hitEvent_dependsOn (C : ℕ → Finset V) (ε : ℝ) (i : ℕ) (ξ η : V → ℝ)
    (h : ∀ w ∈ ((stageSites C i : Finset V) : Set V), ξ w = η w) :
    ξ ∈ hitEvent C ε i ↔ η ∈ hitEvent C ε i := by
  have hsub : ∀ j ≤ i, ∀ w ∈ ((C j : Finset V) : Set V), ξ w = η w := by
    intro j hj w hw
    refine h w ?_
    have hw' : w ∈ C j := Finset.mem_coe.1 hw
    have hw'' : w ∈ stageSites C i := by
      rw [stageSites]
      simp only [Finset.mem_biUnion, Finset.mem_range]
      exact ⟨j, by omega, hw'⟩
    exact Finset.mem_coe.2 hw''
  simp only [hitEvent, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(trapEvent_dependsOn (C i) ε ξ η (hsub i le_rfl)).1 h1, fun j hj hc => ?_⟩
    exact h2 j hj ((trapEvent_dependsOn (C j) ε ξ η (hsub j (by omega))).2 hc)
  · rintro ⟨h1, h2⟩
    refine ⟨(trapEvent_dependsOn (C i) ε ξ η (hsub i le_rfl)).2 h1, fun j hj hc => ?_⟩
    exact h2 j hj ((trapEvent_dependsOn (C j) ε ξ η (hsub j (by omega))).1 hc)

theorem restEvent_dependsOn (C : ℕ → Finset V) (ε : ℝ) {i j : ℕ} (hji : j < i) (ξ η : V → ℝ)
    (h : ∀ w ∈ ((stageSitesExcept C i j : Finset V) : Set V), ξ w = η w) :
    ξ ∈ restEvent C ε i j ↔ η ∈ restEvent C ε i j := by
  classical
  have hsub : ∀ l, l ≤ i → l ≠ j → ∀ w ∈ ((C l : Finset V) : Set V), ξ w = η w := by
    intro l hl hlj w hw
    refine h w ?_
    have hw' : w ∈ C l := Finset.mem_coe.mpr hw
    have hmem : w ∈ stageSitesExcept C i j := by
      rw [stageSitesExcept]
      simp only [Finset.mem_biUnion]
      exact ⟨l, Finset.mem_erase.2 ⟨hlj, Finset.mem_range.2 (by omega)⟩, hw'⟩
    exact hmem
  have hij : i ≠ j := by omega
  simp only [restEvent, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(trapEvent_dependsOn (C i) ε ξ η (hsub i le_rfl hij)).1 h1, fun l hl hlj hc => ?_⟩
    exact h2 l hl hlj ((trapEvent_dependsOn (C l) ε ξ η (hsub l (by omega) hlj)).2 hc)
  · rintro ⟨h1, h2⟩
    refine ⟨(trapEvent_dependsOn (C i) ε ξ η (hsub i le_rfl hij)).2 h1, fun l hl hlj hc => ?_⟩
    exact h2 l hl hlj ((trapEvent_dependsOn (C l) ε ξ η (hsub l (by omega) hlj)).1 hc)

theorem compl_trapEvent_dependsOn (D : Finset V) (ε : ℝ) (ξ η : V → ℝ)
    (h : ∀ w ∈ ((D : Finset V) : Set V), ξ w = η w) :
    ξ ∈ (trapEvent D ε)ᶜ ↔ η ∈ (trapEvent D ε)ᶜ := by
  simpa using not_congr (trapEvent_dependsOn D ε ξ η h)

/-- The `j`-th block is disjoint from the sites of the other stages. -/
theorem disjoint_block_stageSitesExcept (C : ℕ → Finset V) {i j : ℕ} (hj : j ≤ i)
    (hdisj : ∀ a ≤ i, ∀ b ≤ i, a ≠ b → Disjoint (C a) (C b)) :
    Disjoint ((C j : Finset V) : Set V) ((stageSitesExcept C i j : Finset V) : Set V) := by
  classical
  rw [stageSitesExcept, Finset.disjoint_coe, Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_biUnion] at hb
  obtain ⟨l, hl, hal⟩ := hb
  obtain ⟨hlj, hlr⟩ := Finset.mem_erase.1 hl
  have hli : l ≤ i := by
    have h2 := Finset.mem_range.1 hlr
    omega
  exact Finset.disjoint_left.1 (hdisj j hj l hli (Ne.symm hlj)) ha hal

theorem stageSites_subset (C : ℕ → Finset V) {K : Finset V} {i : ℕ}
    (hCK : ∀ j ≤ i, C j ⊆ K) : stageSites C i ⊆ K := by
  classical
  intro v hv
  simp only [stageSites, Finset.mem_biUnion, Finset.mem_range] at hv
  obtain ⟨j, hj, hvj⟩ := hv
  exact hCK j (by omega) hvj

/-! ### The measure of the stage events -/

/-- **The hit event factorizes** across an earlier block and the others. -/
theorem measure_hitEvent_factor (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : ℕ → Finset V) (ε : ℝ) {i j : ℕ} (hji : j < i)
    (hdisj : ∀ a ≤ i, ∀ b ≤ i, a ≠ b → Disjoint (C a) (C b)) :
    RWRS.iidLaw V ν (hitEvent C ε i)
      = RWRS.iidLaw V ν ((trapEvent (C j) ε)ᶜ) * RWRS.iidLaw V ν (restEvent C ε i j) := by
  rw [hitEvent_eq_compl_inter_rest C ε hji]
  exact measure_inter_of_disjoint ν
    (disjoint_block_stageSitesExcept C (le_of_lt hji) hdisj)
    (measurableSet_trapEvent (C j) ε).compl
    (measurableSet_restEvent C ε i j)
    (compl_trapEvent_dependsOn (C j) ε)
    (restEvent_dependsOn C ε hji)

/-- **The event read by the other blocks is at most the hit event divided by the
probability that the `j`-th trap fails.** -/
theorem measure_restEvent_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (C : ℕ → Finset V) (ε : ℝ) {i j : ℕ} (hji : j < i)
    (hdisj : ∀ a ≤ i, ∀ b ≤ i, a ≠ b → Disjoint (C a) (C b)) {q : ℝ} (hq : 0 < q)
    (hcompl : ENNReal.ofReal q ≤ RWRS.iidLaw V ν ((trapEvent (C j) ε)ᶜ)) :
    (RWRS.iidLaw V ν (restEvent C ε i j)).toReal
      ≤ (RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  set A : ℝ := (RWRS.iidLaw V ν ((trapEvent (C j) ε)ᶜ)).toReal with hA
  set R : ℝ := (RWRS.iidLaw V ν (restEvent C ε i j)).toReal with hR
  have hfac : (RWRS.iidLaw V ν (hitEvent C ε i)).toReal = A * R := by
    rw [measure_hitEvent_factor ν C ε hji hdisj, ENNReal.toReal_mul]
  have hAq : q ≤ A := by
    have h2 : (ENNReal.ofReal q).toReal ≤ A :=
      ENNReal.toReal_mono (measure_ne_top _ _) hcompl
    rwa [ENNReal.toReal_ofReal hq.le] at h2
  have hRnn : 0 ≤ R := ENNReal.toReal_nonneg
  rw [hfac, le_div_iff₀ hq]
  nlinarith [hRnn, hAq, hq]

end RWRS.Support
