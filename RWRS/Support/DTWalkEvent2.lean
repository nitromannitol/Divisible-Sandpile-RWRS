import RWRS.Support.DTWalkGood

/-!
# The exit-based walk event of Step 1

The cover lemma: a trajectory with `T_ℓ < ∞` visits finitely many sites
up to `T_ℓ` and uses finitely many trap blocks, so some member of an
exhaustion captures both, keeping the walk inside up to `T_ℓ`.  The
full-measure lemma: the event `T_ℓ < ∞` has measure one.  The
selection lemma: some finite set keeps the walk inside up to `T_ℓ` with
probability at least `15/16`.
-/

namespace RWRS.Support

open MeasureTheory LatticeProb Filter
open scoped Classical ENNReal

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **Cover of the finiteness event by exit-based walk events.** -/
theorem walkEvent2_iUnion_cover
    (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (K : ℕ → Finset V) (hexh : ∀ S : Finset V, ∃ n, S ⊆ K n) (ℓ : ℕ) :
    {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤}
      ⊆ ⋃ n, {X' : ℕ → V | (uncTime G r C X' ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (K n : Set V) X'
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X' i ⊆ K n} := by
  intro X hX
  simp only [Set.mem_setOf_eq] at hX
  obtain ⟨t, ht⟩ : ∃ t : ℕ, (uncTime G r C X ℓ : ℕ∞) = t := by
    lift (uncTime G r C X ℓ : ℕ∞) to ℕ using ne_of_lt hX with t
    exact ⟨t, rfl⟩
  classical
  set S : Finset V := (Finset.range (t + 1)).image X ∪
    (Finset.range (ℓ + 1)).biUnion (fun i => uncUsed G r C X i) with hS
  obtain ⟨n, hn⟩ := hexh S
  refine Set.mem_iUnion.2 ⟨n, ?_, ?_⟩
  · rw [ht]
    have hstay : LatticeProb.Graph.stayIn (K n : Set V) t X := by
      intro j hj
      have hmem : X j ∈ S := Finset.mem_union_left _ (Finset.mem_image.2
        ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hj), rfl⟩)
      exact hn hmem
    have hEq := LatticeProb.Graph.stayIn_eq_lt_exitTime (K n : Set V) t
    exact hEq.subset hstay
  · intro i hi
    have hsub : uncUsed G r C X i ⊆ S := by
      intro x hx
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), hx⟩)
    exact Finset.Subset.trans hsub hn

/-- **The event `T_ℓ < ∞` has full measure.** -/
theorem measure_uncTime_lt_top (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (hdt : RWRS.DoublyTransient G)
    (r : ℕ) (C : V → Finset V) (hC : ∀ y : V, y ∈ C y) (o : V) (ℓ : ℕ) :
    (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤} = 1 := by
  have hstop := uncTime_isStopping G r C ℓ
  have hmeasN : ∀ N : ℕ, MeasurableSet {X : ℕ → V | uncTime G r C X ℓ < (N : ℕ∞)} := by
    intro N
    have hset : {X : ℕ → V | uncTime G r C X ℓ < (N : ℕ∞)}
        = ⋃ n ∈ Finset.range N, {X : ℕ → V | uncTime G r C X ℓ = (n : ℕ∞)} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro h
        lift (uncTime G r C X ℓ : ℕ∞) to ℕ using ne_of_lt (lt_of_lt_of_le h le_top) with t
        exact ⟨t, by exact_mod_cast h, rfl⟩
      · rintro ⟨n, hn, heq⟩
        rw [heq]
        exact_mod_cast hn
    rw [hset]
    exact MeasurableSet.biUnion
      ((Finset.finite_toSet (Finset.range N)).countable)
      (fun n _ => measurableSet_eq_of_isWalkStopping _ hstop n)
  have hmeas : MeasurableSet {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤} := by
    have hset : {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤}
        = ⋃ N : ℕ, {X : ℕ → V | uncTime G r C X ℓ < (N : ℕ∞)} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        lift (uncTime G r C X ℓ : ℕ∞) to ℕ using ne_of_lt (lt_of_lt_of_le h le_top) with t
        exact ⟨t + 1, by exact_mod_cast Nat.lt_succ_self t⟩
      · rintro ⟨N, hN⟩
        exact lt_of_lt_of_le hN le_top
    rw [hset]
    exact MeasurableSet.iUnion hmeasN
  have hae := ae_uncTime_ne_top hG hdeg hdt r C hC o ℓ
  rw [ae_iff] at hae
  have hcompl : {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤}ᶜ
      = {X : ℕ → V | ¬ (uncTime G r C X ℓ : ℕ∞) ≠ ⊤} := by
    ext X
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    constructor
    · intro h hne
      exact h (lt_top_iff_ne_top.2 hne)
    · intro h hlt
      exact h (fun heq => absurd (heq ▸ hlt) (by simp))
  rw [← hcompl] at hae
  have h1 : (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤}ᶜ
      = 1 - (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤} := by
    have hne : (LatticeProb.Graph.walkLaw G o)
        {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤} ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _))
        (by rw [measure_univ (μ := LatticeProb.Graph.walkLaw G o)]; norm_num))
    rw [measure_compl hmeas hne, measure_univ
      (μ := LatticeProb.Graph.walkLaw G o)]
  rw [hae] at h1
  have h2 : (1 : ℝ≥0∞) ≤ (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤} := tsub_eq_zero_iff_le.1 h1.symm
  have h3 : (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤}
      ≤ (LatticeProb.Graph.walkLaw G o) (Set.univ : Set (ℕ → V)) :=
    measure_mono (Set.subset_univ _)
  rw [measure_univ] at h3
  exact le_antisymm h3 h2

/-- **Some `K` keeps the walk inside up to `T_ℓ` and captures the blocks.** -/
theorem exists_K_walkEvent2_prob (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (hdt : RWRS.DoublyTransient G)
    (r : ℕ) (C : V → Finset V) (hC : ∀ y : V, y ∈ C y) (o : V) (ℓ : ℕ)
    (K : ℕ → Finset V) (hexh : ∀ S : Finset V, ∃ n, S ⊆ K n) :
    ∃ K' : Finset V, (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (K' : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ K'} ≥ 15 / 16 := by
  set Km : ℕ → Finset V := fun n => (Finset.range n).biUnion K with hKm
  have hKmmono : ∀ a b : ℕ, a ≤ b → Km a ⊆ Km b := by
    intro a b hab S hS
    obtain ⟨i, hi, hSi⟩ := Finset.mem_biUnion.1 hS
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (Nat.lt_of_lt_of_le
      (Finset.mem_range.1 hi) hab), hSi⟩
  have hKmexh : ∀ S : Finset V, ∃ n, S ⊆ Km n := by
    intro S
    obtain ⟨n, hn⟩ := hexh S
    refine ⟨n + 1, ?_⟩
    intro x hx
    exact Finset.mem_biUnion.2 ⟨n, Finset.mem_range.2 (Nat.lt_succ_self n), hn hx⟩
  have hmono : Monotone (fun n : ℕ => {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
      < LatticeProb.Graph.exitTime (Km n : Set V) X
    ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ Km n}) := by
    intro a b hab X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    have hexit : LatticeProb.Graph.exitTime (Km a : Set V) X
        ≤ LatticeProb.Graph.exitTime (Km b : Set V) X := by
      refine sInf_le_sInf ?_
      rintro m ⟨n, rfl, hx⟩
      exact ⟨n, rfl, fun h => hx (hKmmono a b hab h)⟩
    exact ⟨lt_of_lt_of_le hX.1 hexit, fun i hi => Finset.Subset.trans (hX.2 i hi)
      (hKmmono a b hab)⟩
  have hcover : {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞) < ⊤}
      ⊆ ⋃ n : ℕ, {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (Km n : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ Km n} :=
    walkEvent2_iUnion_cover G r C Km hKmexh ℓ
  have hfull := measure_uncTime_lt_top hG hdeg hdt r C hC o ℓ
  have huni : (LatticeProb.Graph.walkLaw G o)
      (⋃ n : ℕ, {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (Km n : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ Km n}) = 1 := by
    refine le_antisymm ?_ ?_
    · rw [← measure_univ (μ := LatticeProb.Graph.walkLaw G o)]
      exact measure_mono (Set.subset_univ _)
    · rw [← hfull]
      exact measure_mono hcover
  by_contra hcon
  push Not at hcon
  have hT : Filter.Tendsto (fun n : ℕ => (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (Km n : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ Km n}) atTop
      (nhds ((LatticeProb.Graph.walkLaw G o)
        (⋃ n : ℕ, {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (Km n : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ Km n}))) := by
    exact tendsto_measure_iUnion_atTop
      (s := fun n : ℕ => {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (Km n : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ Km n})
      (μ := LatticeProb.Graph.walkLaw G o) hmono
  rw [huni] at hT
  have hmin : Filter.Tendsto (fun n : ℕ => min ((LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (Km n : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ Km n}) (15 / 16 : ℝ≥0∞)) atTop (nhds 1) := by
    exact hT.congr (fun n => (min_eq_left (le_of_lt (hcon (Km n)))).symm)
  have hle : (1 : ℝ≥0∞) ≤ 15 / 16 :=
    le_of_tendsto' hmin (fun c => min_le_right _ _)
  have h1516 : (15 / 16 : ℝ≥0∞) < 1 := by
    have h : (15 / 16 : ℝ≥0∞) < 16 / 16 := by
      refine ENNReal.div_lt_div_iff_left (by norm_num) (by norm_num) |>.2 ?_
      exact_mod_cast Nat.lt_succ_self 15
    rwa [ENNReal.div_self (by norm_num) (by norm_num)] at h
  exact absurd hle (not_le.2 h1516)

end RWRS.Support