/-
# The walk-good event for the trap rule

`walkGoodEvent G r C ℓ K N` is the event that the constrained stage recursion
completes `ℓ` stages inside `K` and below the horizon `N`, with all the trap
sites inside `K`, and that the walk leaves `K` before the horizon.  On this
event every stage is usable, so the rule can use all `ℓ + 1` of them, and the
failure case of Step 1 costs nothing because the rule then stops outside `K`.

The event is decided by the trajectory up to the horizon, and it contains the
exit-based event of `DTWalkEvent2` intersected with `{τ_K < N}`, which is how
its probability is bounded below.
-/
import RWRS.Support.DTStageCount
import RWRS.Support.DTStagesAE
import RWRS.Support.DTUncAE
import RWRS.Support.DTStopMeas
import RWRS.Support.DTNatConv

namespace RWRS.Support

open MeasureTheory LatticeProb Filter
open scoped Classical ENNReal

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable V] [Infinite V]

/-- **The exit event**: the walk leaves `K` before the horizon. -/
def exitEvent (K : Finset V) (N : ℕ) : Set (ℕ → V) := {X : ℕ → V | ∃ n, n < N ∧ X n ∉ K}

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **Not having left `K` before the horizon is staying in `K`.** -/
theorem compl_exitEvent_subset (K : Finset V) {N : ℕ} (hN : 0 < N) :
    (exitEvent (V := V) K N)ᶜ ⊆ LatticeProb.Graph.stayIn (K : Set V) (N - 1) := by
  intro X hX j hj
  by_contra hjK
  exact hX ⟨j, by omega, hjK⟩

omit [DecidableEq V] [Infinite V] [Countable V] in
/-- **The exit event is measurable.** -/
theorem measurableSet_exitEvent (K : Finset V) (N : ℕ) :
    MeasurableSet (exitEvent (V := V) K N) := by
  have : exitEvent (V := V) K N = ⋃ n ∈ Finset.range N, {X : ℕ → V | X n ∉ K} := by
    ext X
    simp [exitEvent, Finset.mem_range]
  rw [this]
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun n _ => ?_
  have hm : MeasurableSet ((K : Set V)ᶜ) := (K.finite_toSet.measurableSet).compl
  have heq : {X : ℕ → V | X n ∉ K} = (fun X : ℕ → V => X n) ⁻¹' ((K : Set V)ᶜ) := rfl
  rw [heq]
  exact (measurable_pi_apply n) hm

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **The exit event grows with the horizon.** -/
theorem exitEvent_mono (K : Finset V) {N M : ℕ} (h : N ≤ M) :
    exitEvent (V := V) K N ⊆ exitEvent K M := by
  rintro X ⟨n, hn, hnK⟩
  exact ⟨n, lt_of_lt_of_le hn h, hnK⟩

/-- **The walk-good event for the rule with parameters `(K, N)`.** -/
def walkGoodEvent (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (ℓ : ℕ) (K : Finset V) (N : ℕ) : Set (ℕ → V) :=
  {X : ℕ → V | (stageState G r C K N X ℓ).1 < N
    ∧ (∀ j ≤ (stageState G r C K N X ℓ).1, X j ∈ K)
    ∧ (stageState G r C K N X ℓ).2 ⊆ K
    ∧ X ∈ exitEvent K N}

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **On the walk-good event the walk leaves `K` before the horizon.** -/
theorem exitEvent_of_walkGood {r : ℕ} {C : V → Finset V} {ℓ : ℕ} {K : Finset V} {N : ℕ}
    {X : ℕ → V} (h : X ∈ walkGoodEvent G r C ℓ K N) : ∃ n, n < N ∧ X n ∉ K := h.2.2.2

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **On the walk-good event every stage is usable.** -/
theorem stageCnt_eq_of_walkGood (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) {N : ℕ}
    (hN : 0 < N) (X : ℕ → V) (h : X ∈ walkGoodEvent G r C ℓ K N) :
    stageCnt G r C ℓ K N X = ℓ + 1 := by
  have hlt : ℓ < stageCnt G r C ℓ K N X :=
    lt_stageCnt_of_fire r C ℓ K hN X le_rfl h.1 h.2.1 h.2.2.1
  exact le_antisymm (stageCnt_le r C ℓ K N X) hlt

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **The walk-good event is decided by the trajectory up to the horizon.** -/
theorem dependsUpTo_walkGoodEvent (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V)
    {N : ℕ} (hN : 0 < N) (c : ℝ) :
    LatticeProb.Graph.DependsUpTo N
      (fun X : ℕ → V => (walkGoodEvent G r C ℓ K N).indicator (fun _ => c) X) := by
  intro X Y hXY
  have hpre : stageState G r C K N X ℓ = stageState G r C K N Y ℓ :=
    stageState_prefix r C K hN hXY ℓ (stageState_le r C K hN X ℓ)
  have hiff : X ∈ walkGoodEvent G r C ℓ K N ↔ Y ∈ walkGoodEvent G r C ℓ K N := by
    simp only [walkGoodEvent, exitEvent, Set.mem_setOf_eq, hpre]
    constructor
    · rintro ⟨h1, h2, h3, n, hn, hnK⟩
      refine ⟨h1, fun j hj => ?_, h3, n, hn, ?_⟩
      · rw [← hXY j (le_trans hj (stageState_le r C K hN Y ℓ))]
        exact h2 j hj
      · rw [← hXY n (by omega)]
        exact hnK
    · rintro ⟨h1, h2, h3, n, hn, hnK⟩
      refine ⟨h1, fun j hj => ?_, h3, n, hn, ?_⟩
      · rw [hXY j (le_trans hj (stageState_le r C K hN Y ℓ))]
        exact h2 j hj
      · rw [hXY n (by omega)]
        exact hnK
  by_cases hX : X ∈ walkGoodEvent G r C ℓ K N
  · show (walkGoodEvent G r C ℓ K N).indicator (fun _ => c) X
      = (walkGoodEvent G r C ℓ K N).indicator (fun _ => c) Y
    rw [Set.indicator_of_mem hX, Set.indicator_of_mem (hiff.1 hX)]
  · show (walkGoodEvent G r C ℓ K N).indicator (fun _ => c) X
      = (walkGoodEvent G r C ℓ K N).indicator (fun _ => c) Y
    rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun hY => hX (hiff.2 hY))]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **The exit event is decided by the trajectory up to the horizon.** -/
theorem dependsUpTo_exitEvent (K : Finset V) (N : ℕ) (c : ℝ) :
    LatticeProb.Graph.DependsUpTo N
      (fun X : ℕ → V => ((exitEvent K N)ᶜ).indicator (fun _ => c) X) := by
  intro X Y hXY
  have hiff : X ∈ exitEvent K N ↔ Y ∈ exitEvent K N := by
    constructor
    · rintro ⟨n, hn, hnK⟩
      exact ⟨n, hn, by rw [← hXY n (by omega)]; exact hnK⟩
    · rintro ⟨n, hn, hnK⟩
      exact ⟨n, hn, by rw [hXY n (by omega)]; exact hnK⟩
  have hiffc : X ∈ (exitEvent K N)ᶜ ↔ Y ∈ (exitEvent K N)ᶜ := by
    simp only [Set.mem_compl_iff]
    exact not_congr hiff
  by_cases hX : X ∈ (exitEvent K N)ᶜ
  · show ((exitEvent K N)ᶜ).indicator (fun _ => c) X
      = ((exitEvent K N)ᶜ).indicator (fun _ => c) Y
    rw [Set.indicator_of_mem hX, Set.indicator_of_mem (hiffc.1 hX)]
  · show ((exitEvent K N)ᶜ).indicator (fun _ => c) X
      = ((exitEvent K N)ᶜ).indicator (fun _ => c) Y
    rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun hY => hX (hiffc.2 hY))]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **A good walk leaves `K` before the horizon.** -/
theorem walkGoodEvent_subset_exitEvent (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V)
    (N : ℕ) : walkGoodEvent G r C ℓ K N ⊆ exitEvent K N := fun _ h => h.2.2.2

end RWRS.Support
