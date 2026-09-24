/-
Choosing the finite set and the horizon of Step 1.

The exit-based event of `DTWalkEvent2` has probability at least `15/16` for a
suitable `K`, and for that `K` the walk leaves before a large enough horizon
with probability as close to one as wanted.  On the intersection every stage is
usable, so the intersection lies in the walk-good event.
-/
import RWRS.Support.DTWalkGood
import RWRS.Support.DTWalkEvent2
import RWRS.Support.DTLeave

namespace RWRS.Support

open MeasureTheory LatticeProb Filter
open scoped Classical ENNReal

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable V] [Infinite V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V] [DecidableEq V] in
/-- **The exit-based event and the exit event together give a good walk.** -/
theorem walkEvent2_inter_exit_subset_walkGood (r : ℕ) (C : V → Finset V) (ℓ : ℕ)
    (K : Finset V) (N : ℕ) :
    ({X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (K : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ K} ∩ exitEvent K N)
      ⊆ walkGoodEvent G r C ℓ K N := by
  rintro X ⟨⟨hlt, hused⟩, hexit⟩
  obtain ⟨n, hnN, hnK⟩ := hexit
  have hne : uncTime G r C X ℓ ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    exact absurd hlt (by simp)
  have hstay : ∀ j ≤ (uncTime G r C X ℓ).toNat, X j ∈ K := by
    have hcoe : ((uncTime G r C X ℓ).toNat : ℕ∞) = uncTime G r C X ℓ :=
      ENat.coe_toNat hne
    have : X ∈ LatticeProb.Graph.stayIn (K : Set V) ((uncTime G r C X ℓ).toNat) := by
      rw [LatticeProb.Graph.stayIn_eq_lt_exitTime]
      rw [Set.mem_setOf_eq, hcoe]
      exact hlt
    exact this
  have hexitle : LatticeProb.Graph.exitTime (K : Set V) X ≤ (n : ℕ∞) := by
    by_contra hcon
    have hstayn : X ∈ LatticeProb.Graph.stayIn (K : Set V) n := by
      rw [LatticeProb.Graph.stayIn_eq_lt_exitTime]
      exact Set.mem_setOf.2 (not_le.1 hcon)
    exact hnK (hstayn n le_rfl)
  have hTN : uncTime G r C X ℓ < (N : ℕ∞) :=
    lt_of_lt_of_le (lt_of_lt_of_le hlt hexitle) (by exact_mod_cast Nat.le_of_lt hnN)
  have hall : ∀ i ≤ ℓ, StageOK G r C K N X i := by
    intro i hi
    refine ⟨lt_of_le_of_lt (uncTime_mono G r C X hi) hTN, fun j hj => ?_, hused i hi⟩
    exact hstay j (le_trans hj (ENat.toNat_le_toNat (uncTime_mono G r C X hi) hne))
  have hcnt : stageCnt G r C ℓ K N X = ℓ + 1 := stageCnt_eq_of_all r C ℓ K N X hall
  have hagree : stageState G r C K N X ℓ
      = ((uncTime G r C X ℓ).toNat, uncUsed G r C X ℓ) :=
    stageState_eq_of_lt_stageCnt r C ℓ K N X (by omega)
  refine ⟨?_, ?_, ?_, ⟨n, hnN, hnK⟩⟩
  · rw [hagree]
    exact toNat_lt_of_lt_coe _ _ hTN
  · rw [hagree]
    exact hstay
  · rw [hagree]
    exact hused ℓ le_rfl

/-- **Intersecting with an event of small complement costs little mass.** -/
theorem toReal_measure_inter_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A B : Set Ω) :
    (μ A).toReal - (μ Bᶜ).toReal ≤ (μ (A ∩ B)).toReal := by
  have hsub : A ⊆ (A ∩ B) ∪ Bᶜ := by
    intro x hx
    by_cases hB : x ∈ B
    · exact Or.inl ⟨hx, hB⟩
    · exact Or.inr hB
  have h1 : μ A ≤ μ (A ∩ B) + μ Bᶜ :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  have hfin : ∀ S : Set Ω, μ S ≠ ⊤ := fun S =>
    ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ S)) (by simp))
  have h2 : (μ A).toReal ≤ (μ (A ∩ B)).toReal + (μ Bᶜ).toReal := by
    rw [← ENNReal.toReal_add (hfin _) (hfin _)]
    exact ENNReal.toReal_mono (by
      exact ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩) h1
  linarith

/-- **The horizon of Step 1**: given a finite set that the walk keeps its
stages inside, a horizon by which it has left with probability at least `1 - δ`,
and for which the walk is good with probability at least three quarters. -/
theorem exists_N_walkGood (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (r : ℕ) (C : V → Finset V) (o : V) (ℓ : ℕ) (K : Finset V)
    (hK : (15 : ℝ≥0∞) / 16 ≤ (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
          < LatticeProb.Graph.exitTime (K : Set V) X
        ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ K})
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N
      ∧ (3 : ℝ) / 4 ≤ ((LatticeProb.Graph.walkLaw G o) (walkGoodEvent G r C ℓ K N)).toReal
      ∧ ((LatticeProb.Graph.walkLaw G o) (exitEvent K N)ᶜ).toReal ≤ δ := by
  set A : Set (ℕ → V) := {X : ℕ → V | (uncTime G r C X ℓ : ℕ∞)
      < LatticeProb.Graph.exitTime (K : Set V) X
    ∧ ∀ i, i ≤ ℓ → uncUsed G r C X i ⊆ K} with hA
  have hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V) := esc_of_finset hG K
  set η : ℝ≥0∞ := min (ENNReal.ofReal δ) (1 / 16) with hη
  have hηpos : 0 < η := lt_min (ENNReal.ofReal_pos.2 hδ) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := exists_N_stayIn_le hdeg K hesc o hηpos
  have hcompl : (exitEvent K (N₀ + 1))ᶜ ⊆ LatticeProb.Graph.stayIn (K : Set V) N₀ := by
    have := compl_exitEvent_subset (V := V) K (N := N₀ + 1) (Nat.succ_pos _)
    simpa using this
  have hfin : ∀ S : Set (ℕ → V), (LatticeProb.Graph.walkLaw G o) S ≠ ⊤ := fun S =>
    ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ S)) (by simp))
  refine ⟨N₀ + 1, Nat.succ_pos _, ?_, ?_⟩
  · have hsmall : (LatticeProb.Graph.walkLaw G o) (exitEvent K (N₀ + 1))ᶜ ≤ 1 / 16 :=
      le_trans (le_trans (measure_mono hcompl) hN₀) (min_le_right _ _)
    have hAge : (15 : ℝ) / 16 ≤ ((LatticeProb.Graph.walkLaw G o) A).toReal := by
      have h := ENNReal.toReal_mono (hfin A) hK
      simpa using h
    have hBle : ((LatticeProb.Graph.walkLaw G o) (exitEvent K (N₀ + 1))ᶜ).toReal ≤ 1 / 16 := by
      have h := ENNReal.toReal_mono (by norm_num) hsmall
      simpa using h
    have hinter := toReal_measure_inter_ge (μ := LatticeProb.Graph.walkLaw G o) A
      (exitEvent K (N₀ + 1))
    have hmono : ((LatticeProb.Graph.walkLaw G o) (A ∩ exitEvent K (N₀ + 1))).toReal
        ≤ ((LatticeProb.Graph.walkLaw G o) (walkGoodEvent G r C ℓ K (N₀ + 1))).toReal :=
      ENNReal.toReal_mono (hfin _)
        (measure_mono (walkEvent2_inter_exit_subset_walkGood r C ℓ K (N₀ + 1)))
    linarith
  · have hsmall : (LatticeProb.Graph.walkLaw G o) (exitEvent K (N₀ + 1))ᶜ
        ≤ ENNReal.ofReal δ :=
      le_trans (le_trans (measure_mono hcompl) hN₀) (min_le_left _ _)
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsmall
    rw [ENNReal.toReal_ofReal hδ.le] at h
    exact h

end RWRS.Support
