/-
How many stages the capped rule can use on a given trajectory.

A stage is usable when its unconstrained time is below the horizon, the walk is
inside `K` up to it, and the sites it has used lie in `K`.  Usability is
inherited by earlier stages, so the usable stages form an initial segment whose
length is `stageCnt`.  Below `stageCnt` the constrained stage recursion of the
rule agrees with the unconstrained one; at or above it the rule can never fire,
because a firing stage would make the next stage usable as well.
-/
import RWRS.Support.DTAgreement
import RWRS.Support.DTCappedRule
import RWRS.Support.DTStageAdm

open scoped Classical ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The constrained used sets grow along the stages.** -/
theorem stageState_used_mono (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ)
    (X : ℕ → V) {i j : ℕ} (hij : i ≤ j) :
    (stageState G r C K N X i).2 ⊆ (stageState G r C K N X j).2 := by
  rw [stageState_snd r C K N X i, stageState_snd r C K N X j]
  intro v hv
  obtain ⟨a, ha, hva⟩ := Finset.mem_biUnion.1 hv
  exact Finset.mem_biUnion.2 ⟨a, Finset.mem_range.2 (by
    have := Finset.mem_range.1 ha; omega), hva⟩

/-- **A usable stage**: its unconstrained time lies below the horizon, the walk
stays in `K` up to it, and the sites used lie in `K`. -/
def StageOK (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (K : Finset V) (N : ℕ) (X : ℕ → V) (i : ℕ) : Prop :=
  uncTime G r C X i < (N : ℕ∞) ∧ (∀ j ≤ (uncTime G r C X i).toNat, X j ∈ K)
    ∧ uncUsed G r C X i ⊆ K

/-- **Usability is inherited by earlier stages.** -/
theorem StageOK.mono {r : ℕ} {C : V → Finset V} {K : Finset V} {N : ℕ} {X : ℕ → V}
    {i j : ℕ} (hij : i ≤ j) (h : StageOK G r C K N X j) : StageOK G r C K N X i := by
  obtain ⟨h1, h2, h3⟩ := h
  have hmono : uncTime G r C X i ≤ uncTime G r C X j := uncTime_mono G r C X hij
  have hjne : uncTime G r C X j ≠ ⊤ := ne_top_of_lt h1
  refine ⟨lt_of_le_of_lt hmono h1, fun k hk => h2 k ?_, ?_⟩
  · exact le_trans hk (ENat.toNat_le_toNat hmono hjne)
  · exact Finset.Subset.trans (uncUsed_mono' G r C X hij) h3

/-- **The number of usable stages**, capped at `ℓ + 1`. -/
noncomputable def stageCnt (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ) (X : ℕ → V) : ℕ :=
  sInf {n : ℕ | ¬ (n ≤ ℓ ∧ StageOK G r C K N X n)}

theorem stageCnt_le (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ)
    (X : ℕ → V) : stageCnt G r C ℓ K N X ≤ ℓ + 1 :=
  Nat.sInf_le (Set.mem_setOf.2 fun h => absurd h.1 (by omega))

theorem stageCnt_spec (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ)
    (X : ℕ → V) :
    ¬ (stageCnt G r C ℓ K N X ≤ ℓ ∧ StageOK G r C K N X (stageCnt G r C ℓ K N X)) := by
  have h : sInf {n : ℕ | ¬ (n ≤ ℓ ∧ StageOK G r C K N X n)}
      ∈ {n : ℕ | ¬ (n ≤ ℓ ∧ StageOK G r C K N X n)} :=
    Nat.sInf_mem ⟨ℓ + 1, Set.mem_setOf.2 fun hh => absurd hh.1 (by omega)⟩
  exact h

/-- **Every stage below the count is usable.** -/
theorem stageOK_of_lt_stageCnt (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V)
    (N : ℕ) (X : ℕ → V) {i : ℕ} (hi : i < stageCnt G r C ℓ K N X) :
    i ≤ ℓ ∧ StageOK G r C K N X i := by
  by_contra hcon
  exact absurd (Nat.sInf_le (Set.mem_setOf.2 hcon)) (not_le.2 hi)

/-- **Below the count the constrained stages agree with the unconstrained
ones.** -/
theorem stageState_eq_of_lt_stageCnt (r : ℕ) (C : V → Finset V) (ℓ : ℕ)
    (K : Finset V) (N : ℕ) (X : ℕ → V) {i : ℕ} (hi : i < stageCnt G r C ℓ K N X) :
    stageState G r C K N X i = ((uncTime G r C X i).toNat, uncUsed G r C X i) := by
  have hok : ∀ j ≤ i, StageOK G r C K N X j := fun j hj =>
    (stageOK_of_lt_stageCnt r C ℓ K N X (lt_of_le_of_lt hj hi)).2
  refine stageState_eq_uncStageState r C K N X i (hok i le_rfl).2.1 ?_
    (fun j hj => (hok j hj).2.2) i le_rfl
  intro j hj
  exact ⟨ne_top_of_lt (hok j hj).1, (hok j hj).1⟩

/-- **A constrained stage inside `K` and below the horizon is usable**, provided
every earlier stage is. -/
theorem stageOK_of_constrained (r : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ}
    (hN : 0 < N) (X : ℕ → V) (c : ℕ)
    (hprev : ∀ j < c, StageOK G r C K N X j)
    (hA : (stageState G r C K N X c).1 < N)
    (hB : ∀ j ≤ (stageState G r C K N X c).1, X j ∈ K)
    (hC2 : (stageState G r C K N X c).2 ⊆ K) :
    StageOK G r C K N X c := by
  cases c with
  | zero =>
      have h0 : (stageState G r C K N X 0) = (0, C (X 0)) := rfl
      refine ⟨?_, ?_, ?_⟩
      · show (0 : ℕ∞) < (N : ℕ∞)
        exact_mod_cast hN
      · intro j hj
        have hj0 : j ≤ (stageState G r C K N X 0).1 := by
          have hu : (uncTime G r C X 0).toNat = 0 := rfl
          have hs : (stageState G r C K N X 0).1 = 0 := rfl
          rw [hu] at hj
          omega
        exact hB j hj0
      · show C (X 0) ⊆ K
        rw [h0] at hC2
        exact hC2
  | succ d =>
      have hprevd : StageOK G r C K N X d := hprev d (Nat.lt_succ_self d)
      have hagree : stageState G r C K N X d
          = ((uncTime G r C X d).toNat, uncUsed G r C X d) := by
        refine stageState_eq_uncStageState r C K N X d hprevd.2.1 ?_
          (fun j hj => (StageOK.mono hj hprevd).2.2) d le_rfl
        intro j hj
        exact ⟨ne_top_of_lt (StageOK.mono hj hprevd).1, (StageOK.mono hj hprevd).1⟩
      have hstepfst : (stageState G r C K N X (d + 1)).1
          = sInf (stageSet G r K N X ((uncTime G r C X d).toNat, uncUsed G r C X d)) := by
        show (stageStep G r C K N X (stageState G r C K N X d)).1 = _
        rw [hagree]
        rfl
      have hstepsnd : (stageState G r C K N X (d + 1)).2
          = uncUsed G r C X d
            ∪ C (X (sInf (stageSet G r K N X
              ((uncTime G r C X d).toNat, uncUsed G r C X d)))) := by
        show (stageStep G r C K N X (stageState G r C K N X d)).2 = _
        rw [hagree]
        rfl
      have hsmem : sInf (stageSet G r K N X ((uncTime G r C X d).toNat, uncUsed G r C X d))
          ∈ stageSet G r K N X ((uncTime G r C X d).toNat, uncUsed G r C X d) :=
        Nat.sInf_mem ⟨N, stageSet_nonempty r K N X _⟩
      have hsN : sInf (stageSet G r K N X ((uncTime G r C X d).toNat, uncUsed G r C X d)) < N := by
        rw [← hstepfst]; exact hA
      rcases hsmem with heq | ⟨hlt, _, hin, hadm⟩
      · rw [heq] at hsN; exact absurd hsN (lt_irrefl N)
      · have hex : ∃ m : ℕ, (uncTime G r C X d).toNat < m
            ∧ Admissible G r (uncUsed G r C X d) (X m) := ⟨_, hlt, hadm⟩
        have hfindle : Nat.find hex
            ≤ sInf (stageSet G r K N X ((uncTime G r C X d).toNat, uncUsed G r C X d)) :=
          Nat.find_min' hex ⟨hlt, hadm⟩
        have hfindin : ∀ j ≤ Nat.find hex, X j ∈ K := fun j hj => hin j (le_trans hj hfindle)
        have hfindlt : Nat.find hex < N := lt_of_le_of_lt hfindle hsN
        have hsInfeq : sInf (stageSet G r K N X
            ((uncTime G r C X d).toNat, uncUsed G r C X d)) = Nat.find hex :=
          sInf_stageSet_eq_find r C K N X _ _ hex hfindin hfindlt
        have hne' : (uncStageState G r C X d).1 ≠ ⊤ := ne_top_of_lt hprevd.1
        obtain ⟨ht1, ht2⟩ := uncTime_succ_of_ex G r C X d hne' hex
        refine ⟨?_, ?_, ?_⟩
        · rw [ht1]; exact_mod_cast hfindlt
        · rw [ht1]
          simp only [ENat.toNat_coe]
          exact hfindin
        · rw [ht2]
          rw [hstepsnd, hsInfeq] at hC2
          exact hC2

/-- **If every stage up to `ℓ` is usable the count is `ℓ + 1`.** -/
theorem stageCnt_eq_of_all (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) (N : ℕ)
    (X : ℕ → V) (hall : ∀ i ≤ ℓ, StageOK G r C K N X i) :
    stageCnt G r C ℓ K N X = ℓ + 1 := by
  refine le_antisymm (stageCnt_le r C ℓ K N X) ?_
  by_contra hlt
  have hle : stageCnt G r C ℓ K N X ≤ ℓ := by omega
  exact stageCnt_spec r C ℓ K N X ⟨hle, hall _ hle⟩

/-- **The rule can only fire at a stage below the count.** -/
theorem lt_stageCnt_of_fire (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) {N : ℕ}
    (hN : 0 < N) (X : ℕ → V) {i : ℕ} (hiℓ : i ≤ ℓ)
    (h1 : (stageState G r C K N X i).1 < N)
    (h2 : ∀ j ≤ (stageState G r C K N X i).1, X j ∈ K)
    (h3 : (stageState G r C K N X i).2 ⊆ K) :
    i < stageCnt G r C ℓ K N X := by
  by_contra hcon
  have hci : stageCnt G r C ℓ K N X ≤ i := Nat.not_lt.1 hcon
  have hcl : stageCnt G r C ℓ K N X ≤ ℓ := le_trans hci hiℓ
  refine stageCnt_spec r C ℓ K N X ⟨hcl, ?_⟩
  have hmono1 : (stageState G r C K N X (stageCnt G r C ℓ K N X)).1
      ≤ (stageState G r C K N X i).1 := stageState_mono' r C K hN X hci
  refine stageOK_of_constrained r C K hN X _
    (fun j hj => (stageOK_of_lt_stageCnt r C ℓ K N X hj).2)
    (lt_of_le_of_lt hmono1 h1) (fun j hj => h2 j (le_trans hj hmono1))
    (Finset.Subset.trans (stageState_used_mono r C K N X hci) h3)

end RWRS.Support
