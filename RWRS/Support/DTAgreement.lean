import RWRS.Support.DTStages
import RWRS.Support.DTUnconstrained

/-!
# Agreement of the constrained and unconstrained stages

On a trajectory that stays in `K` up to the horizon `N` and whose
unconstrained stage times are finite and below `N`, the constrained stage
recursion of `trapRule` makes the same choices as the unconstrained one.
-/

namespace RWRS.Support

open scoped Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The unconstrained stage times are monotone.** -/
theorem uncTime_mono (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) {i j : ℕ} (hij : i ≤ j) :
    uncTime G r C X i ≤ uncTime G r C X j := by
  induction hij with
  | refl => exact le_refl _
  | @step k _ ih =>
    by_cases h : (uncStageState G r C X k).1 = ⊤
    · have h1 : uncTime G r C X k = ⊤ := by
        simp only [uncTime]; exact h
      have h2 := uncTime_top_frozen G r C X k h1 (k + 1) (Nat.le_succ k)
      have h2' : uncTime G r C X (k + 1) = ⊤ := by
        simp only [uncTime]; rw [h2]; exact h
      rw [h2']
      exact le_top
    · exact le_trans ih (le_of_lt (uncTime_lt G r C X k (by
        intro hh
        exact h hh)))

/-- **On a good trajectory the constrained stage step is the unconstrained one.**
If the walk stays in `K` up to the next unconstrained stage time, that time
exists strictly before the horizon, then the
constrained step selects exactly the unconstrained next stage time. -/
theorem sInf_stageSet_eq_find (r : ℕ) (_C : V → Finset V) (K : Finset V) (N : ℕ)
    (X : ℕ → V) (t : ℕ) (F : Finset V)
    (hex : ∃ m : ℕ, t < m ∧ Admissible G r F (X m))
    (hin : ∀ j ≤ Nat.find hex, X j ∈ K)
    (hfind : Nat.find hex < N) :
    sInf (stageSet G r K N X (t, F)) = Nat.find hex := by
  have hmem : Nat.find hex ∈ stageSet G r K N X (t, F) :=
    Or.inr ⟨(Nat.find_spec hex).1, hfind, hin, (Nat.find_spec hex).2⟩
  have hle : ∀ m ∈ stageSet G r K N X (t, F), Nat.find hex ≤ m := by
    intro m hm
    rcases hm with rfl | hm
    · exact le_of_lt hfind
    · exact Nat.find_min' hex ⟨hm.1, hm.2.2.2⟩
  exact le_antisymm (Nat.sInf_le hmem) (hle _ (Nat.sInf_mem ⟨_, hmem⟩))
/-- **On a good trajectory the constrained stages agree with the unconstrained
ones.**  If the walk stays in `K` up to the horizon `N`, every unconstrained
stage time up to `ℓ` is finite and strictly below `N`, and every used set up
to `ℓ` lies in `K`, then the constrained stage state at `i ≤ ℓ` is exactly the
unconstrained one. -/
theorem stageState_eq_uncStageState (r : ℕ) (C : V → Finset V) (K : Finset V) (N : ℕ)
    (X : ℕ → V) (ℓ : ℕ)
    (hin : ∀ j ≤ (uncTime G r C X ℓ).toNat, X j ∈ K)
    (hfin : ∀ i ≤ ℓ, uncTime G r C X i ≠ ⊤ ∧ (uncTime G r C X i) < (N : ℕ∞))
    (_hused : ∀ i ≤ ℓ, uncUsed G r C X i ⊆ K) :
    ∀ i ≤ ℓ, stageState G r C K N X i
      = ((uncTime G r C X i).toNat, uncUsed G r C X i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rfl
  | succ i ih =>
    intro hi
    have hile : i ≤ ℓ := Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl ℓ)
    have hprev := ih hile
    obtain ⟨hne, hltN⟩ := hfin (i + 1) hi
    obtain ⟨hne', hltN'⟩ := hfin i hile
    have hex : ∃ m : ℕ, (uncTime G r C X i).toNat < m ∧
        Admissible G r (uncUsed G r C X i) (X m) := by
      by_contra hno
      have htop : uncTime G r C X (i + 1) = ⊤ := by
        simp only [uncTime, uncStageState, uncStageStep, uncUsed] at hne' hno ⊢
        rw [if_neg hne', dif_neg hno]
      exact hne htop
    have hstep := uncTime_succ_of_ex G r C X i hne' hex
    rw [hstep.1] at hltN
    have hfindlt : Nat.find hex < N := by exact_mod_cast hltN
    have hℓne : uncTime G r C X ℓ ≠ ⊤ := (hfin ℓ (Nat.le_refl ℓ)).1
    have hfindle : Nat.find hex ≤ (uncTime G r C X ℓ).toNat := by
      have hmono := uncTime_mono G r C X hi
      rw [hstep.1] at hmono
      exact ENat.toNat_le_toNat hmono hℓne
    have hsInf := sInf_stageSet_eq_find r C K N X (uncTime G r C X i).toNat
      (uncUsed G r C X i) hex (fun j hj => hin j (Nat.le_trans hj hfindle)) hfindlt
    have hss : stageState G r C K N X (i + 1)
        = (Nat.find hex, uncUsed G r C X i ∪ C (X (Nat.find hex))) := by
      show stageStep G r C K N X (stageState G r C K N X i)
        = (Nat.find hex, uncUsed G r C X i ∪ C (X (Nat.find hex)))
      rw [hprev]
      simp only [stageStep]
      rw [hsInf]
    have hcoe : ((Nat.find hex : ℕ∞).toNat) = Nat.find hex := ENat.toNat_coe (Nat.find hex)
    rw [hss, hstep.2]
    rw [hstep.1]
    exact Prod.ext hcoe.symm rfl
