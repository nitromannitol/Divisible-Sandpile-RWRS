/-
The unconstrained stage sequence of Step 1 of
`prop:doubly-transient-really-general`.

The paper selects the centres of its traps along the walk path alone: `T_0 = 0`,
`F_0 = ∅`, and `T_{i+1}` is the first time at or after `T_i` at which the walk
sits at a site admissible for the used set `F_i`; `F_{i+1} = F_i ∪ C(X_{T_{i+1}})`.
The scenery never enters the selection, so conditionally on the walk the trap
sets are fixed pairwise disjoint finite sets.

The times are `ℕ∞`-valued: a trajectory that never reaches the admissible set
gives `⊤`, which is the almost-surely-excluded case.  The `sInf` over `ℕ∞` is
reduced to an `ℕ`-`sInf` through the two cast lemmas below, which is what makes
the prefix and stopping-time arguments ordinary `ℕ` arguments, exactly as in
`DTStages.lean` for the truncated sequence.
-/
import RWRS.Support.DTAdmissible
import LatticeProb.Graph.MarkovAE

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The stage sequence -/

open scoped Classical in
noncomputable def stageE (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) : ℕ → ℕ∞ × Finset V
  | 0 => (0, ∅)
  | i + 1 =>
      let p := stageE G r C X i
      let T := sInf {k : ℕ∞ | ∃ n : ℕ, k = (n : ℕ∞) ∧ p.1 ≤ (n : ℕ∞) ∧
        Admissible G r p.2 (X n)}
      (T, p.2 ∪ C (X T.toNat))

open scoped Classical in
noncomputable def stageTime (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ) : ℕ∞ :=
  (stageE G r C X i).1

open scoped Classical in
noncomputable def stageUsed (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ) : Finset V :=
  (stageE G r C X i).2

def stageNext (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (X : ℕ → V) (i : ℕ) : Set ℕ :=
  {n : ℕ | stageTime G r C X i ≤ (n : ℕ∞) ∧ Admissible G r (stageUsed G r C X i) (X n)}

theorem stageTime_succ (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (X : ℕ → V) (i : ℕ) :
    stageTime G r C X (i + 1) = sInf {k : ℕ∞ | ∃ n : ℕ, k = (n : ℕ∞) ∧
      stageTime G r C X i ≤ (n : ℕ∞) ∧ Admissible G r (stageUsed G r C X i) (X n)} := rfl

theorem stageUsed_succ (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ) (C : V → Finset V)
    (X : ℕ → V) (i : ℕ) :
    stageUsed G r C X (i + 1)
      = stageUsed G r C X i ∪ C (X (stageTime G r C X (i + 1)).toNat) := rfl

theorem stageTime_mono (r : ℕ) (C : V → Finset V) (X : ℕ → V) (i : ℕ) :
    stageTime G r C X i ≤ stageTime G r C X (i + 1) := by
  rw [stageTime_succ]
  refine le_sInf ?_; rintro k ⟨n, rfl, hn, -⟩; exact hn

theorem sInf_cast_eq_top (Q : ℕ → Prop) :
    sInf {k : ℕ∞ | ∃ n : ℕ, k = (n : ℕ∞) ∧ Q n} = ⊤ ↔ ∀ n : ℕ, ¬ Q n := by
  constructor
  · intro h n hn
    have hle : sInf {k : ℕ∞ | ∃ n : ℕ, k = (n : ℕ∞) ∧ Q n} ≤ (n : ℕ∞) :=
      sInf_le ⟨n, rfl, hn⟩
    rw [h] at hle
    exact absurd (top_le_iff.1 hle) (ENat.coe_ne_top n)
  · intro h
    have hempty : {k : ℕ∞ | ∃ n : ℕ, k = (n : ℕ∞) ∧ Q n} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 (by rintro k ⟨n, rfl, hn⟩; exact h n hn)
    rw [hempty, sInf_empty]

theorem sInf_cast_eq_cast (Q : ℕ → Prop) (n₀ : ℕ) (h₀ : Q n₀) :
    sInf {k : ℕ∞ | ∃ n : ℕ, k = (n : ℕ∞) ∧ Q n}
      = ((sInf {n : ℕ | Q n} : ℕ) : ℕ∞) := by
  have mem_cast_sInf : ((sInf {n : ℕ | Q n} : ℕ) : ℕ∞)
      ∈ {k : ℕ∞ | ∃ n : ℕ, k = (n : ℕ∞) ∧ Q n} :=
    ⟨(sInf {n : ℕ | Q n} : ℕ), rfl, Nat.sInf_mem ⟨n₀, h₀⟩⟩
  refine le_antisymm ?_ ?_
  · exact sInf_le mem_cast_sInf
  · refine le_sInf (fun k hk => by
      obtain ⟨n, rfl, hn⟩ := hk
      exact Nat.cast_le.2 (Nat.sInf_le (s := {m : ℕ | Q m}) hn))

theorem exists_mem_of_sInf_cast_le (Q : ℕ → Prop) {k : ℕ}
    (h : sInf {m : ℕ∞ | ∃ n : ℕ, m = (n : ℕ∞) ∧ Q n} ≤ (k : ℕ∞)) :
    ∃ n₀ : ℕ, Q n₀ := by
  by_contra hc
  have hempty : ∀ n : ℕ, ¬ Q n := fun n hn => hc ⟨n, hn⟩
  have htop : sInf {m : ℕ∞ | ∃ n : ℕ, m = (n : ℕ∞) ∧ Q n} = ⊤ :=
    (sInf_cast_eq_top Q).2 hempty
  rw [htop] at h
  exact absurd (top_le_iff.1 h) (ENat.coe_ne_top k)

theorem stageE_prefix (r : ℕ) (C : V → Finset V) {X Y : ℕ → V} {k : ℕ}
    (h : ∀ j ≤ k, X j = Y j) :
    ∀ i, stageTime G r C X i ≤ (k : ℕ∞) → stageE G r C X i = stageE G r C Y i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro hle
      have hi : stageTime G r C X i ≤ (k : ℕ∞) :=
        le_trans (stageTime_mono r C X i) hle
      have hp := ih hi
      -- the used sets and times of order i agree
      have hT : stageTime G r C X i = stageTime G r C Y i := congrArg Prod.fst hp
      have hF : stageUsed G r C X i = stageUsed G r C Y i := congrArg Prod.snd hp
      -- the next-time sets agree on members ≤ k
      have hagree : ∀ m : ℕ, m ≤ k →
          (m ∈ stageNext G r C X i ↔ m ∈ stageNext G r C Y i) := by
        intro m hm
        simp only [stageNext, Set.mem_setOf_eq, hT, hF]
        rw [h m hm]
      -- both next times are ≤ k, so both sInfs are casts of ℕ-sInfs of nonempty sets
      -- the next-time predicate, as a function of the trajectory
      have hQX : ∀ m : ℕ, m ∈ stageNext G r C X i ↔ (stageTime G r C X i ≤ (m : ℕ∞)
          ∧ Admissible G r (stageUsed G r C X i) (X m)) := fun m => Iff.rfl
      -- nonemptiness of both next sets, from hle
      have hneX : ∃ n₀ : ℕ, n₀ ∈ stageNext G r C X i := by
        have h1 := hle
        rw [stageTime_succ] at h1
        exact exists_mem_of_sInf_cast_le
          (fun n => stageTime G r C X i ≤ (n : ℕ∞)
            ∧ Admissible G r (stageUsed G r C X i) (X n)) h1
      have hXk : sInf (stageNext G r C X i) ≤ k := by
        have h1 := hle
        rw [stageTime_succ,
          sInf_cast_eq_cast (fun n => stageTime G r C X i ≤ (n : ℕ∞)
            ∧ Admissible G r (stageUsed G r C X i) (X n)) hneX.choose hneX.choose_spec] at h1
        exact Nat.cast_le.1 h1
      have hneY : ∃ n₀ : ℕ, n₀ ∈ stageNext G r C Y i :=
        ⟨sInf (stageNext G r C X i), (hagree _ hXk).1 (Nat.sInf_mem hneX)⟩
      have hcastX : stageTime G r C X (i + 1)
          = ((sInf (stageNext G r C X i) : ℕ) : ℕ∞) := by
        rw [stageTime_succ]
        exact sInf_cast_eq_cast _ hneX.choose hneX.choose_spec
      have hcastY : stageTime G r C Y (i + 1)
          = ((sInf (stageNext G r C Y i) : ℕ) : ℕ∞) := by
        rw [stageTime_succ]
        exact sInf_cast_eq_cast _ hneY.choose hneY.choose_spec
      -- the sInfs agree
      have hmemX : sInf (stageNext G r C X i) ∈ stageNext G r C X i :=
        Nat.sInf_mem hneX
      have hXY : sInf (stageNext G r C X i) ∈ stageNext G r C Y i :=
        (hagree _ hXk).1 hmemX
      have hleXY : sInf (stageNext G r C Y i) ≤ sInf (stageNext G r C X i) :=
        Nat.sInf_le hXY
      have hYk : sInf (stageNext G r C Y i) ≤ k := le_trans hleXY hXk
      have hmemY : sInf (stageNext G r C Y i) ∈ stageNext G r C Y i :=
        Nat.sInf_mem hneY
      have hYX : sInf (stageNext G r C Y i) ∈ stageNext G r C X i :=
        (hagree _ hYk).2 hmemY
      have heq : sInf (stageNext G r C X i) = sInf (stageNext G r C Y i) :=
        le_antisymm (Nat.sInf_le hYX) hleXY
      -- the times agree
      have hTnext : stageTime G r C X (i + 1) = stageTime G r C Y (i + 1) := by
        rw [hcastX, hcastY, heq]
      -- the centres agree
      have hcentre : X (stageTime G r C X (i + 1)).toNat
          = Y (stageTime G r C Y (i + 1)).toNat := by
        have htoNat : ∀ S : Set ℕ, (((sInf S : ℕ) : ℕ∞).toNat) = sInf S := fun S => by
          exact_mod_cast ENat.coe_toNat (ENat.coe_ne_top (sInf S))
        rw [hcastX, hcastY, htoNat, heq, htoNat]
        exact h _ hYk
      -- conclude
      have hgoal : stageE G r C X (i + 1)
          = (stageTime G r C X (i + 1),
             stageUsed G r C X i ∪ C (X (stageTime G r C X (i + 1)).toNat)) := rfl
      have hgoalY : stageE G r C Y (i + 1)
          = (stageTime G r C Y (i + 1),
             stageUsed G r C Y i ∪ C (Y (stageTime G r C Y (i + 1)).toNat)) := rfl
      rw [hgoal, hgoalY, hF, hTnext]
      have hcentre' : X (stageTime G r C Y (i + 1)).toNat
          = Y (stageTime G r C Y (i + 1)).toNat := by
        have := hcentre
        rw [hTnext] at this
        exact this
      rw [hcentre']

/-- **The stage time is a stopping time of the walk.** -/
theorem isWalkStoppingE_stageTime (r : ℕ) (C : V → Finset V) :
    ∀ i, LatticeProb.Graph.IsWalkStoppingE (fun X => stageTime G r C X i) := by
  intro i
  induction i with
  | zero =>
      intro k X Y hXY hk
      simpa only [stageTime, stageE] using hk
  | succ i ih =>
      intro k X Y hXY hk
      have hkX : stageTime G r C X (i + 1) = (k : ℕ∞) := hk
      have hi : stageTime G r C X i ≤ (k : ℕ∞) :=
        le_trans (stageTime_mono r C X i) hkX.le
      have hp : stageE G r C X i = stageE G r C Y i :=
        stageE_prefix r C hXY i hi
      have hT : stageTime G r C X i = stageTime G r C Y i := congrArg Prod.fst hp
      have hF : stageUsed G r C X i = stageUsed G r C Y i := congrArg Prod.snd hp
      have hagree : ∀ m : ℕ, m ≤ k →
          (m ∈ stageNext G r C X i ↔ m ∈ stageNext G r C Y i) := by
        intro m hm
        simp only [stageNext, Set.mem_setOf_eq, hT, hF]
        rw [hXY m hm]
      have hneX : ∃ n₀ : ℕ, n₀ ∈ stageNext G r C X i := by
        have h1 := hkX
        rw [stageTime_succ] at h1
        exact exists_mem_of_sInf_cast_le
          (fun n => stageTime G r C X i ≤ (n : ℕ∞)
            ∧ Admissible G r (stageUsed G r C X i) (X n)) (by rw [← h1])
      have hXk : sInf (stageNext G r C X i) ≤ k := by
        have h1 := hkX
        rw [stageTime_succ,
          sInf_cast_eq_cast (fun n => stageTime G r C X i ≤ (n : ℕ∞)
            ∧ Admissible G r (stageUsed G r C X i) (X n)) hneX.choose hneX.choose_spec] at h1
        exact Nat.cast_le.1 (by rw [show sInf (stageNext G r C X i)
            = sInf {n : ℕ | stageTime G r C X i ≤ (n : ℕ∞)
              ∧ Admissible G r (stageUsed G r C X i) (X n)} from rfl, h1])
      have hneY : ∃ n₀ : ℕ, n₀ ∈ stageNext G r C Y i :=
        ⟨sInf (stageNext G r C X i), (hagree _ hXk).1 (Nat.sInf_mem hneX)⟩
      have hcastX : stageTime G r C X (i + 1)
          = ((sInf (stageNext G r C X i) : ℕ) : ℕ∞) := by
        rw [stageTime_succ]
        exact sInf_cast_eq_cast _ hneX.choose hneX.choose_spec
      have hcastY : stageTime G r C Y (i + 1)
          = ((sInf (stageNext G r C Y i) : ℕ) : ℕ∞) := by
        rw [stageTime_succ]
        exact sInf_cast_eq_cast _ hneY.choose hneY.choose_spec
      have hmemX : sInf (stageNext G r C X i) ∈ stageNext G r C X i :=
        Nat.sInf_mem hneX
      have hXYm : sInf (stageNext G r C X i) ∈ stageNext G r C Y i :=
        (hagree _ hXk).1 hmemX
      have hleXY : sInf (stageNext G r C Y i) ≤ sInf (stageNext G r C X i) :=
        Nat.sInf_le hXYm
      have hYk : sInf (stageNext G r C Y i) ≤ k := le_trans hleXY hXk
      have hmemY : sInf (stageNext G r C Y i) ∈ stageNext G r C Y i :=
        Nat.sInf_mem hneY
      have hYXm : sInf (stageNext G r C Y i) ∈ stageNext G r C X i :=
        (hagree _ hYk).2 hmemY
      have heq : sInf (stageNext G r C X i) = sInf (stageNext G r C Y i) :=
        le_antisymm (Nat.sInf_le hYXm) hleXY
      show stageTime G r C Y (i + 1) = (k : ℕ∞)
      rw [hcastY, ← heq, ← hcastX, hkX]

end RWRS.Support
