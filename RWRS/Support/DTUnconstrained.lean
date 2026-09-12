import RWRS.Support.DTAdmissible
import RWRS.Support.DTTrapFamily
import RWRS.Support.DTExitAux
import LatticeProb.Graph.MarkovAE
import LatticeProb.Graph.ExitTime

open LatticeProb RWRS RWRS.Support

open MeasureTheory
open scoped ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

open scoped Classical in
/-- One step of the unconstrained stage recursion: from the pair
`(T_i, F_i)` of the current stage time and the used sites, the next time is the
first entry into the sites admissible for `F_i` strictly after `T_i` (`⊤` if
none), and the used sites gain the block of the site reached. -/
noncomputable def uncStageStep (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (p : ℕ∞ × Finset V) : ℕ∞ × Finset V :=
  if p.1 = ⊤ then (⊤, p.2)
  else if h : ∃ m : ℕ, p.1.toNat < m ∧ Admissible G r p.2 (X m) then
    (Nat.find h, p.2 ∪ C (X (Nat.find h)))
  else (⊤, p.2)

open scoped Classical in
/-- The unconstrained stage state: `(T_i, F_i)`, the `i`-th stage time and the
trap sites used up to it. -/
noncomputable def uncStageState (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) : ℕ → ℕ∞ × Finset V
  | 0 => (0, C (X 0))
  | i + 1 => uncStageStep G r C X (uncStageState G r C X i)

open scoped Classical in
/-- The unconstrained stage times. -/
noncomputable def uncTime (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ) : ℕ∞ :=
  (uncStageState G r C X i).1

open scoped Classical in
/-- The sites used by the unconstrained stages up to `i`. -/
noncomputable def uncUsed (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ) : Finset V :=
  (uncStageState G r C X i).2

end RWRS.Support

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

open scoped Classical in
theorem uncTime_succ_of_ex (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ)
    (hne : (uncStageState G r C X i).1 ≠ ⊤)
    (h : ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
      Admissible G r (uncStageState G r C X i).2 (X m)) :
    uncTime G r C X (i + 1) = Nat.find h ∧
    uncUsed G r C X (i + 1) =
      (uncStageState G r C X i).2 ∪ C (X (Nat.find h)) := by
  simp only [uncTime, uncUsed, uncStageState, uncStageStep, if_neg hne, dif_pos h]
  trivial



open scoped Classical in
theorem uncTime_succ_of_nex (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ)
    (h : ¬ ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
      Admissible G r (uncStageState G r C X i).2 (X m)) :
    uncTime G r C X (i + 1) = ⊤ ∧
    uncUsed G r C X (i + 1) = (uncStageState G r C X i).2 := by
  simp only [uncTime, uncUsed, uncStageState, uncStageStep]
  split <;> simp



open scoped Classical in
theorem uncTime_lt (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ)
    (hfin : (uncStageState G r C X i).1 ≠ ⊤) :
    (uncStageState G r C X i).1 < uncTime G r C X (i + 1) := by
  by_cases hex : ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
      Admissible G r (uncStageState G r C X i).2 (X m)
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [← hn] at hex
    simp only [uncTime, uncStageState, uncStageStep]
    rw [← hn]
    simp only [dif_pos hex]
    exact ENat.coe_lt_coe.mpr (Nat.find_spec hex).1
  · simp only [uncTime, uncStageState, uncStageStep]
    split
    · exact absurd (by assumption) hfin
    · exact lt_of_le_of_ne le_top hfin

/-- **Once a stage fails, the stage state freezes.**  If the `i`-th stage time
is `⊤`, then so is every later stage time, and the used set stops growing. -/
theorem uncTime_top_frozen (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) :
    ∀ i : ℕ, (uncTime G r C X i) = ⊤ →
      ∀ j, i ≤ j → uncStageState G r C X j = uncStageState G r C X i := by
  intro i hi j hj
  induction hj with
  | refl => rfl
  | @step j hj ih =>
    show uncStageStep G r C X (uncStageState G r C X j) = uncStageState G r C X i
    rw [ih]
    simp only [uncStageStep]
    rw [if_pos (show (uncStageState G r C X i).1 = ⊤ from hi)]
    have heta : (uncStageState G r C X i)
        = ((uncStageState G r C X i).1, (uncStageState G r C X i).2) := Prod.mk.eta
    rw [heta, show ((uncStageState G r C X i).1 : ℕ∞) = ⊤ from hi]


open scoped Classical in
/-- If two existence predicates agree below and at `k`, and `k` is the least
witness of the first, then it is also the least witness of the second. -/
theorem least_witness_transport {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] (k : ℕ)
    (hex : ∃ m, p m) (hex' : ∃ m, q m)
    (hagree : ∀ m ≤ Nat.find hex, p m ↔ q m)
    (hfind : Nat.find hex = k) : Nat.find hex' = k := by
  have hp : p k := hfind ▸ Nat.find_spec hex
  have h1 : Nat.find hex' ≤ k :=
    Nat.find_le ((hagree k (le_of_eq hfind.symm)).mp hp)
  have h2 : k ≤ Nat.find hex' := Nat.le_of_not_lt
    fun hlt => Nat.lt_irrefl k
      (by calc k = Nat.find hex := hfind.symm
        _ ≤ Nat.find hex' :=
          Nat.find_le ((hagree _ (hlt.le.trans_eq hfind.symm)).mpr (Nat.find_spec hex'))
        _ < k := hlt)
  exact Nat.le_antisymm h1 h2

open scoped Classical in
/-- **Stage-state determination.**  If two trajectories agree up to time `k`
and the `i`-th stage time of `X` is the finite value `s`, then the stage
states agree. -/
theorem uncStageState_det (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) :
    ∀ (i : ℕ) (X Y : ℕ → V) (s : ℕ∞) (_hag : ∀ j : ℕ, (j : ℕ∞) ≤ s → X j = Y j),
      (uncTime G r C X i) = s →
      uncStageState G r C X i = uncStageState G r C Y i := by
  intro i X Y s
  induction i generalizing X Y s with
  | zero =>
    intro hag hs
    have hs0 : s = 0 := by
      have h0 : (uncTime G r C X 0) = 0 := rfl
      rw [h0] at hs; exact hs.symm
    subst hs0
    simp only [uncStageState]
    rw [hag 0 (by norm_num)]
  | succ i ih =>
    intro hag hs
    by_cases hstop : s = ⊤
    · -- full agreement: X = Y
      have hXY : X = Y := funext fun j => hag j (by simp [hstop])
      rw [hXY]
    · -- s is finite: the step existence holds for X
      have hstate : uncStageState G r C X (i + 1)
          = uncStageStep G r C X (uncStageState G r C X i) := rfl
      by_cases htop : (uncStageState G r C X i).1 = ⊤
      · have : uncTime G r C X (i + 1) = ⊤ := by
          simp only [uncTime, uncStageState, uncStageStep, if_pos htop]
        rw [this] at hs; exact absurd hs.symm hstop
      · by_cases hex : ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
          Admissible G r (uncStageState G r C X i).2 (X m)
        · rw [(uncTime_succ_of_ex G r C X i htop hex).1] at hs
          have hs' : s = ↑(Nat.find hex) := hs.symm
          -- the stage state at i is determined
          have hs0 : uncTime G r C X (i + 1) = s := by
            rw [← hs]; exact (uncTime_succ_of_ex G r C X i htop hex).1
          have hlt := uncTime_lt G r C X i htop
          rw [hs0] at hlt
          have hstate := ih X Y (uncStageState G r C X i).1
            (fun j hj => hag j (le_trans hj (le_of_lt hlt)))
            (show (uncTime G r C X i) = _ from rfl)
          have hXYm : X (Nat.find hex) = Y (Nat.find hex) :=
            hag (Nat.find hex) (by rw [hs'])
          -- transport the existence to Y
          have hex' : ∃ m : ℕ, (uncStageState G r C Y i).1.toNat < m ∧
              Admissible G r (uncStageState G r C Y i).2 (Y m) := by
            rw [← hstate]
            refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_⟩
            rw [← hXYm]
            exact (Nat.find_spec hex).2
          have htop' : (uncStageState G r C Y i).1 ≠ ⊤ := by
            rw [← hstate]; exact htop
          -- the least witnesses agree
          have hagree : ∀ m ≤ Nat.find hex,
              (uncStageState G r C X i).1.toNat < m ∧
                Admissible G r (uncStageState G r C X i).2 (X m) ↔
              (uncStageState G r C X i).1.toNat < m ∧
                Admissible G r (uncStageState G r C X i).2 (Y m) := by
            intro m hm
            constructor
            · intro h
              exact ⟨h.1, by rw [← hag m (by rw [hs']; exact Nat.cast_le.mpr hm)]; exact h.2⟩
            · intro h
              exact ⟨h.1, by rw [hag m (by rw [hs']; exact Nat.cast_le.mpr hm)]; exact h.2⟩
          rw [← hstate] at hex'
          have hfind : Nat.find hex' = Nat.find hex :=
            least_witness_transport _ hex hex' hagree rfl
          -- both steps now agree
          simp only [uncStageState, uncStageStep, ← hstate]
          rw [if_neg htop, if_neg htop, dif_pos hex, dif_pos hex', hfind]
          exact Prod.ext rfl (by rw [hXYm])
        · have : uncTime G r C X (i + 1) = ⊤ := by
            rw [(uncTime_succ_of_nex G r C X i hex).1]
          rw [this] at hs; exact absurd hs.symm hstop

/-- **The unconstrained stage times are stopping times.** -/
theorem uncTime_isStopping (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (i : ℕ) :
    LatticeProb.Graph.IsWalkStoppingE (fun Y => uncTime G r C Y i) := by
  intro k X Y hag hX
  have hstate : uncStageState G r C X i = uncStageState G r C Y i :=
    uncStageState_det G r C i X Y (k : ℕ∞)
      (fun j hj => hag j (by exact_mod_cast hj))
      (show uncTime G r C X i = (k : ℕ∞) from hX)
  show (uncStageState G r C Y i).1 = (k : ℕ∞)
  rw [← hstate]
  exact hX

open scoped Classical in
/-- **If a stage time is finite, the existence predicate held at the previous
stage.** -/
theorem uncStage_ex_of_succ_ne_top (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ)
    (hfin : uncTime G r C X (i + 1) ≠ ⊤) :
    ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
      Admissible G r (uncStageState G r C X i).2 (X m) := by
  by_contra hex
  obtain ⟨h1, _⟩ := uncTime_succ_of_nex G r C X i hex
  exact hfin h1

open scoped Classical in
/-- **The used set grows.** -/
theorem uncUsed_mono (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (X : ℕ → V) (i : ℕ) :
    uncUsed G r C X i ⊆ uncUsed G r C X (i + 1) := by
  simp only [uncUsed, uncStageState, uncStageStep]
  split
  · exact le_rfl
  · split
    · intro v hv
      exact Finset.mem_union_left _ hv
    · exact le_rfl

open scoped Classical in
/-- **The starting site is always used.** -/
theorem uncStart_mem_used (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (hC : ∀ y : V, y ∈ C y) (X : ℕ → V) :
    ∀ i : ℕ, X 0 ∈ uncUsed G r C X i := by
  intro i
  induction i with
  | zero =>
    show X 0 ∈ C (X 0)
    exact hC (X 0)
  | succ i ih => exact uncUsed_mono G r C X i ih

open scoped Classical in
/-- **The stage centre lies in its own trap block, which is part of the used
set.** -/
theorem uncCentre_mem_used (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (hC : ∀ y : V, y ∈ C y) (X : ℕ → V) :
    ∀ i : ℕ, X ((uncTime G r C X i).toNat) ∈ uncUsed G r C X i := by
  intro i
  induction i with
  | zero =>
    show X ((0 : ℕ∞).toNat) ∈ C (X 0)
    simp only [ENat.toNat_zero]
    exact hC (X 0)
  | succ i ih =>
    by_cases htop : uncTime G r C X i = ⊤
    · have hfrozen : uncStageState G r C X (i + 1) = uncStageState G r C X i :=
        uncTime_top_frozen G r C X i htop (i + 1) (Nat.le_succ i)
      have h1 : (uncTime G r C X (i + 1)).toNat = 0 := by
        show (uncStageState G r C X (i + 1)).1.toNat = 0
        rw [hfrozen]
        have htop' : (uncStageState G r C X i).1 = ⊤ := htop
        rw [htop']
        simp
      rw [h1, uncUsed, hfrozen]
      exact uncStart_mem_used G r C hC X i
    · by_cases hex : ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
        Admissible G r (uncStageState G r C X i).2 (X m)
      · obtain ⟨h1, h2⟩ := uncTime_succ_of_ex G r C X i htop hex
        rw [h1, h2]
        exact Finset.mem_union_right _ (hC _)
      · obtain ⟨h1, h2⟩ := uncTime_succ_of_nex G r C X i hex
        rw [h1]
        show X 0 ∈ uncUsed G r C X (i + 1)
        rw [h2]
        exact uncStart_mem_used G r C hC X i


open scoped Classical in
/-- **The stage centre is not admissible for the used set.**  The centre lies
in its own trap block, which is part of the used set, and its distance to
itself is `0 ≤ 2r`. -/
theorem uncCentre_not_admissible (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (hC : ∀ y : V, y ∈ C y) (X : ℕ → V) (i : ℕ) :
    ¬ Admissible G r (uncUsed G r C X i) (X ((uncTime G r C X i).toNat)) := by
  intro hadm
  exact absurd (hadm.1 _ (uncCentre_mem_used G r C hC X i)
    (by simp [SimpleGraph.edist_self])) (by simp)

open scoped Classical in
/-- **The stage increment is bounded by the exit time of the non-admissible
set.**  On the event that the `i`-th stage time is finite and a further
admissible site is reached, the next stage time is at most the current stage
time plus the exit time of the non-admissible set for the used set `F_i`,
computed along the trajectory restarted at the stage centre. -/
theorem uncTime_succ_le_exit (G : SimpleGraph V) [G.LocallyFinite] (r : ℕ)
    (C : V → Finset V) (hC : ∀ y : V, y ∈ C y) (X : ℕ → V) (i : ℕ)
    (hfin : (uncStageState G r C X i).1 ≠ ⊤)
    (hex : ∃ m : ℕ, (uncStageState G r C X i).1.toNat < m ∧
      Admissible G r (uncStageState G r C X i).2 (X m)) :
    uncTime G r C X (i + 1) ≤
      (uncStageState G r C X i).1 +
        exitTime {z : V | ¬ Admissible G r (uncStageState G r C X i).2 z}
          (LatticeProb.Graph.shiftPath (uncStageState G r C X i).1.toNat X) := by
  obtain ⟨h1, _⟩ := uncTime_succ_of_ex G r C X i hfin hex
  rw [h1]
  by_cases htop : exitTime {z : V | ¬ Admissible G r (uncStageState G r C X i).2 z}
      (LatticeProb.Graph.shiftPath (uncStageState G r C X i).1.toNat X) = ⊤
  · rw [htop]
    simp
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    have hout0 : (LatticeProb.Graph.shiftPath (uncStageState G r C X i).1.toNat X)
        ((exitTime {z : V | ¬ Admissible G r (uncStageState G r C X i).2 z}
          (LatticeProb.Graph.shiftPath (uncStageState G r C X i).1.toNat X)).toNat)
        ∉ {z : V | ¬ Admissible G r (uncStageState G r C X i).2 z} :=
      exitTime_notMem_at _ _ htop
    have hout : (LatticeProb.Graph.shiftPath (uncStageState G r C X i).1.toNat X) n
        ∉ {z : V | ¬ Admissible G r (uncStageState G r C X i).2 z} := by
      have htn : (exitTime {z : V | ¬ Admissible G r (uncStageState G r C X i).2 z}
          (LatticeProb.Graph.shiftPath (uncStageState G r C X i).1.toNat X)).toNat = n := by
        rw [← hn, ENat.toNat_coe]
      rw [htn] at hout0
      exact hout0
    have hn0 : 0 < n := by
      by_contra h0
      have hne : n = 0 := by omega
      subst hne
      exact hout (by
        show X ((uncStageState G r C X i).1.toNat)
          ∈ {z : V | ¬ Admissible G r (uncStageState G r C X i).2 z}
        exact uncCentre_not_admissible G r C hC X i)
    have hwit1 : (uncStageState G r C X i).1.toNat <
        ((uncStageState G r C X i).1.toNat + n) := by omega
    have hwit2 : Admissible G r (uncStageState G r C X i).2
          (X ((uncStageState G r C X i).1.toNat + n)) := by
      have := hout
      simp only [LatticeProb.Graph.shiftPath, Set.mem_setOf_eq, not_not] at this
      simpa using this
    have hexw : (uncStageState G r C X i).1.toNat <
        ((uncStageState G r C X i).1.toNat + n) ∧
        Admissible G r (uncStageState G r C X i).2
          (X ((uncStageState G r C X i).1.toNat + n)) := ⟨hwit1, hwit2⟩
    have hfind : Nat.find hex ≤ (uncStageState G r C X i).1.toNat + n :=
      Nat.find_le hexw
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfin
    have htt : (uncStageState G r C X i).1.toNat = t := by
      rw [← ht, ENat.toNat_coe]
    have hfind : Nat.find hex ≤ t + n := htt ▸ Nat.find_le hexw
    have hA : ((t + n : ℕ) : ℕ∞) = (uncStageState G r C X i).1 + (n : ℕ∞) := by
      rw [← ht]
      push_cast
      ring
    have hstep : ((Nat.find hex : ℕ) : ℕ∞) ≤ ((t + n : ℕ) : ℕ∞) := by
      exact_mod_cast hfind
    refine le_trans hstep ?_
    rw [← hn]
    exact hA.le

end RWRS.Support
