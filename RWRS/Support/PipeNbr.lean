/-
The neighbours of a site of the tree of pipes.

The electrical estimates of `ssec:comb-estimates` are the node law read at each
kind of site, so what they need first is the neighbour set at each kind of site:
two neighbours at an interior site of a pipe, the step towards the root and the
step away from it.
-/
import RWRS.Support.Comb

namespace RWRS.Support

variable {B : ℕ} {L : ℕ → ℕ}

/-- The site one step further from the root along a pipe: the next interior site
if there is one, and otherwise the branching vertex at the far end. -/
def pipeUp (B : ℕ) (L : ℕ → ℕ) (v : List (Fin B) × ℕ) : List (Fin B) × ℕ :=
  if v.2 + 1 ≤ L v.1.length - 1 then (v.1, v.2 + 1) else (v.1, 0)

/-- At an interior site of a pipe, the sites one step further from the root are
exactly `pipeUp`. -/
theorem pred_eq_iff_of_interior (e : Bool) {w : List (Fin B)} {i : ℕ}
    (hw : w ≠ []) (hi : 1 ≤ i) (hiL : i ≤ L w.length - 1)
    {u : List (Fin B) × ℕ} (hu : PipeValidPlus B L e u) :
    pipePred B L u = (w, i) ↔ u = pipeUp B L (w, i) := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw
  have hL2 : 2 ≤ L w.length := by omega
  constructor
  · intro h
    obtain ⟨w', j⟩ := u
    match j with
    | 0 =>
        by_cases hw' : w' = []
        · rw [hw'] at h
          rw [show pipePred B L (([] : List (Fin B)), 0) = ([], 0) by simp [pipePred]] at h
          have := congrArg Prod.snd h
          simp only at this
          omega
        · by_cases hL2' : 2 ≤ L w'.length
          · rw [show pipePred B L ((w' : List (Fin B)), 0) = (w', L w'.length - 1) by
              simp [pipePred, hw', hL2']] at h
            have hw'w : w' = w := congrArg Prod.fst h
            have hiv : L w'.length - 1 = i := congrArg Prod.snd h
            subst hw'w
            have hnot : ¬ (i + 1 ≤ L w'.length - 1) := by omega
            simp [pipeUp, hnot]
          · rw [show pipePred B L ((w' : List (Fin B)), 0) = (w'.dropLast, 0) by
              simp [pipePred, hw', hL2']] at h
            have := congrArg Prod.snd h
            simp only at this
            omega
    | j + 1 =>
        by_cases hj : j = 0
        · subst hj
          rw [show pipePred B L ((w' : List (Fin B)), 0 + 1) = (w'.dropLast, 0) by
            simp [pipePred]] at h
          have := congrArg Prod.snd h
          simp only at this
          omega
        · have hpe : pipePred B L ((w' : List (Fin B)), j + 1) = (w', j) := by
            simp [pipePred, hj]
          rw [hpe] at h
          have hw'w : w' = w := congrArg Prod.fst h
          have hji : j = i := congrArg Prod.snd h
          have hval : j + 1 ≤ L w'.length - 1 := by
            rcases hu with (h0 | ⟨-, -, h2⟩) | ⟨-, hbad⟩
            · simp only at h0; omega
            · exact h2
            · exact absurd (congrArg Prod.snd hbad) (by simp [hj])
          subst hw'w
          subst hji
          simp only [pipeUp]
          rw [if_pos hval]
  · intro h
    subst h
    by_cases hup : i + 1 ≤ L w.length - 1
    · simp only [pipeUp, if_pos hup]
      have hne : ¬ (i = 0) := by omega
      simp [pipePred, hne]
    · simp only [pipeUp, if_neg hup]
      have hiv : i = L w.length - 1 := by omega
      simp [pipePred, hw, hL2, hiv]

theorem pipeValidPlus_pipeUp (e : Bool) {w : List (Fin B)} {i : ℕ}
    (hw : w ≠ []) (hi : 1 ≤ i) :
    PipeValidPlus B L e (pipeUp B L (w, i)) := by
  by_cases hup : i + 1 ≤ L w.length - 1
  · simp only [pipeUp, if_pos hup]
    exact Or.inl (Or.inr ⟨hw, by omega, hup⟩)
  · simp only [pipeUp, if_neg hup]
    exact Or.inl (Or.inl rfl)

theorem ne_pipeUp {w : List (Fin B)} {i : ℕ} (hi : 1 ≤ i) :
    ((w : List (Fin B)), i) ≠ pipeUp B L (w, i) := by
  by_cases hup : i + 1 ≤ L w.length - 1
  · simp only [pipeUp, if_pos hup]
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · simp only [pipeUp, if_neg hup]
    intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

/-- **An interior site of a pipe has exactly two neighbours**: the step towards
the root and the step away from it. -/
theorem neighborSet_interior (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    {w : List (Fin B)} {i : ℕ} (hw : w ≠ []) (hi : 1 ≤ i) (hiL : i ≤ L w.length - 1) :
    (pipeGraph B L e).neighborSet ((w : List (Fin B)), i)
      = {pipePred B L (w, i), pipeUp B L (w, i)} := by
  have hval : PipeValid B L ((w : List (Fin B)), i) := Or.inr ⟨hw, hi, hiL⟩
  have hne : ((w : List (Fin B)), i) ≠ pipeRoot B := by
    intro h
    have := congrArg Prod.snd h
    simp only [pipeRoot] at this
    omega
  ext u
  constructor
  · rintro ⟨-, hu, hne', hcase⟩
    rcases hcase with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.2
        ((pred_eq_iff_of_interior e hw hi hiL hu).1 h.symm))
  · intro hu
    rcases hu with h | h
    · subst h
      exact ⟨Or.inl hval, Or.inl (pipePred_valid hval),
        fun hcontra => pipePred_ne_self hL hval hne hcontra.symm, Or.inl rfl⟩
    · rw [Set.mem_singleton_iff] at h
      subst h
      refine ⟨Or.inl hval, pipeValidPlus_pipeUp e hw hi, ne_pipeUp hi, Or.inr ?_⟩
      exact ((pred_eq_iff_of_interior e hw hi hiL
        (pipeValidPlus_pipeUp e hw hi)).2 rfl).symm

theorem pipePred_ne_pipeUp {w : List (Fin B)} {i : ℕ} (hw : w ≠ []) (hi : 1 ≤ i) :
    pipePred B L ((w : List (Fin B)), i) ≠ pipeUp B L (w, i) := by
  have hlen : 1 ≤ w.length := List.length_pos_iff.2 hw
  have hdrop : w.dropLast ≠ w := by
    intro h
    have := congrArg List.length h
    rw [List.length_dropLast] at this
    omega
  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  subst hk
  by_cases hk0 : k = 0
  · subst hk0
    have hpe : pipePred B L ((w : List (Fin B)), 0 + 1) = (w.dropLast, 0) := by
      simp [pipePred]
    rw [hpe]
    by_cases hup : 0 + 1 + 1 ≤ L w.length - 1
    · simp only [pipeUp, if_pos hup]
      intro h
      exact absurd (congrArg Prod.snd h) (by simp)
    · simp only [pipeUp, if_neg hup]
      intro h
      exact hdrop (congrArg Prod.fst h)
  · have hpe : pipePred B L ((w : List (Fin B)), k + 1) = (w, k) := by
      simp [pipePred, hk0]
    rw [hpe]
    by_cases hup : k + 1 + 1 ≤ L w.length - 1
    · simp only [pipeUp, if_pos hup]
      intro h
      have := congrArg Prod.snd h
      simp only at this
      omega
    · simp only [pipeUp, if_neg hup]
      intro h
      have := congrArg Prod.snd h
      simp only at this
      omega

open scoped Classical in
theorem neighborFinset_interior (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    {w : List (Fin B)} {i : ℕ} (hw : w ≠ []) (hi : 1 ≤ i) (hiL : i ≤ L w.length - 1) :
    (pipeGraph B L e).neighborFinset ((w : List (Fin B)), i)
      = {pipePred B L (w, i), pipeUp B L (w, i)} := by
  classical
  have hset := neighborSet_interior hL e hw hi hiL
  ext u
  rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_neighborSet, hset]
  simp [Finset.mem_insert, Finset.mem_singleton]

/-- **The node law at an interior site of a pipe.**  With only two neighbours,
the Laplacian is the second difference along the pipe. -/
theorem laplacian_interior (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    {w : List (Fin B)} {i : ℕ} (hw : w ≠ []) (hi : 1 ≤ i) (hiL : i ≤ L w.length - 1)
    (f : List (Fin B) × ℕ → ℝ) :
    laplacian (pipeGraph B L e) f ((w : List (Fin B)), i)
      = (f (pipePred B L (w, i)) - f (w, i)) + (f (pipeUp B L (w, i)) - f (w, i)) := by
  classical
  rw [laplacian, neighborFinset_interior hL e hw hi hiL,
    Finset.sum_insert (by simpa using pipePred_ne_pipeUp hw hi), Finset.sum_singleton]

/-! ### The voltage is affine along a pipe -/

open scoped Classical in
/-- The comb as a `Finset`. -/
noncomputable def combFinset (B : ℕ) (L : ℕ → ℕ) (n : ℕ) (w : List (Fin B)) :
    Finset (List (Fin B) × ℕ) := (combSet_finite (B := B) (L := L) n w).toFinset

open scoped Classical in
theorem coe_combFinset (n : ℕ) (w : List (Fin B)) :
    ((combFinset B L n w : Finset (List (Fin B) × ℕ)) : Set (List (Fin B) × ℕ))
      = combSet B L n w := by
  rw [combFinset, Set.Finite.coe_toFinset]

theorem pipeRoot_mem_combSet {n : ℕ} (w : List (Fin B)) (hn : 1 ≤ n) :
    pipeRoot B ∈ combSet B L n w :=
  ⟨Or.inl rfl, by simp [pipeRoot], by simp [pipeRoot], Or.inr ⟨by simp [pipeRoot], by
    simp only [pipeRoot, List.length_nil]; omega⟩⟩

open scoped Classical in
/-- **The increments of the voltage along a pipe are equal.**  At an interior
site the node law is the second difference, and the killed Green function is
harmonic there, so the voltage is an arithmetic progression along each pipe. -/
theorem combVoltage_increment (hB : 1 ≤ B) (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (e : Bool)
    {n : ℕ} {w u : List (Fin B)} (hwn : w.length = n) (hn : 1 ≤ n)
    {i : ℕ} (hu : u ≠ []) (hi : 1 ≤ i) (hiL : i ≤ L u.length - 1)
    (hmem : ((u : List (Fin B)), i) ∈ combSet B L n w) :
    combVoltage B L e n w (pipeUp B L (u, i)) - combVoltage B L e n w (u, i)
      = combVoltage B L e n w (u, i) - combVoltage B L e n w (pipePred B L (u, i)) := by
  classical
  set C := combFinset B L n w with hC
  have hcoe : ((C : Finset (List (Fin B) × ℕ)) : Set (List (Fin B) × ℕ))
      = combSet B L n w := coe_combFinset n w
  have hesc : ∀ x : List (Fin B) × ℕ,
      ∃ (q : List (Fin B) × ℕ) (_ : (pipeGraph B L e).Walk x q), q ∉ (C : Set _) := by
    intro x
    obtain ⟨q, p, hq⟩ := escape_combSet hL e hwn x
    exact ⟨q, p, by rwa [hcoe]⟩
  have hesc' : ∀ x : List (Fin B) × ℕ,
      ∃ (q : List (Fin B) × ℕ) (_ : (pipeGraph B L e).Walk x q), q ∉ C := by
    intro x
    obtain ⟨q, p, hq⟩ := hesc x
    exact ⟨q, p, by simpa using hq⟩
  have hdeg : ∀ v ∈ C, 0 < (pipeGraph B L e).degree v := by
    intro v hv
    exact degree_pos_of_mem_combSet hB hL e (by rw [← hcoe]; exact_mod_cast hv)
  have ho : pipeRoot B ∈ C := by
    rw [← Finset.mem_coe, hcoe]; exact pipeRoot_mem_combSet w hn
  have hvC : ((u : List (Fin B)), i) ∈ C := by
    rw [← Finset.mem_coe, hcoe]; exact hmem
  have hvo : ((u : List (Fin B)), i) ≠ pipeRoot B := by
    intro h
    have := congrArg Prod.snd h
    simp only [pipeRoot] at this
    omega
  have hharm := harmonic_killedGreenReal_of_escape C hesc' hdeg ho hvC hvo
  rw [hcoe] at hharm
  rw [laplacian_interior hL e hu hi hiL] at hharm
  simp only [combVoltage]
  linarith

end RWRS.Support
