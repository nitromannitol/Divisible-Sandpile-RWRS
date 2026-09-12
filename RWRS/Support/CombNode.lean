/-
The node law at the branching vertices of the tree of pipes.

A branching vertex `(u,0)` with `u ≠ []` has `B + 1` neighbours: the last
interior site `(u, L_{|u|}-1)` of the pipe joining it to its parent, and the
first interior site `(u ++ [c], 1)` of each of its `B` child pipes.  The root
`([],0)` has the `B` first interior sites `([c],1)` of its child pipes and, when
the flag `e` is on, the extra boundary vertex `([],1)`.  Reading the Laplacian
there is what turns `eq:gC-PDE` into Kirchhoff's node law.

Throughout, `2 ≤ L j` for every `j ≥ 1`, which under `eq:comb-B-cond` holds for
`L_j = ⌊B^{αj}⌋` because `B^α ≥ 4`.
-/
import RWRS.Support.PipeNbr

namespace RWRS.Support

variable {B : ℕ} {L : ℕ → ℕ}

/-! ### The step towards the root from a child -/

theorem pipePred_child (c : Fin B) (u : List (Fin B)) :
    pipePred B L (u ++ [c], 1) = (u, 0) := by
  simp [pipePred]

theorem pipeValid_child (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (c : Fin B) (u : List (Fin B)) :
    PipeValid B L (u ++ [c], 1) := by
  have hlen : 1 ≤ (u ++ [c]).length := by simp
  have := hL2 (u ++ [c]).length hlen
  refine Or.inr ⟨by simp, le_rfl, ?_⟩
  show (1 : ℕ) ≤ L (u ++ [c]).length - 1
  omega

theorem pipeValid_pred_branch (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) {u : List (Fin B)} (hu : u ≠ []) :
    PipeValid B L (u, L u.length - 1) := by
  have hlen : 1 ≤ u.length := List.length_pos_iff.2 hu
  have := hL2 u.length hlen
  exact Or.inr ⟨hu, by omega, le_rfl⟩

theorem pipePred_branch (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) {u : List (Fin B)} (hu : u ≠ []) :
    pipePred B L (u, 0) = (u, L u.length - 1) := by
  have hlen : 1 ≤ u.length := List.length_pos_iff.2 hu
  have h2 : 2 ≤ L u.length := hL2 u.length hlen
  simp [pipePred, hu, h2]

/-! ### The neighbours of a branching vertex -/

theorem neighborSet_branch (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    {u : List (Fin B)} (hu : u ≠ []) :
    (pipeGraph B L e).neighborSet ((u : List (Fin B)), 0)
      = {v | v = (u, L u.length - 1) ∨ ∃ c : Fin B, v = (u ++ [c], 1)} := by
  have hlen : 1 ≤ u.length := List.length_pos_iff.2 hu
  have h2 : 2 ≤ L u.length := hL2 u.length hlen
  ext v
  constructor
  · rintro ⟨-, hval2, hne, hcase⟩
    rcases hcase with h | h
    · exact Or.inl (by rw [h, pipePred_branch hL2 hu])
    · obtain ⟨w', i⟩ := v
      match i with
      | 0 =>
          by_cases hw : w' = []
          · subst hw
            rw [show pipePred B L (([] : List (Fin B)), 0) = ([], 0) by simp [pipePred]] at h
            exact absurd (by simpa using congrArg Prod.fst h : u = []) hu
          · have hlen' : 1 ≤ w'.length := List.length_pos_iff.2 hw
            have h2' : 2 ≤ L w'.length := hL2 w'.length hlen'
            rw [show pipePred B L ((w' : List (Fin B)), 0) = (w', L w'.length - 1) by
              simp [pipePred, hw, h2']] at h
            have hu' : w' = u := (congrArg Prod.fst h).symm
            subst hu'
            have := congrArg Prod.snd h
            simp only at this
            omega
      | j + 1 =>
          by_cases hj : j = 0
          · subst hj
            rw [show pipePred B L ((w' : List (Fin B)), 0 + 1) = (w'.dropLast, 0) by
              simp [pipePred]] at h
            have hd : w'.dropLast = u := (congrArg Prod.fst h).symm
            have hw : w' ≠ [] := by
              intro hnil; rw [hnil] at hd; exact hu hd.symm
            obtain ⟨l, c, rfl⟩ : ∃ l c, w' = l ++ [c] := by
              rcases List.eq_nil_or_concat w' with h' | ⟨l, c, h'⟩
              · exact absurd h' hw
              · exact ⟨l, c, by simpa using h'⟩
            simp only [List.dropLast_concat] at hd
            subst hd
            exact Or.inr ⟨c, rfl⟩
          · rw [show pipePred B L ((w' : List (Fin B)), j + 1) = (w', j) by
              simp [pipePred, hj]] at h
            have := congrArg Prod.snd h
            simp only at this
            omega
  · intro hv
    rcases hv with h | ⟨c, h⟩
    · subst h
      refine ⟨Or.inl (Or.inl rfl), Or.inl (pipeValid_pred_branch hL2 hu), ?_,
        Or.inl (pipePred_branch hL2 hu).symm⟩
      intro hcontra
      have := congrArg Prod.snd hcontra
      simp only at this
      omega
    · subst h
      refine ⟨Or.inl (Or.inl rfl), Or.inl (pipeValid_child hL2 c u), ?_,
        Or.inr (pipePred_child c u).symm⟩
      intro hcontra
      exact absurd (congrArg Prod.snd hcontra) (by simp)

theorem neighborSet_root (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) :
    (pipeGraph B L e).neighborSet (([] : List (Fin B)), 0)
      = {v | (∃ c : Fin B, v = ([c], 1)) ∨ (e = true ∧ v = ([], 1))} := by
  have h2 : 2 ≤ L 1 := hL2 1 le_rfl
  ext v
  constructor
  · rintro ⟨-, hval2, hne, hcase⟩
    rcases hcase with h | h
    · rw [show pipePred B L (([] : List (Fin B)), 0) = ([], 0) by simp [pipePred]] at h
      exact absurd h.symm hne
    · obtain ⟨w', i⟩ := v
      match i with
      | 0 =>
          by_cases hw : w' = []
          · subst hw
            exact absurd rfl hne
          · have hlen' : 1 ≤ w'.length := List.length_pos_iff.2 hw
            have h2' : 2 ≤ L w'.length := hL2 w'.length hlen'
            rw [show pipePred B L ((w' : List (Fin B)), 0) = (w', L w'.length - 1) by
              simp [pipePred, hw, h2']] at h
            exact absurd (congrArg Prod.fst h).symm hw
      | j + 1 =>
          by_cases hj : j = 0
          · subst hj
            rw [show pipePred B L ((w' : List (Fin B)), 0 + 1) = (w'.dropLast, 0) by
              simp [pipePred]] at h
            have hd : w'.dropLast = [] := (congrArg Prod.fst h).symm
            have hlen : w'.length ≤ 1 := by
              have := congrArg List.length hd
              simp only [List.length_dropLast, List.length_nil] at this
              omega
            match w', hlen with
            | [], _ =>
                refine Or.inr ⟨?_, rfl⟩
                rcases hval2 with (h0 | ⟨hne', -, -⟩) | ⟨he, -⟩
                · exact absurd h0 (by simp)
                · exact absurd rfl hne'
                · exact he
            | [a], _ => exact Or.inl ⟨a, rfl⟩
            | (a :: b :: t), hlen => simp at hlen
          · rw [show pipePred B L ((w' : List (Fin B)), j + 1) = (w', j) by
              simp [pipePred, hj]] at h
            have := congrArg Prod.snd h
            simp only at this
            omega
  · intro hv
    rcases hv with ⟨c, h⟩ | ⟨he, h⟩
    · subst h
      have hval : PipeValid B L (([c] : List (Fin B)), 1) := by
        refine Or.inr ⟨by simp, le_rfl, ?_⟩
        simp only [List.length_singleton]
        omega
      refine ⟨Or.inl (Or.inl rfl), Or.inl hval, by simp, Or.inr ?_⟩
      have := pipePred_child (L := L) c ([] : List (Fin B))
      simpa using this.symm
    · subst h
      refine ⟨Or.inl (Or.inl rfl), Or.inr ⟨he, rfl⟩, by simp, Or.inr ?_⟩
      have := pipePred_child (L := L) (B := B)
      simp [pipePred]

/-! ### The Laplacian at a branching vertex -/

open scoped Classical in
theorem neighborFinset_branch (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    {u : List (Fin B)} (hu : u ≠ []) :
    (pipeGraph B L e).neighborFinset ((u : List (Fin B)), 0)
      = insert ((u : List (Fin B)), L u.length - 1)
          ((Finset.univ : Finset (Fin B)).image fun c => ((u ++ [c] : List (Fin B)), 1)) := by
  classical
  ext v
  rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_neighborSet,
    neighborSet_branch hL2 e hu]
  simp [Finset.mem_insert, Finset.mem_image, eq_comm]

theorem branch_not_mem_image {u : List (Fin B)} :
    ((u : List (Fin B)), L u.length - 1)
      ∉ (Finset.univ : Finset (Fin B)).image fun c => ((u ++ [c] : List (Fin B)), 1) := by
  classical
  simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro c hc
  have := congrArg (fun p => p.1.length) hc
  simp at this

theorem child_injective (u : List (Fin B)) :
    Function.Injective fun c : Fin B => ((u ++ [c] : List (Fin B)), 1) := by
  intro c d h
  have : (u ++ [c] : List (Fin B)) = u ++ [d] := congrArg Prod.fst h
  simpa using this

/-- **The node law at a branching vertex.**  A branching vertex `(u,0)` other
than the root has `B + 1` neighbours: the last interior site of its parent pipe
and the first interior site of each child pipe. -/
theorem laplacian_branch (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    {u : List (Fin B)} (hu : u ≠ []) (f : List (Fin B) × ℕ → ℝ) :
    laplacian (pipeGraph B L e) f ((u : List (Fin B)), 0)
      = (f (u, L u.length - 1) - f (u, 0))
        + ∑ c : Fin B, (f ((u ++ [c] : List (Fin B)), 1) - f (u, 0)) := by
  classical
  rw [laplacian, neighborFinset_branch hL2 e hu,
    Finset.sum_insert branch_not_mem_image,
    Finset.sum_image (fun c _ d _ h => child_injective u h)]

open scoped Classical in
theorem neighborFinset_root (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool) :
    (pipeGraph B L e).neighborFinset (([] : List (Fin B)), 0)
      = ((Finset.univ : Finset (Fin B)).image fun c => (([c] : List (Fin B)), 1))
          ∪ (if e then {(([] : List (Fin B)), 1)} else ∅) := by
  classical
  ext v
  rw [SimpleGraph.mem_neighborFinset, ← SimpleGraph.mem_neighborSet,
    neighborSet_root hL2 e]
  cases e with
  | false => simp [Finset.mem_image, eq_comm]
  | true => simp [Finset.mem_image, eq_comm]; tauto

theorem root_child_injective :
    Function.Injective fun c : Fin B => (([c] : List (Fin B)), 1) := by
  intro c d h
  have : ([c] : List (Fin B)) = [d] := congrArg Prod.fst h
  simpa using this

/-- **The node law at the root.**  The root has the `B` first interior sites of
its child pipes as neighbours, together with the extra boundary vertex when the
flag `e` is on. -/
theorem laplacian_root (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (e : Bool)
    (f : List (Fin B) × ℕ → ℝ) :
    laplacian (pipeGraph B L e) f (([] : List (Fin B)), 0)
      = (∑ c : Fin B, (f (([c] : List (Fin B)), 1) - f ([], 0)))
        + (if e then f (([] : List (Fin B)), 1) - f ([], 0) else 0) := by
  classical
  have hdisj : Disjoint
      ((Finset.univ : Finset (Fin B)).image fun c => (([c] : List (Fin B)), 1))
      (if e then {(([] : List (Fin B)), 1)} else (∅ : Finset (List (Fin B) × ℕ))) := by
    cases e with
    | false => simp
    | true =>
        simp only [if_true, Finset.disjoint_singleton_right, Finset.mem_image,
          Finset.mem_univ, true_and, not_exists]
        intro c hc
        have := congrArg (fun p => p.1.length) hc
        simp at this
  rw [laplacian, neighborFinset_root hL2 e, Finset.sum_union hdisj,
    Finset.sum_image (fun c _ d _ h => root_child_injective h)]
  cases e with
  | false => simp
  | true => simp

end RWRS.Support
