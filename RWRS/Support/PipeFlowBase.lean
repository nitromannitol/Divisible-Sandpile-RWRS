import RWRS.Support.PipeSub
import RWRS.Support.CombNode
import LatticeProb.Network.Flow

/-!
# The unit flow on the pipe tree

This module builds the ambient unit flow `pipeFlowAmb` on the tree of pipes underlying a
gadget: a current of size `B ^ (-n)` through every level-`n` pipe, directed away from the root
along the unique path back to it via `pipePred`. Restricting to `pipeSites` gives `pipeFlow`,
and `isFlow_pipeFlow` checks that it is a genuine flow, `LatticeProb.Network.IsFlow`, on the
pipe sub-network `pipeSub`: antisymmetric and supported on its edges.
-/

namespace RWRS.Support

open scoped Classical

variable {B : ℕ} {L : ℕ → ℕ}

/-- The step towards the root from the root itself is the root: `pipePred` fixes `pipeRoot`. -/
theorem pipePred_root : pipePred B L (pipeRoot B) = pipeRoot B := by
  simp [pipePred, pipeRoot]

/-- At most one of two distinct sites is the step towards the root from the
other. -/
theorem pipePred_not_both (hL : ∀ j, 1 ≤ j → 1 ≤ L j) {u v : List (Fin B) × ℕ}
    (hu : PipeValid B L u) (hv : PipeValid B L v) (hne : u ≠ v)
    (h1 : u = pipePred B L v) (h2 : v = pipePred B L u) : False := by
  by_cases hvr : v = pipeRoot B
  · rw [hvr, pipePred_root] at h1
    exact hne (h1.trans hvr.symm)
  · by_cases hur : u = pipeRoot B
    · rw [hur, pipePred_root] at h2
      exact hvr h2
    · have d1 := pipeDepth_pred_lt hL hv hvr
      have d2 := pipeDepth_pred_lt hL hu hur
      rw [← h1] at d1
      rw [← h2] at d2
      omega

/-- The unit flow on the tree of pipes: the current `B^{-n}` through every pipe
at level `n`, directed away from the root. -/
noncomputable def pipeFlowAmb (B : ℕ) (L : ℕ → ℕ) (u v : List (Fin B) × ℕ) : ℝ :=
  if u = v then 0
  else if u = pipePred B L v then ((B : ℝ) ^ (v.1.length))⁻¹
  else if v = pipePred B L u then -(((B : ℝ) ^ (u.1.length))⁻¹)
  else 0

/-- The unit flow read on the sites of the tree of pipes. -/
noncomputable def pipeFlow (B : ℕ) (L : ℕ → ℕ) (u v : pipeSites B L) : ℝ :=
  pipeFlowAmb B L (u : List (Fin B) × ℕ) (v : List (Fin B) × ℕ)

/-- The ambient unit flow through a site to itself is zero. -/
theorem pipeFlowAmb_self (u : List (Fin B) × ℕ) : pipeFlowAmb B L u u = 0 := by
  simp [pipeFlowAmb]

/-- Along the parent-edge `u = pipePred B L v`, the ambient unit flow from `u` to `v` is
`B ^ (-n)` for `n` the word length of `v`, the current directed away from the root. -/
theorem pipeFlowAmb_of_pred {u v : List (Fin B) × ℕ} (hne : u ≠ v)
    (h : u = pipePred B L v) :
    pipeFlowAmb B L u v = ((B : ℝ) ^ (v.1.length))⁻¹ := by
  rw [pipeFlowAmb, if_neg hne, if_pos h]

/-- Along the parent-edge `v = pipePred B L u`, the ambient unit flow from `u` to `v` is
`-B ^ (-n)` for `n` the word length of `u`; `pipePred_not_both` rules out both predecessor
relations holding at once, which is where `hL` is used. -/
theorem pipeFlowAmb_of_pred' (hL : ∀ j, 1 ≤ j → 1 ≤ L j) {u v : List (Fin B) × ℕ}
    (hu : PipeValid B L u) (hv : PipeValid B L v) (hne : u ≠ v)
    (h : v = pipePred B L u) :
    pipeFlowAmb B L u v = -(((B : ℝ) ^ (u.1.length))⁻¹) := by
  rw [pipeFlowAmb, if_neg hne, if_neg ?_, if_pos h]
  intro hc
  exact pipePred_not_both hL hu hv hne hc h

/-- When neither site is the pipe-predecessor of the other, the ambient unit flow between them
vanishes. -/
theorem pipeFlowAmb_of_neither {u v : List (Fin B) × ℕ}
    (h1 : u ≠ pipePred B L v) (h2 : v ≠ pipePred B L u) :
    pipeFlowAmb B L u v = 0 := by
  simp only [pipeFlowAmb, if_neg h1, if_neg h2, ite_self]

/-- The unit flow `pipeFlow` on `pipeSites`, read off `pipeFlowAmb_of_pred`, from a site `u` to
a site `v` whose pipe-predecessor is `u`. -/
theorem pipeFlow_of_pred {u v : pipeSites B L} (hne : u ≠ v)
    (h : (u : List (Fin B) × ℕ) = pipePred B L (v : List (Fin B) × ℕ)) :
    pipeFlow B L u v = ((B : ℝ) ^ ((v : List (Fin B) × ℕ).1.length))⁻¹ :=
  pipeFlowAmb_of_pred (fun hc => hne (Subtype.ext hc)) h

/-- The unit flow `pipeFlow` on `pipeSites` in the reverse direction, read off
`pipeFlowAmb_of_pred'`. -/
theorem pipeFlow_of_pred' (hL : ∀ j, 1 ≤ j → 1 ≤ L j) {u v : pipeSites B L} (hne : u ≠ v)
    (h : (v : List (Fin B) × ℕ) = pipePred B L (u : List (Fin B) × ℕ)) :
    pipeFlow B L u v = -(((B : ℝ) ^ ((u : List (Fin B) × ℕ).1.length))⁻¹) :=
  pipeFlowAmb_of_pred' hL u.2 v.2 (fun hc => hne (Subtype.ext hc)) h

/-- The unit flow `pipeFlow` vanishes between two sites of `pipeSites` neither of which is the
other's pipe-predecessor. -/
theorem pipeFlow_of_neither {u v : pipeSites B L}
    (h1 : (u : List (Fin B) × ℕ) ≠ pipePred B L (v : List (Fin B) × ℕ))
    (h2 : (v : List (Fin B) × ℕ) ≠ pipePred B L (u : List (Fin B) × ℕ)) :
    pipeFlow B L u v = 0 :=
  pipeFlowAmb_of_neither h1 h2


/-- **The unit flow is a genuine flow.**  `pipeFlow` is antisymmetric and supported on the edges
of `pipeSub`, checked case by case with the predecessor lemmas above. -/
theorem isFlow_pipeFlow (hL : ∀ j, 1 ≤ j → 1 ≤ L j) :
    LatticeProb.Network.IsFlow (pipeSub B L) (pipeFlow B L) := by
  constructor
  · intro u v
    by_cases huv : u = v
    · subst huv; simp [pipeFlow, pipeFlowAmb_self]
    · have hvu : v ≠ u := fun h => huv h.symm
      by_cases h1 : (u : List (Fin B) × ℕ) = pipePred B L (v : List (Fin B) × ℕ)
      · rw [pipeFlow_of_pred huv h1, pipeFlow_of_pred' hL hvu h1]
      · by_cases h2 : (v : List (Fin B) × ℕ) = pipePred B L (u : List (Fin B) × ℕ)
        · rw [pipeFlow_of_pred' hL huv h2, pipeFlow_of_pred hvu h2, neg_neg]
        · rw [pipeFlow_of_neither h1 h2, pipeFlow_of_neither h2 h1, neg_zero]
  · intro u v hadj
    by_cases huv : u = v
    · subst huv; simp [pipeFlow, pipeFlowAmb_self]
    · refine pipeFlow_of_neither ?_ ?_ <;> intro hc <;> apply hadj
      · exact ⟨Or.inl u.2, Or.inl v.2, fun h => huv (Subtype.ext h), Or.inr hc⟩
      · exact ⟨Or.inl u.2, Or.inl v.2, fun h => huv (Subtype.ext h), Or.inl hc⟩

end RWRS.Support
