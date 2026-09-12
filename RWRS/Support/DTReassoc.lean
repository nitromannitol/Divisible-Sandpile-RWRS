import Mathlib

namespace RWRS.Support

variable {Ω : Type*} (A : ℕ → Set Ω)

/-- **Re-association of the first-hit event.**  For `j < i`, the event
`{J = i} = A i ∩ ⋂_{l < i} (A l)ᶜ` can be written as
`(A j)ᶜ ∩ (A i ∩ ⋂_{l < i, l ≠ j} (A l)ᶜ)`, the form
`integral_sum_block_le` needs (the `A j`-block read by the second factor,
the rest by the first). -/
theorem reassoc_firstHit (i j : ℕ) (hj : j < i) :
    A i ∩ ⋂ l ∈ Finset.range i, (A l)ᶜ
      = (A j)ᶜ ∩ (A i ∩ ⋂ l ∈ (Finset.range i).erase j, (A l)ᶜ) := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iInter, Finset.mem_range,
    Finset.mem_erase]
  constructor
  · rintro ⟨hAi, hl⟩
    refine ⟨fun hAj => absurd hAj (hl j (by omega)), hAi, fun l _ => hl l (by omega)⟩
  · rintro ⟨hAj, hAi, hl⟩
    refine ⟨hAi, fun l hl' => ?_⟩
    by_cases h : l = j
    · subst h; exact hAj
    · exact hl l ⟨h, hl'⟩

end RWRS.Support
