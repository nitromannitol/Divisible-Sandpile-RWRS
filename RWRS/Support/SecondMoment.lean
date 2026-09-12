/-
The second-moment step of `lem:moment-sharpness`.

The counting variable of the good sites is a sum of indicators, so it is
integer-valued; if it is at least half its mean and its mean is positive, then it
is not zero and hence at least one.  Paley--Zygmund at `θ = 1/2` therefore bounds
the probability that some good site occurs, and the elementary inequality
`min(s,1)/2 ≤ s/(1+s)` turns the resulting ratio into the paper's
`c min(|B| p, 1)`.
-/
import RWRS.Support.PaleyZygmund
import RWRS.Support.MomentIneq

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `min(s,1)/2 ≤ s/(1+s)` for nonnegative `s`. -/
theorem div_one_add_ge_half_min {s : ℝ} (hs : 0 ≤ s) :
    min s 1 / 2 ≤ s / (1 + s) := by
  have hpos : (0 : ℝ) < 1 + s := by linarith
  rcases le_or_gt s 1 with h | h
  · rw [min_eq_left h]
    field_simp
    nlinarith
  · rw [min_eq_right h.le]
    field_simp
    nlinarith

omit [MeasurableSpace Ω] in
/-- An integer-valued variable at least half a positive mean is at least one. -/
theorem subset_one_le_of_pos_mean (Z : Ω → ℝ)
    (hint : ∀ ω, ∃ k : ℕ, Z ω = (k : ℝ)) {m : ℝ} (hm : 0 < m) :
    {ω | m / 2 ≤ Z ω} ⊆ {ω | 1 ≤ Z ω} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  obtain ⟨k, hk⟩ := hint ω
  rw [hk] at hω ⊢
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hω
    linarith
  have : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  exact_mod_cast this

end RWRS.Support
