/-
Two facts about divergent series in `[0,∞]`, used in Steps 4 and 6 of
`lem:moment-sharpness`.

Capping the terms of a divergent series of finite terms at one keeps it
divergent: either infinitely many terms are at least one, and then the capped
series has infinitely many terms equal to one, or only finitely many are, and
then the cap changes only finitely many terms.  Both cases are one inequality,
`a ≤ min a 1 + 1_{a ≥ 1} a`, and the finiteness of the exceptional set is
Markov's inequality for series.

The same inequality gives the second fact: a divergent lower bound valid from
some index on still forces divergence.
-/
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped ENNReal

namespace RWRS.Support

/-- **Capping at one keeps a divergent series divergent.** -/
theorem tsum_min_one_eq_top {a : ℕ → ℝ≥0∞} (hfin : ∀ t, a t ≠ ⊤) (h : ∑' t, a t = ⊤) :
    ∑' t, min (a t) 1 = ⊤ := by
  classical
  by_contra hb
  have hS : {t : ℕ | (1 : ℝ≥0∞) ≤ min (a t) 1}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hb one_ne_zero
  set S := {t : ℕ | (1 : ℝ≥0∞) ≤ min (a t) 1} with hSdef
  have hpt : ∀ t, a t ≤ min (a t) 1 + (if t ∈ S then a t else 0) := by
    intro t
    by_cases ht : t ∈ S
    · simp only [ht, if_pos]
      exact le_add_self
    · have hlt : ¬ ((1 : ℝ≥0∞) ≤ min (a t) 1) := by simpa [hSdef] using ht
      have hmin : min (a t) 1 = a t := by
        rcases min_cases (a t) (1 : ℝ≥0∞) with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1
        · exact absurd (le_of_eq h1.symm) hlt
      simp only [ht, if_neg, not_false_iff, add_zero, hmin]
      exact le_refl _
  have hle : (∑' t, a t) ≤ (∑' t, min (a t) 1) + ∑' t, (if t ∈ S then a t else 0) := by
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hpt
  have hfin2 : (∑' t : ℕ, (if t ∈ S then a t else 0)) ≠ ⊤ := by
    have hsupp : ∀ t ∉ hS.toFinset, (if t ∈ S then a t else 0) = 0 := by
      intro t ht
      rw [Set.Finite.mem_toFinset] at ht
      simp [ht]
    rw [tsum_eq_sum hsupp]
    refine ENNReal.sum_ne_top.2 (fun t _ => ?_)
    by_cases hx : t ∈ S
    · simpa [hx] using hfin t
    · simp [hx]
  rw [h] at hle
  exact (ENNReal.add_ne_top.2 ⟨hb, hfin2⟩) (top_le_iff.1 hle)

/-- **An eventual lower bound inherits the divergence.** -/
theorem tsum_eq_top_of_eventually_le {f g : ℕ → ℝ≥0∞} (T : ℕ) (hg : ∀ t, g t ≠ ⊤)
    (h : ∀ t, T ≤ t → g t ≤ f t) (htop : ∑' t, g t = ⊤) : ∑' t, f t = ⊤ := by
  classical
  by_contra hb
  have hpt : ∀ t, g t ≤ f t + (if t < T then g t else 0) := by
    intro t
    by_cases ht : t < T
    · simp only [ht, if_pos]
      exact le_add_self
    · simp only [ht, if_neg, not_false_iff, add_zero]
      exact h t (Nat.le_of_not_lt ht)
  have hle : (∑' t, g t) ≤ (∑' t, f t) + ∑' t, (if t < T then g t else 0) := by
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hpt
  have hfin2 : (∑' t : ℕ, (if t < T then g t else 0)) ≠ ⊤ := by
    have hsupp : ∀ t ∉ Finset.range T, (if t < T then g t else 0) = 0 := by
      intro t ht
      rw [Finset.mem_range] at ht
      simp [ht]
    rw [tsum_eq_sum hsupp]
    refine ENNReal.sum_ne_top.2 (fun t _ => ?_)
    by_cases hx : t < T
    · simpa [hx] using hg t
    · simp [hx]
  rw [htop] at hle
  exact (ENNReal.add_ne_top.2 ⟨hb, hfin2⟩) (top_le_iff.1 hle)

end RWRS.Support
