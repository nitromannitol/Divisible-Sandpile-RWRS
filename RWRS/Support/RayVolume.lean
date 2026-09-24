/-
The volume growth of the ray with the gadgets, and the parameters of
`sec:recurrent-nonstab`.

`prop:rec-growth` is proved for any graph satisfying the `RayGadget` predicate;
here it is read on the graph that satisfies it, and the base `B` and the
exponent `α = 1/(d_f-1)` the section fixes are produced.
-/
import RWRS.Support.GadgetSeq
import RWRS.Support.RayRecurrent
import RWRS.Frozen.RecVolumeGrowth

namespace RWRS.Support

open Filter

variable {B : ℕ} {α d_f ρ : ℝ} {m s : ℕ → ℕ}

/-- The volume growth of the ray with the gadgets, from `prop:rec-growth`. -/
theorem volumeGrowth_rayGraph (hc : RWRS.CombCond B α) (hdf : d_f = 1 + 1 / α) (hρ : 0 < ρ)
    (hρ' : ρ < Real.log (RWRS.combLambda B α) / (α * Real.log B) / (d_f + 1))
    (hsdef : ∀ k, s k = ⌈(RWRS.gadgetRadius (RWRS.combLen B α) (m k) : ℝ) ^ ρ⌉₊)
    (hsep : ∀ k, s k + RWRS.gadgetRadius (RWRS.combLen B α) (m k) < s (k + 1))
    (hvol : ∀ k, (∑ j ∈ Finset.range (k + 1),
        (RWRS.gadgetSize B (RWRS.combLen B α) (m j) : ℝ)) ≤ (s (k + 1) : ℝ) ^ d_f) :
    (∃ C_G : ℝ, 0 < C_G ∧ ∀ r : ℕ, 1 ≤ r →
      (RWRS.closedBall (rayGraph B (RWRS.combLen B α) m s)
          (rayPt B (RWRS.combLen B α) m 0) r).encard
        ≤ ENNReal.ofReal (C_G * (r : ℝ) ^ d_f)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      ENNReal.ofReal (c * ((s k + RWRS.gadgetRadius (RWRS.combLen B α) (m k) : ℕ) : ℝ) ^ d_f)
        ≤ (RWRS.closedBall (rayGraph B (RWRS.combLen B α) m s)
            (rayPt B (RWRS.combLen B α) m 0)
            (s k + RWRS.gadgetRadius (RWRS.combLen B α) (m k))).encard) := by
  refine RWRS.Frozen.recVolumeGrowth B α d_f ρ hc hdf hρ hρ' m s hsdef ?_ ?_
    (rayGraph B (RWRS.combLen B α) m s) (rayPt B (RWRS.combLen B α) m 0)
    (rayPt B (RWRS.combLen B α) m) (rayEmb B (RWRS.combLen B α) m s) rayGadget_rayGraph
  · intro k hk
    have := hsep (k - 1)
    rw [show k - 1 + 1 = k by omega] at this
    exact this
  · intro k hk
    have := hvol (k - 1)
    rw [show k - 1 + 1 = k by omega] at this
    exact this

/-! ### The parameters of the recurrent counterexample -/

/-- `sec:recurrent-nonstab` takes `α = 1/(d_f-1)`, which lies in `(1/2,1)`
exactly when `d_f` lies in `(2,3)`, and then a base `B` large enough for
`eq:comb-B-cond`. -/
theorem exists_rec_base {d : ℝ} (hd2 : 2 < d) (hd3 : d < 3) :
    ∃ (B : ℕ) (α : ℝ), RWRS.CombCond B α ∧ α = 1 / (d - 1) ∧ d = 1 + 1 / α := by
  have hpos : (0 : ℝ) < d - 1 := by linarith
  set α : ℝ := 1 / (d - 1) with hα
  have hα1 : 1 / 2 < α := by
    rw [hα, lt_div_iff₀ hpos]
    linarith
  have hα2 : α < 1 := by
    rw [hα, div_lt_one hpos]
    linarith
  obtain ⟨B, hc⟩ := exists_combCond hα1 hα2
  refine ⟨B, α, hc, rfl, ?_⟩
  rw [hα, one_div_one_div]
  ring

/-- The exponent `δ = log λ /(α log B)` of `cor:rec-loc` is positive. -/
theorem rec_delta_pos (hc : RWRS.CombCond B α) :
    0 < Real.log (RWRS.combLambda B α) / (α * Real.log B) := by
  have hB : (2 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hc.1
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos (by linarith)
  have hα : (0 : ℝ) < α := by have := hc.2.1; linarith
  have hlam : 1 < RWRS.combLambda B α := hc.2.2.2.2.2.2
  exact div_pos (Real.log_pos hlam) (by positivity)

end RWRS.Support
