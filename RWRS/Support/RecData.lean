/-
Everything `sec:recurrent-nonstab` fixes before it builds the graph: the base
`B`, the exponent `α = 1/(d_f-1)`, the exponent `ρ = δ/(2(d_f+1))` of the
attachment points, the constant `C_comb` of `prop:comb-estimates` and the
constant `c_loc` of `cor:rec-loc`, and the depths and attachment points of the
gadgets with the three conditions the section imposes on them.
-/
import RWRS.Support.RayVolume
import RWRS.Support.GrowthExponent
import RWRS.Frozen.RecLocal
import RWRS.Frozen.CombEstimates

namespace RWRS.Support

open Filter

/-- **All the data of `sec:recurrent-nonstab`**: the base `B`, the exponent
`α = 1/(d_f-1)`, the exponent `ρ` of the attachment points, the constant
`c_loc` of `cor:rec-loc`, and the depths and attachment points of the gadgets,
with the three conditions `eq:rec-cond-sep`, `eq:rec-cond-vol` and
`eq:rec-cond-div`. -/
theorem exists_rec_data {d_f : ℝ} (hd2 : 2 < d_f) (hd3 : d_f < 3) :
    ∃ (B : ℕ) (α ρ c_loc C_comb : ℝ) (m s : ℕ → ℕ),
      RWRS.CombCond B α ∧ d_f = 1 + 1 / α ∧ 0 < ρ ∧ 0 < c_loc ∧ 0 < C_comb ∧
      ρ < Real.log (RWRS.combLambda B α) / (α * Real.log B) / (d_f + 1) ∧
      StrictMono m ∧ StrictMono s ∧
      (∀ k, s k = ⌈(RWRS.gadgetRadius (RWRS.combLen B α) (m k) : ℝ) ^ ρ⌉₊) ∧
      (∀ k, s k + RWRS.gadgetRadius (RWRS.combLen B α) (m k) < s (k + 1)) ∧
      (∀ k, (∑ j ∈ Finset.range (k + 1),
          (RWRS.gadgetSize B (RWRS.combLen B α) (m j) : ℝ)) ≤ (s (k + 1) : ℝ) ^ d_f) ∧
      (∀ k, ((s (k + 1) : ℝ) + 1) ^ (d_f + 1) * (((k + 1 : ℕ) : ℝ))
        ≤ c_loc * (RWRS.gadgetRadius (RWRS.combLen B α) (m (k + 1)) : ℝ)
            ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B))) ∧
      (∀ (e : Bool) (n : ℕ) (ω : List (Fin B)), ω.length = n → 1 ≤ n →
        ∀ (Y : List (Fin B) × ℕ → ℝ) (b : ℝ), 0 ≤ b → (∀ v, 1 ≤ Y v) →
          ∀ v ∈ RWRS.combFirstHalf B (RWRS.combLen B α) n ω,
            (2 + 2 * b * (C_comb + 1)) * (RWRS.combLen B α n : ℝ) ≤ Y v →
            c_loc * (RWRS.gadgetRadius (RWRS.combLen B α) n : ℝ)
                ^ (Real.log (RWRS.combLambda B α) / (α * Real.log B))
              ≤ ∑' u : ↥(RWRS.combSet B (RWRS.combLen B α) n ω),
                  RWRS.combVoltage B (RWRS.combLen B α) e n ω u * (Y u - b)) ∧
      (∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
        ∀ (a : List (Fin B) × ℕ → ℝ) (b' : ℝ), 0 ≤ b' →
          (∀ u ∈ RWRS.combSet B (RWRS.combLen B α) n w, -b' ≤ a u) →
          ∀ v ∈ RWRS.combFirstHalf B (RWRS.combLen B α) n w,
            (2 + 2 * b' * (C_comb + 1)) * (RWRS.combLen B α n : ℝ) - b' ≤ a v →
            RWRS.combI B (RWRS.combLen B α) e n w n * (RWRS.combLen B α n : ℝ) ^ 2
              ≤ ∑' u : ↥(RWRS.combSet B (RWRS.combLen B α) n w),
                  RWRS.combVoltage B (RWRS.combLen B α) e n w u * a u) := by
  obtain ⟨B, α, hc, hαdef, hdf⟩ := exists_rec_base hd2 hd3
  obtain ⟨-, -, ⟨C_comb, hCpos, hmass, hspike⟩, -⟩ := RWRS.Frozen.combEstimates B α hc
  obtain ⟨c_loc, hcloc, hloc⟩ := RWRS.Frozen.recLocal B α hc C_comb hCpos hmass
  set δ : ℝ := Real.log (RWRS.combLambda B α) / (α * Real.log B) with hδ
  have hδpos : 0 < δ := rec_delta_pos hc
  have hdfpos : (0 : ℝ) < d_f := by linarith
  set ρ : ℝ := δ / (2 * (d_f + 1)) with hρdef
  have hd1 : (0 : ℝ) < d_f + 1 := by linarith
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hhalf : ρ * (d_f + 1) = δ / 2 := by
    rw [hρdef]
    field_simp
  have hρδ : ρ * (d_f + 1) < δ := by rw [hhalf]; linarith
  have hρlt : ρ < δ / (d_f + 1) := by
    rw [lt_div_iff₀ hd1]
    exact hρδ
  refine ⟨B, α, ρ, c_loc, C_comb,
    mSeq hc hdfpos hρpos hcloc hρδ, sSeq hc hdfpos hρpos hcloc hρδ,
    hc, hdf, hρpos, hcloc, hCpos, hρlt,
    mSeq_strictMono hc hdfpos hρpos hcloc hρδ, sSeq_strictMono hc hdfpos hρpos hcloc hρδ,
    fun k => rfl, sSeq_sep hc hdfpos hρpos hcloc hρδ, sSeq_vol hc hdfpos hρpos hcloc hρδ,
    sSeq_div hc hdfpos hρpos hcloc hρδ, hloc, hspike⟩

/-- The balls of the ray with the gadgets are finite. -/
theorem finite_closedBall_rayGraph {B : ℕ} {L m s : ℕ → ℕ} (hsm : StrictMono s) (R : ℕ) :
    (RWRS.closedBall (rayGraph B L m s) (rayPt B L m 0) R).Finite :=
  @finite_closedBall _ (rayGraph B L m s) (rayLocallyFinite hsm) (rayPt B L m 0) R

end RWRS.Support
