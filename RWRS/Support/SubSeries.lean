/-
Summation over the scales, for `prop:subcritical`.

`rwrs.tex:1210`: "Combining with `E_x[Y_k^q 1_{A_k^c}] = O(2^{-3k})`" and
"`∑_k E_x[Y_k^q] < ∞`".  Both contributions are polynomials in the scale against
geometric factors, so the series converges, and `lem:dyadic` turns it into a
bound on the moment of the running supremum, uniform in the starting vertex.
-/
import RWRS.Support.SubBlockMoment
import RWRS.Frozen.Dyadic
import RWRS.Frozen.GoodWalk

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- A polynomial against a geometric factor is summable, so the series of the
block bounds is finite. -/
theorem tsum_ofReal_poly_geom_ne_top {C : ℝ} (hC : 0 ≤ C) (N : ℕ) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) :
    (∑' k : ℕ, ENNReal.ofReal (C * ((k : ℝ) + 1) ^ N * r ^ k)) ≠ ⊤ := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0.le]
    exact hr
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ N * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one N hnorm
  have h2 : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ N * r ^ (k + 1)) := by
    have h := (summable_nat_add_iff 1).2 h1
    refine h.congr fun k => ?_
    push_cast
    ring
  have h3 : Summable (fun k : ℕ => C * ((k : ℝ) + 1) ^ N * r ^ k) := by
    have h := h2.mul_left (C * r⁻¹)
    refine h.congr fun k => ?_
    field_simp
    ring
  have hnn : ∀ k : ℕ, 0 ≤ C * ((k : ℝ) + 1) ^ N * r ^ k := by
    intro k
    have h1 : (0:ℝ) ≤ ((k : ℝ) + 1) ^ N := by positivity
    have h2 : (0:ℝ) ≤ r ^ k := by positivity
    positivity
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn h3]
  exact ENNReal.ofReal_ne_top

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

/-- **The `q`-th moment of the running supremum is bounded uniformly in the
starting vertex**, for a scenery of finite `p`-th absolute moment and negative
real mean. -/
theorem exists_supPayoff_moment_bound [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (hG : G.Connected)
    [IsProbabilityMeasure ν] {p c Cp d_s A q η δ : ℝ} (nn : ℕ) (d : ℕ)
    (hFN : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), ProbabilityTheory.iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp B : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          0 < B → B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P →
          (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / B ^ 2)))
    (hbd : RWRS.BoundedDegree G d) (hdeg : ∀ v : V, 1 ≤ G.degree v) (hd : 0 < d)
    (hds : 0 < d_s) (hsp : RWRS.SpectralDimensionBound G d_s A)
    (m : ℝ) (hmext : RWRS.extMean ν = (m : EReal)) (hmneg : m < 0)
    (hint : Integrable (fun z : ℝ => z) ν) (hm : ∫ z, z ∂ν = m)
    (hsq : Integrable (fun z : ℝ => (z - m) ^ 2) ν)
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤) (hc : 0 < c) (hCp : 0 ≤ Cp)
    (hq1 : 1 ≤ q) (hqp : q < p) (hq2 : q < ((2 * nn : ℕ) : ℝ)) (hη : 0 < η)
    (hδ0 : 0 < δ) (hδ1 : δ < min (d_s / 2) 1)
    (he1 : 1 + (max (1 - d_s / 2) 0 + η) * (p - 1) + q - p < 0)
    (he2 : 1 + (nn : ℝ) + (max (1 - d_s / 2) 0 + δ) * nn + q - ((2 * nn : ℕ) : ℝ) < 0) :
    ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ x : V,
      (∫⁻ z, RWRS.supPayoff G z.1 z.2 ^ q ∂(RWRS.jointLaw G ν x)) ≤ B := by
  classical
  have hq : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  obtain ⟨C, r, N, hC, hr0, hr1, hgood⟩ := exists_block_moment_bound (G := G) hG nn hFN hdeg
    hds hsp m hint hm hsq hp hmom hc hCp hd hmneg hq hqp hq2 hη he1 he2
  obtain ⟨C', hC', hcompl⟩ :=
    (RWRS.Frozen.goodWalkBounds hG d hbd d_s A hds hsp ν inferInstance m hmext hmneg p hp hmom
      (max (1 - d_s / 2) 0) δ rfl hδ0 hδ1).2.2 q hq1 hqp
  set S : ℕ → Set (ℕ → V) := fun k => RWRS.goodWalk (V := V) (max (1 - d_s / 2) 0) δ k with hSdef
  have hmS : ∀ k, MeasurableSet {z : (V → ℝ) × (ℕ → V) | z.2 ∈ S k} :=
    fun k => measurable_snd (measurableSet_goodWalk _ _ k)
  have hkey : ∀ (x : V) (k : ℕ),
      (∫⁻ z, ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q) ∂(RWRS.jointLaw G ν x))
        ≤ ENNReal.ofReal (C * ((k : ℝ) + 1) ^ N * r ^ k)
          + ENNReal.ofReal (C' * ((k : ℝ) + 1) ^ (0 : ℕ) * ((2:ℝ) ^ (-(3:ℝ))) ^ k) := by
    intro x k
    rw [← MeasureTheory.lintegral_add_compl _ (hmS k)]
    refine add_le_add (hgood x k) ?_
    have heq : ∀ z : (V → ℝ) × (ℕ → V),
        Set.indicator (RWRS.goodWalk (V := V) (max (1 - d_s / 2) 0) δ k)ᶜ
            (fun X => ENNReal.ofReal (RWRS.dyadicY G z.1 m d k X ^ q)) z.2
          = Set.indicator {z : (V → ℝ) × (ℕ → V) | z.2 ∈ S k}ᶜ
              (fun z => ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q)) z := by
      intro z
      by_cases h : z.2 ∈ (RWRS.goodWalk (V := V) (max (1 - d_s / 2) 0) δ k)ᶜ
      · have h' : z ∈ {z : (V → ℝ) × (ℕ → V) | z.2 ∈ S k}ᶜ := h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      · have h' : z ∉ {z : (V → ℝ) × (ℕ → V) | z.2 ∈ S k}ᶜ := h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    have hcc := hcompl x k
    rw [lintegral_congr heq, lintegral_indicator (hmS k).compl] at hcc
    refine le_trans hcc (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    have hpow : ((2:ℝ) ^ (-(3:ℝ))) ^ k = (2:ℝ) ^ (-(3:ℝ) * k) := by
      rw [← Real.rpow_natCast ((2:ℝ) ^ (-(3:ℝ))) k, ← Real.rpow_mul (by norm_num)]
    rw [hpow, pow_zero, mul_one]
  refine ⟨(∑' k : ℕ, ENNReal.ofReal (C * ((k : ℝ) + 1) ^ N * r ^ k))
      + ∑' k : ℕ, ENNReal.ofReal (C' * ((k : ℝ) + 1) ^ (0 : ℕ) * ((2:ℝ) ^ (-(3:ℝ))) ^ k),
    ENNReal.add_ne_top.2 ⟨tsum_ofReal_poly_geom_ne_top hC.le N hr0 hr1,
      tsum_ofReal_poly_geom_ne_top hC'.le 0 (Real.rpow_pos_of_pos (by norm_num) _) ?_⟩,
    fun x => ?_⟩
  · have h := Real.rpow_lt_rpow_of_exponent_lt (x := (2:ℝ)) (by norm_num)
      (show (-(3:ℝ)) < 0 by norm_num)
    rwa [Real.rpow_zero] at h
  · refine le_trans (RWRS.Frozen.dyadic hG d hbd ν inferInstance m hmext hmneg p hp hmom q hq1 x) ?_
    rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum (fun k => hkey x k)


end RWRS.Support
