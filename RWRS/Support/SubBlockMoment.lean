/-
The geometric decay in the scale of the block moments, for `prop:subcritical`.

`rwrs.tex:1211`: "Since `q < (p-1)θ`, the geometric decay dominates `poly(k)`".
The two tails of `eq:Mk-tail-Ak` integrate to `poly(k) 2^{k(q-(p-1)(θ-η))}` and
`poly(k) 2^{k(1+q-n(θ-δ))}`, and both exponents are negative for `η` small and
`n` large.
-/
import RWRS.Support.SubGeom

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- Two polynomial-times-geometric terms combine into one. -/
theorem two_geom_le {N1 N2 e1 e2 C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (N : ℕ) (hN1 : N1 ≤ (N : ℝ)) (hN2 : N2 ≤ (N : ℝ))
    (e : ℝ) (he1 : e1 ≤ e) (he2 : e2 ≤ e) (k : ℕ) :
    C1 * ((k : ℝ) + 1) ^ N1 * (2:ℝ) ^ ((k : ℝ) * e1)
        + C2 * ((k : ℝ) + 1) ^ N2 * (2:ℝ) ^ ((k : ℝ) * e2)
      ≤ (C1 + C2) * ((k : ℝ) + 1) ^ N * ((2:ℝ) ^ e) ^ k := by
  have hk1 : (1:ℝ) ≤ (k : ℝ) + 1 := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hk0 : (0:ℝ) < (k : ℝ) + 1 := by linarith
  have hkN : ((k : ℝ) + 1) ^ (N : ℝ) = ((k : ℝ) + 1) ^ N := Real.rpow_natCast _ N
  have h2e : (2:ℝ) ^ ((k : ℝ) * e) = ((2:ℝ) ^ e) ^ k := by
    rw [← Real.rpow_natCast ((2:ℝ) ^ e) k, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hstep : ∀ {M f : ℝ}, M ≤ (N : ℝ) → f ≤ e → ∀ C : ℝ, 0 ≤ C →
      C * ((k : ℝ) + 1) ^ M * (2:ℝ) ^ ((k : ℝ) * f)
        ≤ C * ((k : ℝ) + 1) ^ N * ((2:ℝ) ^ e) ^ k := by
    intro M f hM hf C hC
    have h1 : ((k : ℝ) + 1) ^ M ≤ ((k : ℝ) + 1) ^ N := by
      rw [← hkN]
      exact Real.rpow_le_rpow_of_exponent_le hk1 hM
    have h2 : (2:ℝ) ^ ((k : ℝ) * f) ≤ ((2:ℝ) ^ e) ^ k := by
      rw [← h2e]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have h4 : (0:ℝ) < (2:ℝ) ^ ((k : ℝ) * f) := Real.rpow_pos_of_pos (by norm_num) _
    calc C * ((k : ℝ) + 1) ^ M * (2:ℝ) ^ ((k : ℝ) * f)
        ≤ C * ((k : ℝ) + 1) ^ N * (2:ℝ) ^ ((k : ℝ) * f) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC) h4.le
      _ ≤ C * ((k : ℝ) + 1) ^ N * ((2:ℝ) ^ e) ^ k :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hA := hstep hN1 he1 C1 hC1
  have hB := hstep hN2 he2 C2 hC2
  have hdist : (C1 + C2) * ((k : ℝ) + 1) ^ N * ((2:ℝ) ^ e) ^ k
      = C1 * ((k : ℝ) + 1) ^ N * ((2:ℝ) ^ e) ^ k
        + C2 * ((k : ℝ) + 1) ^ N * ((2:ℝ) ^ e) ^ k := by ring
  rw [hdist]
  exact add_le_add hA hB

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

/-- **The `q`-th moments of the block variables on the good-walk event decay
geometrically in the scale.** -/
theorem exists_block_moment_bound [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (hG : G.Connected)
    [IsProbabilityMeasure ν] {p c Cp d_s A q η δ : ℝ} (nn : ℕ)
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
    (hdeg : ∀ v : V, 1 ≤ G.degree v)
    (hds : 0 < d_s) (hsp : RWRS.SpectralDimensionBound G d_s A)
    (m : ℝ) (hint : Integrable (fun z : ℝ => z) ν) (hm : ∫ z, z ∂ν = m)
    (hsq : Integrable (fun z : ℝ => (z - m) ^ 2) ν)
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤) (hc : 0 < c) (hCp : 0 ≤ Cp)
    {d : ℕ} (hd : 0 < d) (hmneg : m < 0)
    (hq : 0 < q) (hqp : q < p) (hq2 : q < ((2 * nn : ℕ) : ℝ)) (hη : 0 < η)
    (he1 : 1 + (max (1 - d_s / 2) 0 + η) * (p - 1) + q - p < 0)
    (he2 : 1 + (nn : ℝ) + (max (1 - d_s / 2) 0 + δ) * nn + q - ((2 * nn : ℕ) : ℝ) < 0) :
    ∃ (C r : ℝ) (N : ℕ), 0 < C ∧ 0 < r ∧ r < 1 ∧ ∀ (x : V) (k : ℕ),
      (∫⁻ z in {z : (V → ℝ) × (ℕ → V) |
            z.2 ∈ RWRS.goodWalk (V := V) (max (1 - d_s / 2) 0) δ k},
          ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q) ∂(RWRS.jointLaw G ν x))
        ≤ ENNReal.ofReal (C * ((k : ℝ) + 1) ^ N * r ^ k) := by
  classical
  obtain ⟨C1, hC1, hC1le⟩ := polyBlockConst_le (Cp := Cp) hCp ν (m := m) (A := A) hp hds hη
  obtain ⟨C2, hC2, hC2le⟩ := gaussBlockConst_le hc nn ν m
    (α := max (1 - d_s / 2) 0) (δ := δ)
  have hmpos : (0:ℝ) < |m| := abs_pos.2 (ne_of_lt hmneg)
  have hdpos : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have ha0 : (0:ℝ) < |m| / (d : ℝ) := by positivity
  set e1 : ℝ := 1 + (max (1 - d_s / 2) 0 + η) * (p - 1) + q - p with he1def
  set e2 : ℝ := 1 + (nn : ℝ) + (max (1 - d_s / 2) 0 + δ) * nn + q - ((2 * nn : ℕ) : ℝ)
    with he2def
  set D1 : ℝ := q * C1 * (|m| / (d : ℝ)) ^ (q - p) * (1 / q + 1 / (p - q)) with hD1def
  set D2 : ℝ := q * C2 * (|m| / (d : ℝ)) ^ (q - ((2 * nn : ℕ) : ℝ))
    * (1 / q + 1 / (((2 * nn : ℕ) : ℝ) - q)) with hD2def
  have hD1 : 0 ≤ D1 := by
    have h1 : (0:ℝ) < (|m| / (d : ℝ)) ^ (q - p) := Real.rpow_pos_of_pos ha0 _
    have h2 : (0:ℝ) < 1 / q + 1 / (p - q) := by
      have : (0:ℝ) < p - q := by linarith
      positivity
    rw [hD1def]; positivity
  have hD2 : 0 ≤ D2 := by
    have h1 : (0:ℝ) < (|m| / (d : ℝ)) ^ (q - ((2 * nn : ℕ) : ℝ)) := Real.rpow_pos_of_pos ha0 _
    have h2 : (0:ℝ) < 1 / q + 1 / (((2 * nn : ℕ) : ℝ) - q) := by
      have : (0:ℝ) < ((2 * nn : ℕ) : ℝ) - q := by linarith
      positivity
    rw [hD2def]; positivity
  set e : ℝ := max e1 e2 with hedef
  have hepos : e < 0 := max_lt he1 he2
  set N : ℕ := max ⌈p + 1⌉₊ (2 * nn + 1) with hNdef
  refine ⟨D1 + D2 + 1, (2:ℝ) ^ e, N, by linarith, Real.rpow_pos_of_pos (by norm_num) _, ?_,
    fun x k => ?_⟩
  · have : (2:ℝ) ^ e < (2:ℝ) ^ (0:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hepos
    rwa [Real.rpow_zero] at this
  · have hmain := lintegral_good_dyadicY_rpow_le (G := G) hG nn hFN hdeg hds hsp m hint hm hsq
      hp hmom hc hCp (α := max (1 - d_s / 2) 0) (δ := δ) (k := k) hd hmneg hq hqp hq2 x
    have hT1 : tailValue q (|m| / (d : ℝ) * 2 ^ k) (polyBlockConst Cp ν m p A d_s k) p
        ≤ D1 * ((k : ℝ) + 1) ^ (p + 1) * (2:ℝ) ^ ((k : ℝ) * e1) := by
      have := tailValue_le (q := q) (a0 := |m| / (d : ℝ)) (s := p) hq ha0 hqp
        (K := polyBlockConst Cp ν m p A d_s k) (C := C1) (N := p + 1)
        (e := 1 + (max (1 - d_s / 2) 0 + η) * (p - 1)) k (hC1le k)
      simpa [hD1def, he1def, add_sub_assoc] using this
    have hT2 : tailValue q (|m| / (d : ℝ) * 2 ^ k) (gaussBlockConst c nn ν m
          (max (1 - d_s / 2) 0) δ k) (((2 * nn : ℕ)) : ℝ)
        ≤ D2 * ((k : ℝ) + 1) ^ (((2 * nn + 1 : ℕ)) : ℝ) * (2:ℝ) ^ ((k : ℝ) * e2) := by
      have := tailValue_le (q := q) (a0 := |m| / (d : ℝ)) (s := ((2 * nn : ℕ) : ℝ)) hq ha0 hq2
        (K := gaussBlockConst c nn ν m (max (1 - d_s / 2) 0) δ k) (C := C2)
        (N := ((2 * nn + 1 : ℕ) : ℝ))
        (e := 1 + (nn : ℝ) + (max (1 - d_s / 2) 0 + δ) * nn) k (hC2le k)
      simpa [hD2def, he2def, add_sub_assoc] using this
    have hcomb := two_geom_le hD1 hD2 N
      (N1 := p + 1) (N2 := ((2 * nn + 1 : ℕ) : ℝ))
      (by
        have h1 : p + 1 ≤ (⌈p + 1⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈p + 1⌉₊ : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast Nat.le_max_left ⌈p + 1⌉₊ (2 * nn + 1)
        linarith)
      (by exact_mod_cast Nat.le_max_right ⌈p + 1⌉₊ (2 * nn + 1))
      e (le_max_left _ _) (le_max_right _ _) k
    refine le_trans hmain ?_
    refine le_trans (add_le_add (ENNReal.ofReal_le_ofReal hT1) (ENNReal.ofReal_le_ofReal hT2)) ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal (le_trans hcomb ?_)
    have h5 : (0:ℝ) ≤ ((k : ℝ) + 1) ^ N := by positivity
    have h6 : (0:ℝ) < ((2:ℝ) ^ e) ^ k := by positivity
    nlinarith [h5, h6]


end RWRS.Support
