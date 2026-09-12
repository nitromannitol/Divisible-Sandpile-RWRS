/-
`eq:w-tail` of `prop:subcritical` on the good-walk event.

`rwrs.tex:1186`: the tail of an increment is the sum of a polynomial term of
order `p` and a Gaussian term whose variance is controlled on `A_k`.  The
Gaussian term is turned into a polynomial tail of order `2n`, `n` at the
disposal of the chaining, which is all the later tail integration uses; the
exponent `2n` is chosen at the end large enough that the term is summable in
the scale.
-/
import RWRS.Support.SubGauss
import RWRS.Support.SubVar

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

/-- The constant of the Gaussian remainder once it is written as a polynomial
tail of order `2n`. -/
noncomputable def gaussCoef (c : ℝ) (n : ℕ) (ν : Measure ℝ) (m : ℝ) : ℝ :=
  2 * (Nat.factorial n : ℝ) * ((∫ z, (z - m) ^ 2 ∂ν + 1) / c) ^ n

theorem gaussCoef_nonneg {c : ℝ} (hc : 0 < c) (n : ℕ) (ν : Measure ℝ) (m : ℝ) :
    0 ≤ gaussCoef c n ν m := by
  have h : (0:ℝ) ≤ ∫ z, (z - m) ^ 2 ∂ν := integral_nonneg fun z => sq_nonneg _
  unfold gaussCoef
  positivity

/-- **`eq:w-tail` on the good-walk event**, with the Gaussian remainder already
written as a polynomial tail of order `2n`. -/
theorem meas_fluctOn_ge_good [IsProbabilityMeasure ν] {p c Cp : ℝ} (n : ℕ)
    (hFN : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp B : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          0 < B → B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P →
          (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / B ^ 2)))
    (hdeg : ∀ v : V, 1 ≤ G.degree v)
    (m : ℝ) (hint : Integrable (fun z : ℝ => z) ν) (hm : ∫ z, z ∂ν = m)
    (hsq : Integrable (fun z : ℝ => (z - m) ^ 2) ν)
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤) (hc : 0 < c)
    (hCp : 0 ≤ Cp)
    {α δ : ℝ} {k a b : ℕ} (hab : a < b) (hb : b ≤ 2 ^ (k + 1))
    {X : ℕ → V} (hX : X ∈ RWRS.goodWalk (V := V) α δ k)
    (t : ℝ) (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t ≤ |fluctOn G ξ m a b X|}
      ≤ ENNReal.ofReal (Cp * (∑ v ∈ walkSites a b X,
            incWeight G a b X v ^ p * (RWRS.centeredMoment ν m p).toReal) / t ^ p)
        + ENNReal.ofReal (gaussCoef c n ν m
            * (((b - a : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ n / t ^ (2 * n)) := by
  classical
  have hf : Measurable fun z : ℝ => z - m := measurable_id.sub_const m
  have hfint : Integrable (fun z : ℝ => z - m) ν := hint.sub (integrable_const m)
  have hf0 : ∫ z, (z - m) ∂ν = 0 := by
    rw [integral_sub hint (integrable_const m), hm, integral_const]
    simp
  have hfp : (∫⁻ y, ENNReal.ofReal (|y - m| ^ p) ∂ν) ≠ ⊤ := centeredMoment_ne_top ν hp hmom
  set Vr : ℝ := ∫ z, (z - m) ^ 2 ∂ν with hVr
  have hVr0 : (0:ℝ) ≤ Vr := integral_nonneg fun z => sq_nonneg _
  set L : ℝ := ((b - a : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ) with hL
  have hba : (0:ℝ) < ((b - a : ℕ) : ℝ) := by
    have : 0 < b - a := by omega
    exact_mod_cast this
  have hNpos : (0:ℝ) < (2 ^ (k + 1) : ℝ) ^ (α + δ) := Real.rpow_pos_of_pos (by positivity) _
  have hLpos : (0:ℝ) < L := by rw [hL]; positivity
  set Bb : ℝ := Real.sqrt ((Vr + 1) * L) with hBb
  have hargpos : (0:ℝ) < (Vr + 1) * L := by positivity
  have hBbpos : 0 < Bb := Real.sqrt_pos.2 hargpos
  have hBb2 : Bb ^ 2 = (Vr + 1) * L := Real.sq_sqrt hargpos.le
  have hvar : ∑ v ∈ walkSites a b X, incWeight G a b X v ^ 2 * ∫ z, (z - m) ^ 2 ∂ν ≤ Bb ^ 2 := by
    rw [hBb2, ← Finset.sum_mul, ← hVr]
    have h1 : ∑ v ∈ walkSites a b X, incWeight G a b X v ^ 2
        ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) * ((b - a : ℕ) : ℝ) :=
      sum_incWeight_sq_le_of_good hdeg hb hX
    have h2 : (2 ^ (k + 1) : ℝ) ^ (α + δ) * ((b - a : ℕ) : ℝ) = L := by rw [hL]; ring
    rw [h2] at h1
    nlinarith [hLpos, hVr0]
  have hset : {ξ : V → ℝ | t ≤ |fluctOn G ξ m a b X|}
      = {ξ : V → ℝ | t ≤ |∑ v ∈ walkSites a b X, incWeight G a b X v * (ξ v - m)|} := by
    ext ξ
    simp only [Set.mem_setOf_eq, fluctOn_eq_sum_sites]
  have hmain := meas_weighted_sum_ge_gaussian_le hFN (walkSites a b X) (incWeight G a b X)
    hf hfint hsq hf0 hfp hc Bb hvar t ht
  rw [hset]
  refine le_trans hmain ?_
  have hw : ∀ v ∈ walkSites a b X,
      |incWeight G a b X v| ^ p * (∫⁻ y, ENNReal.ofReal (|y - m| ^ p) ∂ν).toReal
        = incWeight G a b X v ^ p * (RWRS.centeredMoment ν m p).toReal := by
    intro v _
    rw [abs_of_nonneg (incWeight_nonneg a b X v)]
    rfl
  rw [Finset.sum_congr rfl hw]
  set Mp : ℝ := ∑ v ∈ walkSites a b X,
    incWeight G a b X v ^ p * (RWRS.centeredMoment ν m p).toReal with hMp
  have hMp0 : (0:ℝ) ≤ Mp := by
    refine Finset.sum_nonneg fun v _ => ?_
    have h1 : (0:ℝ) ≤ incWeight G a b X v ^ p :=
      Real.rpow_nonneg (incWeight_nonneg a b X v) p
    positivity
  have hA0 : (0:ℝ) ≤ Cp * Mp / t ^ p := by positivity
  have hgauss : 2 * Real.exp (-c * t ^ 2 / Bb ^ 2)
      ≤ gaussCoef c n ν m * L ^ n / t ^ (2 * n) := by
    have h := two_exp_neg_le (B2 := Bb ^ 2) n hc ht (by rw [hBb2]; exact hargpos)
    refine le_trans h (le_of_eq ?_)
    have halg : Bb ^ 2 / c = ((Vr + 1) / c) * L := by rw [hBb2]; ring
    rw [halg, mul_pow, gaussCoef, ← hVr]
    ring
  have hB0 : (0:ℝ) ≤ gaussCoef c n ν m * L ^ n / t ^ (2 * n) := by
    have h1 := gaussCoef_nonneg hc n ν m
    have h2 : (0:ℝ) ≤ L ^ n := by positivity
    positivity
  calc ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / Bb ^ 2))
      ≤ ENNReal.ofReal (Cp * Mp / t ^ p + gaussCoef c n ν m * L ^ n / t ^ (2 * n)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (Cp * Mp / t ^ p)
          + ENNReal.ofReal (gaussCoef c n ν m * L ^ n / t ^ (2 * n)) :=
        ENNReal.ofReal_add hA0 hB0

end RWRS.Support
