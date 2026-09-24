/-
The growth in the scale of the two constants of `eq:Mk-tail-Ak`, for
`prop:subcritical`.

`rwrs.tex:1197`: "The polynomial coefficient arises from the union bound over
`O(2^k)` dyadic intervals, each contributing `O(2^j Λ_p(2^j))`; the geometric sum
is dominated by its largest term."  Here the clock plays the role of `Λ_p`, and
`clockH_le_rpow` absorbs the logarithm of the critical spectral dimension into an
arbitrarily small extra exponent.
-/
import RWRS.Support.SubMomentK

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The value of the layer-cake integral at the `k`-th scale, in the form
`constant times a polynomial in `k` times a power of two`. -/
theorem tailValue_le {q a0 s : ℝ} (hq : 0 < q) (ha0 : 0 < a0) (hqs : q < s)
    {K C N e : ℝ} (k : ℕ)
    (hKle : K ≤ C * ((k : ℝ) + 1) ^ N * (2:ℝ) ^ ((k : ℝ) * e)) :
    tailValue q (a0 * 2 ^ k) K s
      ≤ (q * C * a0 ^ (q - s) * (1 / q + 1 / (s - q)))
          * ((k : ℝ) + 1) ^ N * (2:ℝ) ^ ((k : ℝ) * (e + q - s)) := by
  have h2k : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have hsq : (0:ℝ) < s - q := by linarith
  have hcoef : (0:ℝ) < 1 / q + 1 / (s - q) := by positivity
  have hsplit : (a0 * 2 ^ k) ^ (q - s) = a0 ^ (q - s) * ((2:ℝ) ^ k) ^ (q - s) :=
    Real.mul_rpow ha0.le h2k.le
  have hpow : ((2:ℝ) ^ k) ^ (q - s) = (2:ℝ) ^ ((k : ℝ) * (q - s)) := by
    rw [← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_mul (by norm_num)]
  have hpos1 : (0:ℝ) ≤ a0 ^ (q - s) := (Real.rpow_pos_of_pos ha0 _).le
  have hpos2 : (0:ℝ) < (2:ℝ) ^ ((k : ℝ) * (q - s)) := Real.rpow_pos_of_pos (by norm_num) _
  unfold tailValue
  rw [hsplit, hpow]
  have hstep : q * K * (a0 ^ (q - s) * (2:ℝ) ^ ((k : ℝ) * (q - s))) * (1 / q + 1 / (s - q))
      ≤ q * (C * ((k : ℝ) + 1) ^ N * (2:ℝ) ^ ((k : ℝ) * e))
          * (a0 ^ (q - s) * (2:ℝ) ^ ((k : ℝ) * (q - s))) * (1 / q + 1 / (s - q)) := by
    have hfac : (0:ℝ) ≤ q * (a0 ^ (q - s) * (2:ℝ) ^ ((k : ℝ) * (q - s)))
        * (1 / q + 1 / (s - q)) := by positivity
    nlinarith [hKle, hfac, hpos2, hpos1, hq.le, hcoef.le]
  refine le_trans hstep (le_of_eq ?_)
  have hadd : (2:ℝ) ^ ((k : ℝ) * e) * (2:ℝ) ^ ((k : ℝ) * (q - s))
      = (2:ℝ) ^ ((k : ℝ) * (e + q - s)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  calc q * (C * ((k : ℝ) + 1) ^ N * (2:ℝ) ^ ((k : ℝ) * e))
        * (a0 ^ (q - s) * (2:ℝ) ^ ((k : ℝ) * (q - s))) * (1 / q + 1 / (s - q))
      = (q * C * a0 ^ (q - s) * (1 / q + 1 / (s - q))) * ((k : ℝ) + 1) ^ N
          * ((2:ℝ) ^ ((k : ℝ) * e) * (2:ℝ) ^ ((k : ℝ) * (q - s))) := by ring
    _ = (q * C * a0 ^ (q - s) * (1 / q + 1 / (s - q))) * ((k : ℝ) + 1) ^ N
          * (2:ℝ) ^ ((k : ℝ) * (e + q - s)) := by rw [hadd]

/-- **The constant of the polynomial term grows at the rate `2^{k(1+(α+η)(p-1))}`**,
the logarithm of the critical spectral dimension being absorbed by `η`. -/
theorem polyBlockConst_le {Cp : ℝ} (hCp : 0 ≤ Cp) (ν : Measure ℝ) {m p A d_s η : ℝ}
    (hp : 1 ≤ p) (hds : 0 < d_s) (hη : 0 < η) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ k : ℕ,
      polyBlockConst Cp ν m p A d_s k
        ≤ C1 * ((k : ℝ) + 1) ^ (p + 1)
            * (2:ℝ) ^ ((k : ℝ) * (1 + (max (1 - d_s / 2) 0 + η) * (p - 1))) := by
  obtain ⟨K, hK0, hKle⟩ := clockH_le_rpow A d_s η hds hη
  set α : ℝ := max (1 - d_s / 2) 0 with hαdef
  have hα0 : (0:ℝ) ≤ α := le_max_right _ _
  have hCM : (0:ℝ) ≤ (RWRS.centeredMoment ν m p).toReal := ENNReal.toReal_nonneg
  have hmc : (0:ℝ) < momConst ⌈p⌉₊ := momConst_pos _
  have hKp : (0:ℝ) < K ^ (p - 1) := Real.rpow_pos_of_pos hK0 _
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hE0 : (0:ℝ) ≤ (α + η) * (p - 1) := by nlinarith
  refine ⟨Cp * (RWRS.centeredMoment ν m p).toReal * p * momConst ⌈p⌉₊ * 2 * K ^ (p - 1) + 1,
    by positivity, fun k => ?_⟩
  set E : ℝ := (α + η) * (p - 1) with hEdef
  set X : ℝ := (2:ℝ) ^ k with hXdef
  have hX : (0:ℝ) < X := by rw [hXdef]; positivity
  have hterm : ∀ s ∈ Finset.range (k + 1),
      ((2 ^ (k + 1 - s) : ℕ) : ℝ)
          * (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ s) ^ (p - 1) * ((2 ^ s : ℕ) : ℝ))
        ≤ p * momConst ⌈p⌉₊ * K ^ (p - 1) * X ^ E * (2 * X) := by
    intro s hs
    rw [Finset.mem_range] at hs
    have hsplit : ((2 ^ (k + 1 - s) : ℕ) : ℝ) * ((2 ^ s : ℕ) : ℝ) = 2 * X := by
      rw [hXdef]
      push_cast
      rw [← pow_add]
      have : k + 1 - s + s = k + 1 := by omega
      rw [this, pow_succ]
      ring
    have hcl : clockH A d_s (2 ^ s) ^ (p - 1)
        ≤ K ^ (p - 1) * X ^ E := by
      have h1 : clockH A d_s (2 ^ s) ≤ K * (((2 ^ s : ℕ) : ℝ)) ^ (α + η) :=
        hKle (2 ^ s) Nat.one_le_two_pow
      have h2 : clockH A d_s (2 ^ s) ^ (p - 1)
          ≤ (K * (((2 ^ s : ℕ) : ℝ)) ^ (α + η)) ^ (p - 1) :=
        Real.rpow_le_rpow (clockH_pos A d_s Nat.one_le_two_pow).le h1 (by linarith)
      have heq : (K * (((2 ^ s : ℕ) : ℝ)) ^ (α + η)) ^ (p - 1)
          = K ^ (p - 1) * ((((2 ^ s : ℕ) : ℝ)) ^ (α + η)) ^ (p - 1) :=
        Real.mul_rpow hK0.le (Real.rpow_nonneg (by positivity) _)
      refine le_trans h2 ?_
      rw [heq]
      · refine mul_le_mul_of_nonneg_left ?_ hKp.le
        have h3 : ((((2 ^ s : ℕ) : ℝ)) ^ (α + η)) ^ (p - 1)
            = (((2 ^ s : ℕ) : ℝ)) ^ E := by
          rw [← Real.rpow_mul (by positivity)]
        rw [h3, hEdef, hXdef]
        refine Real.rpow_le_rpow (by positivity) ?_ hE0
        push_cast
        exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hmul : (0:ℝ) ≤ p * momConst ⌈p⌉₊ := by positivity
    calc ((2 ^ (k + 1 - s) : ℕ) : ℝ)
          * (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ s) ^ (p - 1) * ((2 ^ s : ℕ) : ℝ))
        = (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ s) ^ (p - 1))
            * (((2 ^ (k + 1 - s) : ℕ) : ℝ) * ((2 ^ s : ℕ) : ℝ)) := by ring
      _ = (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ s) ^ (p - 1)) * (2 * X) := by rw [hsplit]
      _ ≤ (p * momConst ⌈p⌉₊ * (K ^ (p - 1) * X ^ E)) * (2 * X) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hcl hmul
      _ = p * momConst ⌈p⌉₊ * K ^ (p - 1) * X ^ E * (2 * X) := by ring
  have hsum : ∑ s ∈ Finset.range (k + 1), ((2 ^ (k + 1 - s) : ℕ) : ℝ)
      * (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ s) ^ (p - 1) * ((2 ^ s : ℕ) : ℝ))
      ≤ ((k : ℝ) + 1) * (p * momConst ⌈p⌉₊ * K ^ (p - 1) * X ^ E * (2 * X)) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_of_eq rfl
  have hXpow : X ^ E * X = (2:ℝ) ^ ((k : ℝ) * (1 + E)) := by
    have h1 : X ^ E * X = X ^ (E + 1) := by
      rw [Real.rpow_add hX E 1, Real.rpow_one]
    rw [h1, hXdef, ← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hkpow : ((k : ℝ) + 1) ^ p * ((k : ℝ) + 1) = ((k : ℝ) + 1) ^ (p + 1) := by
    rw [Real.rpow_add (by positivity) p 1, Real.rpow_one]
  rw [polyBlockConst]
  calc Cp * (RWRS.centeredMoment ν m p).toReal * ((k : ℝ) + 1) ^ p
        * ∑ s ∈ Finset.range (k + 1), ((2 ^ (k + 1 - s) : ℕ) : ℝ)
            * (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ s) ^ (p - 1) * ((2 ^ s : ℕ) : ℝ))
      ≤ Cp * (RWRS.centeredMoment ν m p).toReal * ((k : ℝ) + 1) ^ p
          * (((k : ℝ) + 1) * (p * momConst ⌈p⌉₊ * K ^ (p - 1) * X ^ E * (2 * X))) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        have : (0:ℝ) ≤ ((k : ℝ) + 1) ^ p := Real.rpow_nonneg (by positivity) _
        positivity
    _ = (Cp * (RWRS.centeredMoment ν m p).toReal * p * momConst ⌈p⌉₊ * 2 * K ^ (p - 1))
          * (((k : ℝ) + 1) ^ p * ((k : ℝ) + 1)) * (X ^ E * X) := by ring
    _ = (Cp * (RWRS.centeredMoment ν m p).toReal * p * momConst ⌈p⌉₊ * 2 * K ^ (p - 1))
          * ((k : ℝ) + 1) ^ (p + 1) * (2:ℝ) ^ ((k : ℝ) * (1 + E)) := by
        rw [hkpow, hXpow]
    _ ≤ (Cp * (RWRS.centeredMoment ν m p).toReal * p * momConst ⌈p⌉₊ * 2 * K ^ (p - 1) + 1)
          * ((k : ℝ) + 1) ^ (p + 1) * (2:ℝ) ^ ((k : ℝ) * (1 + E)) := by
        have h1 : (0:ℝ) ≤ ((k : ℝ) + 1) ^ (p + 1) := Real.rpow_nonneg (by positivity) _
        have h2 : (0:ℝ) < (2:ℝ) ^ ((k : ℝ) * (1 + E)) := Real.rpow_pos_of_pos (by norm_num) _
        nlinarith [h1, h2]


/-- **The constant of the Gaussian term grows at the rate
`2^{k(1+n+(α+δ)n)}`.** -/
theorem gaussBlockConst_le {c : ℝ} (hc : 0 < c) (nn : ℕ) (ν : Measure ℝ) (m : ℝ)
    {α δ : ℝ} :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ k : ℕ,
      gaussBlockConst c nn ν m α δ k
        ≤ C2 * ((k : ℝ) + 1) ^ (((2 * nn + 1 : ℕ)) : ℝ)
            * (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn)) := by
  have hg := gaussCoef_nonneg hc nn ν m
  refine ⟨gaussCoef c nn ν m * (2:ℝ) ^ (1 + (α + δ) * nn) + 1, by positivity, fun k => ?_⟩
  have h2 : (0:ℝ) < (2:ℝ) := by norm_num
  have hterm : ∀ s ∈ Finset.range (k + 1),
      ((2 ^ (k + 1 - s) : ℕ) : ℝ)
          * ((((2 ^ s : ℕ) : ℝ)) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
        ≤ (2:ℝ) ^ (1 + (α + δ) * nn) * (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn)) := by
    intro s hs
    rw [Finset.mem_range] at hs
    have hsk : s ≤ k := by omega
    have h1 : ((2 ^ (k + 1 - s) : ℕ) : ℝ) ≤ (2:ℝ) ^ ((k : ℝ) + 1) := by
      push_cast
      rw [← Real.rpow_natCast (2:ℝ) (k + 1 - s)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : ((k + 1 - s : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le _ _
      push_cast at this ⊢
      linarith
    have h2s : (((2 ^ s : ℕ) : ℝ)) ^ nn ≤ ((2:ℝ) ^ ((k : ℝ) * (nn : ℝ))) := by
      have hle : (((2 ^ s : ℕ) : ℝ)) ≤ (2:ℝ) ^ ((k : ℝ)) := by
        push_cast
        rw [← Real.rpow_natCast (2:ℝ) s]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hsk)
      calc (((2 ^ s : ℕ) : ℝ)) ^ nn ≤ ((2:ℝ) ^ ((k : ℝ))) ^ nn :=
            pow_le_pow_left₀ (by positivity) hle nn
        _ = (2:ℝ) ^ ((k : ℝ) * (nn : ℝ)) := by
            rw [← Real.rpow_natCast ((2:ℝ) ^ ((k : ℝ))) nn, ← Real.rpow_mul (by norm_num)]
    have h3 : ((2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
        = (2:ℝ) ^ (((k : ℝ) + 1) * ((α + δ) * nn)) := by
      have hb : ((2:ℝ) ^ (k + 1) : ℝ) = (2:ℝ) ^ (((k : ℝ) + 1)) := by
        rw [← Real.rpow_natCast (2:ℝ) (k + 1)]
        push_cast
        ring_nf
      rw [hb, ← Real.rpow_natCast (((2:ℝ) ^ (((k : ℝ) + 1))) ^ (α + δ)) nn,
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by norm_num)]
    rw [mul_pow, h3]
    have hnn1 : (0:ℝ) ≤ (2:ℝ) ^ (((k : ℝ) + 1) * ((α + δ) * nn)) := by positivity
    calc ((2 ^ (k + 1 - s) : ℕ) : ℝ)
          * ((((2 ^ s : ℕ) : ℝ)) ^ nn * (2:ℝ) ^ (((k : ℝ) + 1) * ((α + δ) * nn)))
        ≤ (2:ℝ) ^ ((k : ℝ) + 1)
            * ((2:ℝ) ^ ((k : ℝ) * (nn : ℝ)) * (2:ℝ) ^ (((k : ℝ) + 1) * ((α + δ) * nn))) := by
          refine mul_le_mul h1 (mul_le_mul_of_nonneg_right h2s hnn1) (by positivity)
            (by positivity)
      _ = (2:ℝ) ^ (((k : ℝ) + 1) + (k : ℝ) * (nn : ℝ) + ((k : ℝ) + 1) * ((α + δ) * nn)) := by
          rw [← Real.rpow_add h2, ← Real.rpow_add h2]
          ring_nf
      _ = (2:ℝ) ^ (1 + (α + δ) * nn) * (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn)) := by
          rw [← Real.rpow_add h2]
          congr 1
          ring
  have hsum : ∑ s ∈ Finset.range (k + 1), ((2 ^ (k + 1 - s) : ℕ) : ℝ)
      * ((((2 ^ s : ℕ) : ℝ)) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
      ≤ ((k : ℝ) + 1) * ((2:ℝ) ^ (1 + (α + δ) * nn)
          * (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn))) := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    exact le_of_eq rfl
  have hkpow : ((k : ℝ) + 1) ^ (2 * nn) * ((k : ℝ) + 1)
      = ((k : ℝ) + 1) ^ (((2 * nn + 1 : ℕ)) : ℝ) := by
    have hb : (0:ℝ) < (k : ℝ) + 1 := by positivity
    rw [← Real.rpow_natCast ((k : ℝ) + 1) (2 * nn),
      show ((2 * nn + 1 : ℕ) : ℝ) = ((2 * nn : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.rpow_add hb, Real.rpow_one]
  rw [gaussBlockConst]
  calc gaussCoef c nn ν m * ((k : ℝ) + 1) ^ (2 * nn)
        * ∑ s ∈ Finset.range (k + 1), ((2 ^ (k + 1 - s) : ℕ) : ℝ)
            * ((((2 ^ s : ℕ) : ℝ)) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
      ≤ gaussCoef c nn ν m * ((k : ℝ) + 1) ^ (2 * nn)
          * (((k : ℝ) + 1) * ((2:ℝ) ^ (1 + (α + δ) * nn)
              * (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn)))) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        positivity
    _ = (gaussCoef c nn ν m * (2:ℝ) ^ (1 + (α + δ) * nn))
          * (((k : ℝ) + 1) ^ (2 * nn) * ((k : ℝ) + 1))
          * (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn)) := by ring
    _ = (gaussCoef c nn ν m * (2:ℝ) ^ (1 + (α + δ) * nn))
          * ((k : ℝ) + 1) ^ (((2 * nn + 1 : ℕ)) : ℝ)
          * (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn)) := by rw [hkpow]
    _ ≤ (gaussCoef c nn ν m * (2:ℝ) ^ (1 + (α + δ) * nn) + 1)
          * ((k : ℝ) + 1) ^ (((2 * nn + 1 : ℕ)) : ℝ)
          * (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn)) := by
        have h1 : (0:ℝ) ≤ ((k : ℝ) + 1) ^ (((2 * nn + 1 : ℕ)) : ℝ) :=
          Real.rpow_nonneg (by positivity) _
        have h2' : (0:ℝ) < (2:ℝ) ^ ((k : ℝ) * (1 + (nn : ℝ) + (α + δ) * nn)) :=
          Real.rpow_pos_of_pos (by norm_num) _
        nlinarith [h1, h2']


end RWRS.Support
