/-
`eq:Mk-tail-Ak` of `prop:subcritical` in closed form.

The union bound over the dyadic sub-intervals of `[0,2^{k+1})` produces, at each
scale `s ≤ k`, at most `2^{k+1-s}` equal contributions, so the tail of `Y_k` on
the good-walk event is a sum of two shifted polynomial tails whose constants are
the two sums over the scales recorded here.
-/
import RWRS.Support.SubTailAvg

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The constant of the polynomial term of `eq:Mk-tail-Ak`. -/
noncomputable def polyBlockConst (Cp : ℝ) (ν : Measure ℝ) (m p A d_s : ℝ) (k : ℕ) : ℝ :=
  Cp * (RWRS.centeredMoment ν m p).toReal * ((k : ℝ) + 1) ^ p
    * ∑ s ∈ Finset.range (k + 1), ((2 ^ (k + 1 - s) : ℕ) : ℝ)
        * (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ s) ^ (p - 1) * ((2 ^ s : ℕ) : ℝ))

/-- The constant of the Gaussian term of `eq:Mk-tail-Ak`. -/
noncomputable def gaussBlockConst (c : ℝ) (nn : ℕ) (ν : Measure ℝ) (m α δ : ℝ) (k : ℕ) : ℝ :=
  gaussCoef c nn ν m * ((k : ℝ) + 1) ^ (2 * nn)
    * ∑ s ∈ Finset.range (k + 1), ((2 ^ (k + 1 - s) : ℕ) : ℝ)
        * (((2 ^ s : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn

theorem polyBlockConst_nonneg {Cp : ℝ} (hCp : 0 ≤ Cp) (ν : Measure ℝ) {m p A d_s : ℝ}
    (hp : 1 ≤ p) (k : ℕ) : 0 ≤ polyBlockConst Cp ν m p A d_s k := by
  have hCM : (0:ℝ) ≤ (RWRS.centeredMoment ν m p).toReal := ENNReal.toReal_nonneg
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => ?_)
  have h1 : (0:ℝ) < clockH A d_s (2 ^ s) := clockH_pos A d_s Nat.one_le_two_pow
  have h2 : (0:ℝ) ≤ clockH A d_s (2 ^ s) ^ (p - 1) := (Real.rpow_pos_of_pos h1 _).le
  have h3 : (0:ℝ) ≤ momConst ⌈p⌉₊ := (momConst_pos _).le
  positivity

theorem gaussBlockConst_nonneg {c : ℝ} (hc : 0 < c) (nn : ℕ) (ν : Measure ℝ) (m α δ : ℝ)
    (k : ℕ) : 0 ≤ gaussBlockConst c nn ν m α δ k := by
  have h1 := gaussCoef_nonneg hc nn ν m
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => ?_)
  have h2 : (0:ℝ) ≤ ((2 ^ s : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ) := by positivity
  positivity

/-- The shifted denominators of `eq:Mk-tail-Ak`, in `rpow` form. -/
theorem div_rpow_div_eq {C L u : ℝ} (hL : 0 < L) (hu : 0 < u) (p : ℝ) :
    C / (u / L) ^ p = C * L ^ p / u ^ p := by
  rw [Real.div_rpow hu.le hL.le]
  field_simp

theorem div_pow_div_eq {C L u : ℝ} (hL : 0 < L) (hu : 0 < u) (n : ℕ) :
    C / (u / L) ^ n = C * L ^ n / u ^ n := by
  rw [div_pow]
  have h1 : (0:ℝ) < L ^ n := by positivity
  have h2 : (0:ℝ) < u ^ n := by positivity
  field_simp

/-- A scale-only summand over the dyadic index set, in `[0,∞]`. -/
theorem sum_dyadicIdx_ofReal_mul {k : ℕ} {C : ℝ} (hC : 0 ≤ C) (F : ℕ → ℝ)
    (hF : ∀ s, 0 ≤ F s) :
    ∑ q ∈ dyadicIdx k, ENNReal.ofReal (C * F q.1)
      = ENNReal.ofReal (C * ∑ s ∈ Finset.range (k + 1),
          ((2 ^ (k + 1 - s) : ℕ) : ℝ) * F s) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg hC (hF q.1))]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  rw [sum_dyadicIdx_of_scale k F]
  exact Finset.sum_congr rfl fun s _ => by rw [nsmul_eq_mul]

variable {ν : Measure ℝ}

/-- **`eq:Mk-tail-Ak`**: the tail of `Y_k` on the good-walk event as two shifted
polynomial tails, of orders `p` and `2n`. -/
theorem meas_jointLaw_good_lt_dyadicY_le_const [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (hG : G.Connected)
    [IsProbabilityMeasure ν] {p c Cp d_s A : ℝ} (nn : ℕ)
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
    (hds : 0 < d_s) (hsp : RWRS.SpectralDimensionBound G d_s A)
    (m : ℝ) (hint : Integrable (fun z : ℝ => z) ν) (hm : ∫ z, z ∂ν = m)
    (hsq : Integrable (fun z : ℝ => (z - m) ^ 2) ν)
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤) (hc : 0 < c) (hCp : 0 ≤ Cp)
    {α δ : ℝ} {k d : ℕ} (x : V) {t : ℝ} (ht : 0 < t) :
    (RWRS.jointLaw G ν x) ({z : (V → ℝ) × (ℕ → V) | t < RWRS.dyadicY G z.1 m d k z.2}
        ∩ {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k})
      ≤ ENNReal.ofReal (polyBlockConst Cp ν m p A d_s k
            / (|m| / (d : ℝ) * 2 ^ k + t) ^ p)
        + ENNReal.ofReal (gaussBlockConst c nn ν m α δ k
            / (|m| / (d : ℝ) * 2 ^ k + t) ^ ((2 * nn : ℕ) : ℝ)) := by
  classical
  have hCM : (0:ℝ) ≤ (RWRS.centeredMoment ν m p).toReal := ENNReal.toReal_nonneg
  have hc0 : (0:ℝ) ≤ |m| / (d : ℝ) * 2 ^ k := by positivity
  have hu : (0:ℝ) < |m| / (d : ℝ) * 2 ^ k + t := by linarith
  have hL : (0:ℝ) < (k : ℝ) + 1 := by positivity
  set u : ℝ := |m| / (d : ℝ) * 2 ^ k + t with hudef
  set L : ℝ := (k : ℝ) + 1 with hLdef
  have hF1 : ∀ s : ℕ, (0:ℝ) ≤ p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ s) ^ (p - 1)
      * ((2 ^ s : ℕ) : ℝ) := by
    intro s
    have h1 : (0:ℝ) < clockH A d_s (2 ^ s) := clockH_pos A d_s Nat.one_le_two_pow
    have h2 : (0:ℝ) ≤ clockH A d_s (2 ^ s) ^ (p - 1) := (Real.rpow_pos_of_pos h1 _).le
    have h3 : (0:ℝ) ≤ momConst ⌈p⌉₊ := (momConst_pos _).le
    positivity
  have hF2 : ∀ s : ℕ, (0:ℝ) ≤ (((2 ^ s : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn := by
    intro s
    have h2 : (0:ℝ) ≤ ((2 ^ s : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ) := by positivity
    positivity
  refine le_trans (meas_jointLaw_good_lt_dyadicY_le hG nn hFN hdeg hds hsp m hint hm hsq hp
    hmom hc hCp d x ht) ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add (le_of_eq ?_) (le_of_eq ?_)
  · have hstep : ∀ q : ℕ × ℕ,
        ENNReal.ofReal (Cp * (RWRS.centeredMoment ν m p).toReal / (u / L) ^ p)
            * ENNReal.ofReal (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ q.1) ^ (p - 1)
                * ((2 ^ q.1 : ℕ) : ℝ))
          = ENNReal.ofReal ((Cp * (RWRS.centeredMoment ν m p).toReal * L ^ p / u ^ p)
              * (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ q.1) ^ (p - 1)
                  * ((2 ^ q.1 : ℕ) : ℝ))) := by
      intro q
      rw [div_rpow_div_eq hL hu p, ← ENNReal.ofReal_mul (by positivity)]
    rw [Finset.sum_congr rfl fun q _ => hstep q,
      sum_dyadicIdx_ofReal_mul (by positivity) _ hF1]
    rw [polyBlockConst]
    congr 1
    ring
  · have hstep : ∀ q : ℕ × ℕ,
        ENNReal.ofReal (gaussCoef c nn ν m
            * (((2 ^ q.1 : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn / (u / L) ^ (2 * nn))
          = ENNReal.ofReal ((gaussCoef c nn ν m * L ^ (2 * nn) / u ^ (2 * nn))
              * ((((2 ^ q.1 : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn)) := by
      intro q
      rw [div_pow_div_eq hL hu (2 * nn)]
      congr 1
      ring
    rw [Finset.sum_congr rfl fun q _ => hstep q,
      sum_dyadicIdx_ofReal_mul (by
        have h1 := gaussCoef_nonneg hc nn ν m
        have h2 : (0:ℝ) < L ^ (2 * nn) := by positivity
        have h3 : (0:ℝ) < u ^ (2 * nn) := by positivity
        positivity) _ hF2]
    rw [gaussBlockConst, Real.rpow_natCast]
    congr 1
    ring


end RWRS.Support
