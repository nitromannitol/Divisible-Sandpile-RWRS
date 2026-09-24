/-
The `q`-th moment of `Y_k` on the good-walk event, for `prop:subcritical`.

`rwrs.tex:1205`: "Tail integration gives ...".  The tail of `Y_k` is two shifted
polynomial tails, of orders `p` and `2n`, and each contributes
`q K a^{q-s}(1/q + 1/(s-q))` with `a = |E[ξ]| 2^k / d` the shift.
-/
import RWRS.Support.SubTail
import RWRS.Support.SubConst

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The value of the layer-cake integral of a shifted polynomial tail. -/
noncomputable def tailValue (q a K s : ℝ) : ℝ := q * K * a ^ (q - s) * (1 / q + 1 / (s - q))

theorem tailValue_nonneg {q a K s : ℝ} (hq : 0 < q) (ha : 0 < a) (hK : 0 ≤ K) (hqs : q < s) :
    0 ≤ tailValue q a K s := by
  have h1 : (0:ℝ) < a ^ (q - s) := Real.rpow_pos_of_pos ha _
  have h2 : (0:ℝ) < 1 / q + 1 / (s - q) := by
    have : (0:ℝ) < s - q := by linarith
    positivity
  unfold tailValue
  positivity

theorem ofReal_tail_eq {q a K s : ℝ} (hq : 0 < q) (ha : 0 < a) (hK : 0 ≤ K) (hqs : q < s) :
    ENNReal.ofReal q * (ENNReal.ofReal (a ^ q / q) * ENNReal.ofReal (K / a ^ s)
      + ENNReal.ofReal K * ENNReal.ofReal (a ^ (q - s) / (s - q)))
      = ENNReal.ofReal (tailValue q a K s) := by
  have hs : 0 < s := lt_trans hq hqs
  have haq : (0:ℝ) < a ^ q := Real.rpow_pos_of_pos ha q
  have has : (0:ℝ) < a ^ s := Real.rpow_pos_of_pos ha s
  have hasub : a ^ (q - s) = a ^ q / a ^ s := Real.rpow_sub ha q s
  have hsq : (0:ℝ) < s - q := by linarith
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hq.le]
  congr 1
  unfold tailValue
  rw [hasub]
  field_simp

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

/-- **The `q`-th moment of `Y_k` on the good-walk event**, by tail integration of
`eq:Mk-tail-Ak`. -/
theorem lintegral_good_dyadicY_rpow_le [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] (hG : G.Connected)
    [IsProbabilityMeasure ν] {p c Cp d_s A q : ℝ} (nn : ℕ)
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
    {α δ : ℝ} {k d : ℕ} (hd : 0 < d) (hmneg : m < 0)
    (hq : 0 < q) (hqp : q < p) (hq2 : q < ((2 * nn : ℕ) : ℝ)) (x : V) :
    (∫⁻ z in {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k},
        ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q) ∂(RWRS.jointLaw G ν x))
      ≤ ENNReal.ofReal (tailValue q (|m| / (d : ℝ) * 2 ^ k)
            (polyBlockConst Cp ν m p A d_s k) p)
        + ENNReal.ofReal (tailValue q (|m| / (d : ℝ) * 2 ^ k)
            (gaussBlockConst c nn ν m α δ k) ((2 * nn : ℕ) : ℝ)) := by
  classical
  have hmB : MeasurableSet {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k} :=
    measurable_snd (measurableSet_goodWalk α δ k)
  have hmpos : (0:ℝ) < |m| := abs_pos.2 (ne_of_lt hmneg)
  have hdpos : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have ha : (0:ℝ) < |m| / (d : ℝ) * 2 ^ k := by positivity
  have hK1 : 0 ≤ polyBlockConst Cp ν m p A d_s k := polyBlockConst_nonneg hCp ν hp k
  have hK2 : 0 ≤ gaussBlockConst c nn ν m α δ k := gaussBlockConst_nonneg hc nn ν m α δ k
  have hY0 : ∀ z : (V → ℝ) × (ℕ → V), 0 ≤ RWRS.dyadicY G z.1 m d k z.2 :=
    fun z => le_max_right _ _
  have hYm : AEMeasurable (fun z : (V → ℝ) × (ℕ → V) => RWRS.dyadicY G z.1 m d k z.2)
      ((RWRS.jointLaw G ν x).restrict
        {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k}) :=
    (measurable_dyadicY m d k).aemeasurable
  have htail : ∀ t : ℝ, 0 < t →
      ((RWRS.jointLaw G ν x).restrict
          {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k})
        {z : (V → ℝ) × (ℕ → V) | t < RWRS.dyadicY G z.1 m d k z.2}
      ≤ ENNReal.ofReal (polyBlockConst Cp ν m p A d_s k
            / (|m| / (d : ℝ) * 2 ^ k + t) ^ p)
        + ENNReal.ofReal (gaussBlockConst c nn ν m α δ k
            / (|m| / (d : ℝ) * 2 ^ k + t) ^ ((2 * nn : ℕ) : ℝ)) := by
    intro t ht
    rw [Measure.restrict_apply
      (measurableSet_lt measurable_const (measurable_dyadicY m d k))]
    exact meas_jointLaw_good_lt_dyadicY_le_const hG nn hFN hdeg hds hsp m hint hm hsq hp
      hmom hc hCp x ht
  have hmain := lintegral_rpow_le_of_tail2
    ((RWRS.jointLaw G ν x).restrict
      {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k})
    (fun z => RWRS.dyadicY G z.1 m d k z.2) hY0 hYm hq ha hK1 hK2 hqp hq2 htail
  rw [mul_add, ofReal_tail_eq hq ha hK1 hqp, ofReal_tail_eq hq ha hK2 hq2] at hmain
  exact hmain


end RWRS.Support
