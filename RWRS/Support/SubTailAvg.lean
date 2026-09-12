/-
The walk average of `eq:Mk-tail-Ak`, for `prop:subcritical`.

The tail of `Y_k` on the good-walk event is a sum, over the dyadic
sub-intervals of `[0,2^{k+1})`, of a polynomial term of order `p` carrying the
power sum of the local times of that interval and a term of order `2n` carrying
only the length of the interval and the good-walk bound.  Averaging over the
walk replaces the first by `eq:poly-moment` and leaves the second untouched.
-/
import RWRS.Support.SubUnion
import RWRS.Support.SubAvg

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- A summand depending only on the scale is counted `2^{k+1-s}` times. -/
theorem sum_dyadicIdx_of_scale {M : Type*} [AddCommMonoid M] (k : ℕ) (F : ℕ → M) :
    ∑ q ∈ dyadicIdx k, F q.1
      = ∑ s ∈ Finset.range (k + 1), (2 ^ (k + 1 - s) : ℕ) • F s := by
  classical
  unfold dyadicIdx
  rw [Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_image (fun i _ j _ h => congrArg Prod.snd h)]
    simp
  · intro s _ s' _ hss
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_range]
    rintro ⟨a, b⟩ ⟨i, -, hi⟩ ⟨j, -, hj⟩
    rw [← hi] at hj
    exact hss (congrArg Prod.fst hj).symm

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- The power sum of the local times of a discrete interval. -/
noncomputable def localTimeOnSum (a b : ℕ) (r : ℝ) (X : ℕ → V) : ℝ≥0∞ :=
  ∑' v : V, ENNReal.ofReal (((localTimeOn a b v X : ℕ) : ℝ) ^ r)

theorem measurable_localTimeOnSum (a b : ℕ) (r : ℝ) :
    Measurable (fun X : ℕ → V => localTimeOnSum a b r X) := by
  refine Measurable.tsum fun v => ?_
  exact (measurable_localTimeOn_rpow (V := V) a b v r).ennreal_ofReal

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- The polynomial term of `eq:w-tail` is dominated by the power sum of the
local times. -/
theorem polyTerm_le (hdeg : ∀ v : V, 1 ≤ G.degree v) {ν : Measure ℝ} {m p T : ℝ}
    {Cp : ℝ} (hCp : 0 ≤ Cp) (hp : 0 ≤ p) (hT : 0 < T) (a b : ℕ) (X : ℕ → V) :
    ENNReal.ofReal (Cp * (∑ v ∈ walkSites a b X,
        incWeight G a b X v ^ p * (RWRS.centeredMoment ν m p).toReal) / T ^ p)
      ≤ ENNReal.ofReal (Cp * (RWRS.centeredMoment ν m p).toReal / T ^ p)
          * localTimeOnSum a b p X := by
  have hCM : (0:ℝ) ≤ (RWRS.centeredMoment ν m p).toReal := ENNReal.toReal_nonneg
  have hTp : (0:ℝ) < T ^ p := Real.rpow_pos_of_pos hT p
  have hfac : (0:ℝ) ≤ Cp * (RWRS.centeredMoment ν m p).toReal / T ^ p := by positivity
  have hsumnn : ∀ v : V, (0:ℝ) ≤ incWeight G a b X v ^ p :=
    fun v => Real.rpow_nonneg (incWeight_nonneg a b X v) p
  have hrw : Cp * (∑ v ∈ walkSites a b X,
      incWeight G a b X v ^ p * (RWRS.centeredMoment ν m p).toReal) / T ^ p
      = (Cp * (RWRS.centeredMoment ν m p).toReal / T ^ p)
        * ∑ v ∈ walkSites a b X, incWeight G a b X v ^ p := by
    rw [← Finset.sum_mul]
    field_simp
  rw [hrw, ENNReal.ofReal_mul hfac]
  refine mul_le_mul' le_rfl ?_
  have hstep : ENNReal.ofReal (∑ v ∈ walkSites a b X, incWeight G a b X v ^ p)
      ≤ ∑ v ∈ walkSites a b X, ENNReal.ofReal (((localTimeOn a b v X : ℕ) : ℝ) ^ p) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun v _ => hsumnn v)]
    refine Finset.sum_le_sum fun v _ => ENNReal.ofReal_le_ofReal ?_
    exact Real.rpow_le_rpow (incWeight_nonneg a b X v)
      (incWeight_le_localTimeOn hdeg a b X v) hp
  refine le_trans hstep ?_
  exact ENNReal.sum_le_tsum _

variable {ν : Measure ℝ}

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **The tail of `Y_k` on the good-walk event**, with the polynomial term
written against the power sum of the local times. -/
theorem meas_lt_dyadicY_le_good_poly [IsProbabilityMeasure ν] {p c Cp : ℝ} (nn : ℕ)
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
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤) (hc : 0 < c) (hCp : 0 ≤ Cp)
    {α δ : ℝ} {k : ℕ} {X : ℕ → V} (hX : X ∈ RWRS.goodWalk (V := V) α δ k)
    (d : ℕ) {t : ℝ} (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t < RWRS.dyadicY G ξ m d k X}
      ≤ ∑ q ∈ dyadicIdx k,
          (ENNReal.ofReal (Cp * (RWRS.centeredMoment ν m p).toReal
              / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ p)
              * localTimeOnSum (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) p X
            + ENNReal.ofReal (gaussCoef c nn ν m
                * (((2 ^ q.1 : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
                  / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ (2 * nn))) := by
  have hc0 : (0:ℝ) ≤ |m| / (d : ℝ) * 2 ^ k := by positivity
  have hT : (0:ℝ) < (|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1) := by positivity
  refine le_trans (meas_lt_dyadicY_le_good nn hFN hdeg m hint hm hsq hp hmom hc hCp hX d ht) ?_
  refine Finset.sum_le_sum fun q _ => add_le_add ?_ le_rfl
  exact polyTerm_le hdeg hCp (by linarith) hT _ _ X


/-- `lem:local-time` over a discrete interval, in the notation of this file. -/
theorem lintegral_localTimeOnSum_le' [Infinite V] (hG : G.Connected) {d_s A p : ℝ}
    (hds : 0 < d_s) (hsp : RWRS.SpectralDimensionBound G d_s A) (hp : 1 ≤ p)
    (x : V) {a b : ℕ} (hab : a < b) :
    (∫⁻ X, localTimeOnSum a b p X ∂(RWRS.walkLaw G x))
      ≤ ENNReal.ofReal
          (p * momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1) * ((b - a : ℕ) : ℝ)) := by
  unfold localTimeOnSum
  exact lintegral_localTimeOnSum_le hG hds hsp hp x hab

/-- **`eq:Mk-tail-Ak` averaged over the walk**, on the good-walk event. -/
theorem meas_jointLaw_good_lt_dyadicY_le [Infinite V] (hG : G.Connected)
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
    {α δ : ℝ} {k : ℕ} (d : ℕ) (x : V) {t : ℝ} (ht : 0 < t) :
    (RWRS.jointLaw G ν x) ({z : (V → ℝ) × (ℕ → V) | t < RWRS.dyadicY G z.1 m d k z.2}
        ∩ {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k})
      ≤ ∑ q ∈ dyadicIdx k,
          (ENNReal.ofReal (Cp * (RWRS.centeredMoment ν m p).toReal
              / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ p)
              * ENNReal.ofReal (p * momConst ⌈p⌉₊ * clockH A d_s (2 ^ q.1) ^ (p - 1)
                  * ((2 ^ q.1 : ℕ) : ℝ))
            + ENNReal.ofReal (gaussCoef c nn ν m
                * (((2 ^ q.1 : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
                  / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ (2 * nn))) := by
  classical
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by rw [walkLaw_eq_lib]; infer_instance
  have hmA : MeasurableSet {z : (V → ℝ) × (ℕ → V) | t < RWRS.dyadicY G z.1 m d k z.2} :=
    measurableSet_lt measurable_const (measurable_dyadicY m d k)
  have hmB : MeasurableSet {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k} :=
    measurable_snd (measurableSet_goodWalk α δ k)
  rw [jointLaw_apply_slice ν x (hmA.inter hmB)]
  have hpt : ∀ X : ℕ → V,
      RWRS.iidLaw V ν ((fun ξ => (ξ, X)) ⁻¹'
          ({z : (V → ℝ) × (ℕ → V) | t < RWRS.dyadicY G z.1 m d k z.2}
            ∩ {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k}))
        ≤ ∑ q ∈ dyadicIdx k,
            (ENNReal.ofReal (Cp * (RWRS.centeredMoment ν m p).toReal
                / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ p)
                * localTimeOnSum (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) p X
              + ENNReal.ofReal (gaussCoef c nn ν m
                  * (((2 ^ q.1 : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
                    / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ (2 * nn))) := by
    intro X
    by_cases hX : X ∈ RWRS.goodWalk (V := V) α δ k
    · have hpre : (fun ξ : V → ℝ => (ξ, X)) ⁻¹'
          ({z : (V → ℝ) × (ℕ → V) | t < RWRS.dyadicY G z.1 m d k z.2}
            ∩ {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k})
          = {ξ : V → ℝ | t < RWRS.dyadicY G ξ m d k X} := by
        ext ξ
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, hX, and_true]
      rw [hpre]
      exact meas_lt_dyadicY_le_good_poly nn hFN hdeg m hint hm hsq hp hmom hc hCp hX d ht
    · have hpre : (fun ξ : V → ℝ => (ξ, X)) ⁻¹'
          ({z : (V → ℝ) × (ℕ → V) | t < RWRS.dyadicY G z.1 m d k z.2}
            ∩ {z : (V → ℝ) × (ℕ → V) | z.2 ∈ RWRS.goodWalk (V := V) α δ k}) = ∅ := by
        ext ξ
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, hX, and_false,
          Set.mem_empty_iff_false]
      rw [hpre, measure_empty]
      exact bot_le
  refine le_trans (lintegral_mono hpt) ?_
  rw [lintegral_finsetSum _ (fun q _ =>
    ((measurable_const.mul
      (measurable_localTimeOnSum (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) p)).add
        measurable_const))]
  refine Finset.sum_le_sum fun q hq => ?_
  obtain ⟨hlt, hle, hlen⟩ := dyadicIdx_bounds hq
  rw [lintegral_add_right _ measurable_const,
    lintegral_const_mul _ (measurable_localTimeOnSum (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) p),
    lintegral_const, measure_univ, mul_one]
  refine add_le_add (mul_le_mul' le_rfl ?_) le_rfl
  have hb := lintegral_localTimeOnSum_le' hG hds hsp hp x hlt
  rw [hlen] at hb
  exact hb


end RWRS.Support
