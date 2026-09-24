/-
The union bound of `eq:Mk-tail-Ak` on the good-walk event, for `prop:subcritical`.

Each `W_n` with `n` in the `k`-th dyadic block decomposes into at most `k+1`
increments over dyadic sub-intervals of `[0,2^{k+1})`, so if the block maximum
exceeds `u` then one increment exceeds `u/(k+1)`.  Summing `eq:w-tail` over the
index set of those sub-intervals gives the tail of `Y_k`, for a fixed
trajectory of the walk.
-/
import RWRS.Support.SubGood
import RWRS.Support.SubBlock

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

/-- The membership in the dyadic index set spelled out. -/
theorem mem_dyadicIdx_iff {k : ℕ} {q : ℕ × ℕ} (hq : q ∈ dyadicIdx k) :
    q.1 ≤ k ∧ q.2 < 2 ^ (k + 1 - q.1) := by
  unfold dyadicIdx at hq
  obtain ⟨s, hs, hq⟩ := Finset.mem_biUnion.1 hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hq
  exact ⟨by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hs), Finset.mem_range.1 hi⟩

/-- The dyadic interval of a scale-position pair sits inside `[0,2^{k+1})`. -/
theorem dyadicIdx_bounds {k : ℕ} {q : ℕ × ℕ} (hq : q ∈ dyadicIdx k) :
    q.2 * 2 ^ q.1 < (q.2 + 1) * 2 ^ q.1
      ∧ (q.2 + 1) * 2 ^ q.1 ≤ 2 ^ (k + 1)
      ∧ (q.2 + 1) * 2 ^ q.1 - q.2 * 2 ^ q.1 = 2 ^ q.1 := by
  obtain ⟨hs, hi⟩ := mem_dyadicIdx_iff hq
  have hpow : 0 < 2 ^ q.1 := Nat.two_pow_pos _
  refine ⟨by nlinarith, ?_, by ring_nf; omega⟩
  have h1 : q.2 + 1 ≤ 2 ^ (k + 1 - q.1) := hi
  calc (q.2 + 1) * 2 ^ q.1 ≤ 2 ^ (k + 1 - q.1) * 2 ^ q.1 := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (k + 1 - q.1 + q.1) := (pow_add 2 (k + 1 - q.1) q.1).symm
    _ = 2 ^ (k + 1) := by congr 1; omega

variable {ν : Measure ℝ}

/-- **`eq:Mk-tail-Ak` on the good-walk event, for a fixed trajectory.**  The
union bound over the dyadic sub-intervals, each contributing a polynomial tail
of order `p` and one of order `2n`. -/
theorem meas_block_gt_le_good [IsProbabilityMeasure ν] {p c Cp : ℝ} (nn : ℕ)
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
    {u : ℝ} (hu : 0 < u) :
    RWRS.iidLaw V ν
        {ξ : V → ℝ | ∃ j ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), u < RWRS.fluctuation G ξ m j X}
      ≤ ∑ q ∈ dyadicIdx k,
          (ENNReal.ofReal (Cp * (∑ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X,
              incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v ^ p
                * (RWRS.centeredMoment ν m p).toReal) / (u / ((k : ℝ) + 1)) ^ p)
            + ENNReal.ofReal (gaussCoef c nn ν m
                * (((2 ^ q.1 : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
                  / (u / ((k : ℝ) + 1)) ^ (2 * nn))) := by
  have ht : 0 < u / ((k : ℝ) + 1) := by positivity
  refine le_trans (measure_mono (block_gt_subset m u X k)) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine Finset.sum_le_sum fun q hq => ?_
  obtain ⟨hlt, hle, hlen⟩ := dyadicIdx_bounds hq
  have hbound := meas_fluctOn_ge_good nn hFN hdeg m hint hm hsq hp hmom hc hCp hlt hle hX _ ht
  rw [hlen] at hbound
  refine le_trans (measure_mono (fun ξ hξ => ?_)) hbound
  have hξ' : u / ((k : ℝ) + 1) < |dyadicInc G ξ m q X| := hξ
  exact le_of_lt hξ'

/-- **The tail of `Y_k` on the good-walk event**, for a fixed trajectory. -/
theorem meas_lt_dyadicY_le_good [IsProbabilityMeasure ν] {p c Cp : ℝ} (nn : ℕ)
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
          (ENNReal.ofReal (Cp * (∑ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X,
              incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v ^ p
                * (RWRS.centeredMoment ν m p).toReal)
              / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ p)
            + ENNReal.ofReal (gaussCoef c nn ν m
                * (((2 ^ q.1 : ℕ) : ℝ) * (2 ^ (k + 1) : ℝ) ^ (α + δ)) ^ nn
                  / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ (2 * nn))) := by
  have hc0 : (0:ℝ) ≤ |m| / (d : ℝ) * 2 ^ k := by positivity
  have hu : 0 < |m| / (d : ℝ) * 2 ^ k + t := by linarith
  have hset : {ξ : V → ℝ | t < RWRS.dyadicY G ξ m d k X}
      = {ξ : V → ℝ | ∃ j ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          |m| / (d : ℝ) * 2 ^ k + t < RWRS.fluctuation G ξ m j X} := by
    ext ξ
    exact lt_dyadicY_iff ξ m d k X ht
  rw [hset]
  exact meas_block_gt_le_good nn hFN hdeg m hint hm hsq hp hmom hc hCp hX hu


end RWRS.Support
