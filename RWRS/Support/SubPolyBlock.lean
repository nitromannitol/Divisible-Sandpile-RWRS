/-
`eq:poly-Bernstein`: the tail of the block variable of the recentred field.

The chaining decomposition of `prop:subcritical` is pathwise and does not read
the law of the scenery, so it carries over verbatim: the fluctuation of the
recentred field at a time of the `k`-th dyadic block is a sum of at most `k+1`
increments over dyadic sub-intervals of `[0,2^{k+1})`, and if the block maximum
exceeds `u` then one of them exceeds `u/(k+1)`.  Summing the Bernstein tail of
`SubPolyField` over the index set, whose size is at most `(k+1)2^{k+1}`, gives
`eq:poly-Bernstein`.  What Step 5 needs from it is the probability that the
block variable is positive at all, since on the good-walk event the block
variable is bounded by a deterministic multiple of `N R_N^β`.
-/
import RWRS.Support.SubPolyField

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ρ : Measure ℝ}

/-- The dyadic index set of a block has at most `(k+1) 2^{k+1}` members. -/
theorem dyadicIdx_card_le (k : ℕ) : (dyadicIdx k).card ≤ (k + 1) * 2 ^ (k + 1) := by
  classical
  unfold dyadicIdx
  refine le_trans Finset.card_biUnion_le ?_
  have hterm : ∀ s ∈ Finset.range (k + 1),
      ((Finset.range (2 ^ (k + 1 - s))).image fun i => (s, i)).card ≤ 2 ^ (k + 1) := by
    intro s _
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_range]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- `Y_k` is positive exactly when the fluctuation exceeds the drift somewhere
in the block. -/
theorem zero_lt_dyadicY_iff (ξ : V → ℝ) (m : ℝ) (d k : ℕ) (X : ℕ → V) :
    0 < RWRS.dyadicY G ξ m d k X
      ↔ ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          |m| / (d : ℝ) * 2 ^ k < RWRS.fluctuation G ξ m n X := by
  classical
  have hc : (0:ℝ) ≤ |m| / (d : ℝ) * 2 ^ k := by positivity
  rw [RWRS.dyadicY, iSup_mem_finset_real _ (block_nonempty k) (block_compl k)]
  rw [lt_max_iff, or_iff_left (lt_irrefl (0:ℝ)), sub_pos, lt_max_iff,
    or_iff_left (not_lt.mpr hc)]
  rw [Finset.lt_sup'_iff]

/-- A nonnegative bounded variable has its `q`-th moment at most the `q`-th
power of the bound times the probability that it is positive. -/
theorem lintegral_rpow_le_of_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) {B q : ℝ} (hq : 0 < q)
    (hbd : ∀ ω, Y ω ≤ B) :
    (∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ) ≤ ENNReal.ofReal (B ^ q) * μ {ω | 0 < Y ω} := by
  have hmeas : MeasurableSet {ω | 0 < Y ω} := measurableSet_lt measurable_const hY
  have hpt : ∀ ω, ENNReal.ofReal (Y ω ^ q)
      ≤ Set.indicator {ω | 0 < Y ω} (fun _ => ENNReal.ofReal (B ^ q)) ω := by
    intro ω
    by_cases h : 0 < Y ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | 0 < Y ω} from h)]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (hY0 ω) (hbd ω) hq.le)
    · have hz : Y ω = 0 := le_antisymm (not_lt.1 h) (hY0 ω)
      rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < Y ω} from h), hz,
        Real.zero_rpow (ne_of_gt hq), ENNReal.ofReal_zero]
  calc (∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ)
      ≤ ∫⁻ ω, Set.indicator {ω | 0 < Y ω} (fun _ => ENNReal.ofReal (B ^ q)) ω ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (B ^ q) * μ {ω | 0 < Y ω} := by
        rw [MeasureTheory.lintegral_indicator hmeas, lintegral_const,
          Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- **`eq:poly-Bernstein`, for a fixed trajectory**: the probability that the
fluctuation of the recentred field exceeds `u` somewhere in the `k`-th dyadic
block. -/
theorem meas_block_gt_zetaField_le [IsProbabilityMeasure ρ]
    (hBer : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
          B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
    {M m : ℝ} {t : V → ℝ} (ht : ∀ v : V, -M ≤ t v)
    (X : ℕ → V) (k : ℕ) {u : ℝ} (hu : 0 < u)
    (Mb Db : ℝ) (hMb : 0 < Mb) (hDb : 0 ≤ Db)
    (hbd : ∀ q ∈ dyadicIdx k,
      ∀ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X, ∀ z : ℝ,
        |incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v
          * (siteShift ρ M m (t v) z - m)| ≤ Mb)
    (hvar : ∀ q ∈ dyadicIdx k,
      ∑ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X,
        incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v ^ 2
          * ∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ ≤ Db) :
    RWRS.iidLaw V ρ {ξ : V → ℝ | ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        u < RWRS.fluctuation G (zetaField ρ M m t ξ) m n X}
      ≤ ENNReal.ofReal (((k : ℝ) + 1) * 2 ^ (k + 1)
          * (2 * Real.exp (-((u / ((k : ℝ) + 1)) ^ 2 / 2)
              / (Db + Mb * (u / ((k : ℝ) + 1)) / 3)))) := by
  set w : ℝ := u / ((k : ℝ) + 1) with hwdef
  have hw : 0 < w := by rw [hwdef]; positivity
  set c : ℝ := 2 * Real.exp (-(w ^ 2 / 2) / (Db + Mb * w / 3)) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hsub : {ξ : V → ℝ | ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
        u < RWRS.fluctuation G (zetaField ρ M m t ξ) m n X}
      ⊆ ⋃ q ∈ dyadicIdx k,
          {ξ : V → ℝ | w < |dyadicInc G (zetaField ρ M m t ξ) m q X|} := by
    intro ξ hξ
    have hmem := block_gt_subset (G := G) m u X k hξ
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hmem ⊢
    exact hmem
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hterm : ∀ q ∈ dyadicIdx k,
      RWRS.iidLaw V ρ {ξ : V → ℝ | w < |dyadicInc G (zetaField ρ M m t ξ) m q X|}
        ≤ ENNReal.ofReal c := by
    intro q hq
    refine le_trans (measure_mono (fun ξ hξ => ?_))
      (meas_fluctOn_zetaField_ge hBer ht (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X Mb Db hMb hDb
        (hbd q hq) (hvar q hq) w hw)
    have hξ' : w < |dyadicInc G (zetaField ρ M m t ξ) m q X| := hξ
    exact le_of_lt hξ'
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((dyadicIdx k).card : ℝ≥0∞) ≤ (((k + 1) * 2 ^ (k + 1) : ℕ) : ℝ≥0∞) := by
    exact_mod_cast dyadicIdx_card_le k
  refine le_trans (mul_le_mul_left hcard _) (le_of_eq ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- **The probability that the block variable of the recentred field is
positive.** -/
theorem meas_zero_lt_dyadicY_zetaField_le [IsProbabilityMeasure ρ]
    (hBer : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
          B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
    {M m : ℝ} {t : V → ℝ} (ht : ∀ v : V, -M ≤ t v) (hm : m < 0)
    (X : ℕ → V) (d k : ℕ) (hd : 0 < d)
    (Mb Db : ℝ) (hMb : 0 < Mb) (hDb : 0 ≤ Db)
    (hbd : ∀ q ∈ dyadicIdx k,
      ∀ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X, ∀ z : ℝ,
        |incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v
          * (siteShift ρ M m (t v) z - m)| ≤ Mb)
    (hvar : ∀ q ∈ dyadicIdx k,
      ∑ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X,
        incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v ^ 2
          * ∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ ≤ Db) :
    RWRS.iidLaw V ρ {ξ : V → ℝ | 0 < RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X}
      ≤ ENNReal.ofReal (((k : ℝ) + 1) * 2 ^ (k + 1)
          * (2 * Real.exp (-((|m| / (d : ℝ) * 2 ^ k / ((k : ℝ) + 1)) ^ 2 / 2)
              / (Db + Mb * (|m| / (d : ℝ) * 2 ^ k / ((k : ℝ) + 1)) / 3)))) := by
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hu : 0 < |m| / (d : ℝ) * 2 ^ k := by
    have : 0 < |m| := abs_pos.2 (ne_of_lt hm)
    positivity
  have hset : {ξ : V → ℝ | 0 < RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X}
      = {ξ : V → ℝ | ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          |m| / (d : ℝ) * 2 ^ k < RWRS.fluctuation G (zetaField ρ M m t ξ) m n X} := by
    ext ξ
    exact zero_lt_dyadicY_iff _ m d k X
  rw [hset]
  exact meas_block_gt_zetaField_le hBer ht X k hu Mb Db hMb hDb hbd hvar

end RWRS.Support
