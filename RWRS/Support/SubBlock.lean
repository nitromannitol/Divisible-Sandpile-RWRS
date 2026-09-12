/-
The union bound of `eq:Mk-tail-Ak`, for a fixed trajectory.

The chaining decomposition writes the fluctuation at any time of the `k`-th
dyadic block as a sum of at most `k+1` increments over dyadic sub-intervals of
`[0,2^{k+1})`.  There are `2^{k+1-s}` intervals at scale `s`, and `k+1` scales,
so the event that the block maximum exceeds `u` is contained in the union, over
that finite index set, of the events that one increment exceeds `u/(k+1)`.
Each of those has the polynomial tail of `lem:fuk-nagaev`, so the block maximum
does too, with the index set as the multiplicity.
-/
import RWRS.Support.SubChain

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The dyadic sub-intervals of `[0,2^{k+1})`, indexed by the scale `s ≤ k` and
the position `i < 2^{k+1-s}`. -/
def dyadicIdx (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k + 1)).biUnion fun s => (Finset.range (2 ^ (k + 1 - s))).image fun i => (s, i)

theorem mem_dyadicIdx {k s i : ℕ} (hs : s ≤ k) (hi : i < 2 ^ (k + 1 - s)) :
    (s, i) ∈ dyadicIdx k := by
  refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_range.mpr (by omega), ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩

/-- The increment over the dyadic interval of scale `s` at position `i`. -/
noncomputable def dyadicInc (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ) (m : ℝ)
    (p : ℕ × ℕ) (X : ℕ → V) : ℝ :=
  fluctOn G ξ m (p.2 * 2 ^ p.1) ((p.2 + 1) * 2 ^ p.1) X

/-- **The union bound of `eq:Mk-tail-Ak`, as an inclusion of events.**  If the
fluctuation exceeds `u` somewhere in the `k`-th dyadic block, then one of the
dyadic increments exceeds `u/(k+1)`. -/
theorem block_gt_subset (m u : ℝ) (X : ℕ → V) (k : ℕ) :
    {ξ : V → ℝ | ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), u < RWRS.fluctuation G ξ m n X}
      ⊆ ⋃ p ∈ dyadicIdx k,
          {ξ : V → ℝ | u / ((k : ℝ) + 1) < |dyadicInc G ξ m p X|} := by
  intro ξ hξ
  obtain ⟨n, hn, hgt⟩ := hξ
  rw [Finset.mem_Ico] at hn
  by_contra hcon
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hcon
  have hbase : |fluctOn G ξ m 0 (2 ^ k) X| ≤ u / ((k : ℝ) + 1) := by
    have := hcon (k, 0) (mem_dyadicIdx (le_refl k) (by simp))
    simpa [dyadicInc] using this
  have hsteps : ∀ j ∈ Finset.range k,
      |fluctOn G ξ m (dyTrunc k n j) (dyTrunc k n (j + 1)) X| ≤ u / ((k : ℝ) + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases dyTrunc_step hj hn.2 with hempty | ⟨i, hi, hlo, hhi⟩
    · rw [hempty]
      have : fluctOn G ξ m (dyTrunc k n j) (dyTrunc k n j) X = 0 := by
        unfold fluctOn; simp
      rw [this, abs_zero]
      have h0 : (0:ℝ) ≤ |fluctOn G ξ m 0 (2 ^ k) X| := abs_nonneg _
      linarith
    · have hmem : (k - j - 1, i) ∈ dyadicIdx k :=
        mem_dyadicIdx (by omega) (by
          have : k + 1 - (k - j - 1) = j + 2 := by omega
          rw [this]; exact hi)
      have := hcon (k - j - 1, i) hmem
      rw [hlo, hhi]
      simpa [dyadicInc] using this
  exact absurd (fluctuation_le_of_increments ξ m X hn.1 hn.2 hbase hsteps) (not_le.mpr hgt)

variable {ν : Measure ℝ}

/-- **The polynomial tail of the block maximum, for a fixed trajectory.**  The
tail of `eq:w-tail` summed over the `dyadicIdx` index set of `eq:Mk-tail-Ak`. -/
theorem meas_block_gt_le [IsProbabilityMeasure ν] {p Cp : ℝ}
    (hFN : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|} ≤ ENNReal.ofReal (Cp * Mp / t ^ p))
    (m : ℝ) (hint : Integrable (fun z : ℝ => z) ν) (hm : ∫ z, z ∂ν = m)
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤)
    (X : ℕ → V) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    RWRS.iidLaw V ν
        {ξ : V → ℝ | ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)), u < RWRS.fluctuation G ξ m n X}
      ≤ ∑ q ∈ dyadicIdx k, ENNReal.ofReal (Cp *
          (∑ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X,
            incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v ^ p
              * (RWRS.centeredMoment ν m p).toReal)
          / (u / ((k : ℝ) + 1)) ^ p) := by
  have ht : 0 < u / ((k : ℝ) + 1) := by positivity
  refine le_trans (measure_mono (block_gt_subset m u X k)) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  refine Finset.sum_le_sum fun q _ => ?_
  refine le_trans (measure_mono (fun ξ hξ => ?_))
    (meas_fluctOn_ge hFN m hint hm hp hmom (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X _ ht)
  have hξ' : u / ((k : ℝ) + 1) < |dyadicInc G ξ m q X| := hξ
  have : u / ((k : ℝ) + 1)
      ≤ |fluctOn G ξ m (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X| := le_of_lt hξ'
  exact this

/-! ### The tail of the dyadic block variable -/

/-- `Y_k` exceeds a positive level exactly when the fluctuation exceeds the
shifted level somewhere in the block. -/
theorem lt_dyadicY_iff (ξ : V → ℝ) (m : ℝ) (d k : ℕ) (X : ℕ → V) {t : ℝ} (ht : 0 < t) :
    t < RWRS.dyadicY G ξ m d k X
      ↔ ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          |m| / (d : ℝ) * 2 ^ k + t < RWRS.fluctuation G ξ m n X := by
  classical
  have hc : (0:ℝ) ≤ |m| / (d : ℝ) * 2 ^ k := by positivity
  rw [RWRS.dyadicY, iSup_mem_finset_real _ (block_nonempty k) (block_compl k)]
  rw [lt_max_iff, or_iff_left (not_lt.mpr ht.le), sub_eq_add_neg, ← sub_lt_iff_lt_add,
    lt_max_iff, or_iff_left (not_lt.mpr (by linarith : (0:ℝ) ≤ t - -(|m| / (d : ℝ) * 2 ^ k)))]
  rw [Finset.lt_sup'_iff]
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by linarith⟩
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, by linarith⟩

/-- **`eq:Mk-tail-Ak`, for a fixed trajectory**: the tail of `Y_k` at a positive
level, bounded by the Fuk--Nagaev tails of the dyadic increments. -/
theorem meas_lt_dyadicY_le [IsProbabilityMeasure ν] {p Cp : ℝ}
    (hFN : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|} ≤ ENNReal.ofReal (Cp * Mp / t ^ p))
    (m : ℝ) (hint : Integrable (fun z : ℝ => z) ν) (hm : ∫ z, z ∂ν = m)
    (hp : 1 ≤ p) (hmom : RWRS.absMoment ν p ≠ ⊤)
    (X : ℕ → V) (d k : ℕ) {t : ℝ} (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t < RWRS.dyadicY G ξ m d k X}
      ≤ ∑ q ∈ dyadicIdx k, ENNReal.ofReal (Cp *
          (∑ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X,
            incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v ^ p
              * (RWRS.centeredMoment ν m p).toReal)
          / ((|m| / (d : ℝ) * 2 ^ k + t) / ((k : ℝ) + 1)) ^ p) := by
  have hc : (0:ℝ) ≤ |m| / (d : ℝ) * 2 ^ k := by positivity
  have hu : 0 < |m| / (d : ℝ) * 2 ^ k + t := by linarith
  have hset : {ξ : V → ℝ | t < RWRS.dyadicY G ξ m d k X}
      = {ξ : V → ℝ | ∃ n ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
          |m| / (d : ℝ) * 2 ^ k + t < RWRS.fluctuation G ξ m n X} := by
    ext ξ
    exact lt_dyadicY_iff ξ m d k X ht
  rw [hset]
  exact meas_block_gt_le hFN m hint hm hp hmom X k hu

/-! ### Averaging the conditional bound over the walk, and the layer cake -/

section Joint

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- The joint law slices over the walk: the scenery being independent of it,
the probability of a joint event is the walk average of the conditional
probability. -/
theorem jointLaw_apply_slice (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : V)
    {S : Set ((V → ℝ) × (ℕ → V))} (hS : MeasurableSet S) :
    RWRS.jointLaw G ν x S
      = ∫⁻ X, RWRS.iidLaw V ν ((fun ξ => (ξ, X)) ⁻¹' S) ∂(RWRS.walkLaw G x) := by
  haveI : IsProbabilityMeasure (RWRS.walkLaw G x) := by rw [walkLaw_eq_lib]; infer_instance
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  exact Measure.prod_apply_symm hS

/-- **The layer cake for `Y_k`**: its `q`-th moment is the integral of its tail
against `q t^{q-1} dt`. -/
theorem lintegral_dyadicY_rpow_eq_tail (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℝ) (d k : ℕ) (x : V) {q : ℝ} (hq : 0 < q) :
    (∫⁻ z, ENNReal.ofReal (RWRS.dyadicY G z.1 m d k z.2 ^ q) ∂(RWRS.jointLaw G ν x))
      = ENNReal.ofReal q * ∫⁻ t in Set.Ioi (0:ℝ),
          RWRS.jointLaw G ν x {z | t < RWRS.dyadicY G z.1 m d k z.2}
            * ENNReal.ofReal (t ^ (q - 1)) := by
  refine MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul _ ?_ ?_ hq
  · exact Filter.Eventually.of_forall fun z => le_max_right _ _
  · exact (measurable_dyadicY m d k).aemeasurable

end Joint

end RWRS.Support
