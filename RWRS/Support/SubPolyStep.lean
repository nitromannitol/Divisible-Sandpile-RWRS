/-
Steps 4 and 5 of `prop:poly-growth`, instantiated at the levels of Step 1.

`rwrs.tex:1288-1305`: on the good-walk event the trajectory stays inside the
ball of radius `R_N` up to time `N = 2^{k+1}`, so every recentred coordinate it
reads is bounded by `M_0 ∨ R_N^β` plus the lower truncation level, the weights
are bounded by `N^{α+δ}` and the total variance of an increment by
`C(M_0 ∨ R_N^β)^{2-p}N^{α+δ}N`.  Those are the two constants of the Bernstein
bound `eq:poly-Bernstein`, and with them the `k`-th block moment splits into the
good-walk part, of size `NR_N^β` times the Bernstein probability, and the
bad-walk part, of size `N^{1+β}` times the probability of the bad walk.
-/
import RWRS.Support.SubPolyScenery

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ρ : Measure ℝ}

/-- The largest level a trajectory can meet inside a ball, plus the lower
truncation level. -/
noncomputable def polyCap (M0 β M : ℝ) (R : ℕ) : ℝ := max M0 ((R : ℝ) ^ β) + M

theorem one_le_polyCap {M0 β M : ℝ} (hM0 : 1 ≤ M0) (hM : 0 ≤ M) (R : ℕ) :
    1 ≤ polyCap M0 β M R := by
  have h1 : M0 ≤ max M0 ((R : ℝ) ^ β) := le_max_left _ _
  rw [polyCap]
  linarith

theorem polyCap_pos {M0 β M : ℝ} (hM0 : 1 ≤ M0) (hM : 0 ≤ M) (R : ℕ) :
    0 < polyCap M0 β M R :=
  lt_of_lt_of_le zero_lt_one (one_le_polyCap hM0 hM R)

/-- A dyadic sub-interval of the `k`-th block ends before the block does. -/
theorem dyadicIdx_le {k : ℕ} {q : ℕ × ℕ} (hq : q ∈ dyadicIdx k) :
    (q.2 + 1) * 2 ^ q.1 ≤ 2 ^ (k + 1) := by
  unfold dyadicIdx at hq
  rw [Finset.mem_biUnion] at hq
  obtain ⟨s, hs, hq2⟩ := hq
  rw [Finset.mem_image] at hq2
  obtain ⟨i, hi, rfl⟩ := hq2
  rw [Finset.mem_range] at hs hi
  calc (i + 1) * 2 ^ s ≤ 2 ^ (k + 1 - s) * 2 ^ s := Nat.mul_le_mul_right _ hi
    _ = 2 ^ (k + 1 - s + s) := (pow_add 2 _ _).symm
    _ = 2 ^ (k + 1) := by
        congr 1
        omega

/-- **The variance of an increment on the good-walk event**, with the per-site
variances bounded only at the sites the increment reads. -/
theorem sum_incWeight_sq_var_le' [IsProbabilityMeasure ρ] (hdeg : ∀ v : V, 1 ≤ G.degree v)
    {M m : ℝ} {t : V → ℝ} {α δ S : ℝ} {k a b : ℕ} (hb : b ≤ 2 ^ (k + 1)) {X : ℕ → V}
    (hX : X ∈ RWRS.goodWalk (V := V) α δ k) (hS : 0 ≤ S)
    (hvar : ∀ v ∈ walkSites a b X, (∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ) ≤ S) :
    ∑ v ∈ walkSites a b X, incWeight G a b X v ^ 2
        * ∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ
      ≤ S * ((2 ^ (k + 1) : ℝ) ^ (α + δ) * (2 ^ (k + 1) : ℝ)) := by
  have hterm : ∀ v ∈ walkSites a b X,
      incWeight G a b X v ^ 2 * ∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ
        ≤ S * incWeight G a b X v ^ 2 := by
    intro v hv
    have h0 : (0:ℝ) ≤ incWeight G a b X v ^ 2 := by positivity
    have hvv := hvar v hv
    nlinarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left (sum_incWeight_sq_le_of_good hdeg hb hX) hS) ?_
  refine mul_le_mul_of_nonneg_left ?_ hS
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity) _)
  have hnat : b - a ≤ 2 ^ (k + 1) := le_trans (Nat.sub_le b a) hb
  have hcast : ((b - a : ℕ) : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
  simpa using hcast

/-- **The weight of a site inside a dyadic sub-interval of the block**, on the
good-walk event. -/
theorem incWeight_mul_siteShift_le [IsProbabilityMeasure ρ] (hdeg : ∀ v : V, 1 ≤ G.degree v)
    {M M0 β m α δ : ℝ} (hM : 0 ≤ M) (hM0 : 1 ≤ M0) (hβ : 0 ≤ β)
    {o : V} {k R : ℕ} {X : ℕ → V} (hX : X ∈ polyGood G o α δ k R)
    {q : ℕ × ℕ} (hq : q ∈ dyadicIdx k) :
    ∀ v ∈ walkSites (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X, ∀ z : ℝ,
      |incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X v
          * (siteShift ρ M m (polyLevel G o M0 β v) z - m)|
        ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) * polyCap M0 β M R := by
  intro v hv z
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
  rw [Finset.mem_Ico] at hj
  have hb := dyadicIdx_le hq
  have hjlt : j < 2 ^ (k + 1) := lt_of_lt_of_le hj.2 hb
  have hball : X j ∈ RWRS.closedBall G o R := mem_closedBall_of_polyGood hX hjlt
  have hlev : polyLevel G o M0 β (X j) ≤ max M0 ((R : ℝ) ^ β) :=
    polyLevel_le_of_edist_le hβ hball
  have hMM0 : -M ≤ M0 := by linarith
  have hnum : |siteShift ρ M m (polyLevel G o M0 β (X j)) z - m|
      ≤ polyLevel G o M0 β (X j) + M :=
    abs_siteShift_sub_le ρ (neg_le_polyLevel hMM0 β o (X j)) z
  have hw : incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X (X j)
      ≤ (2 ^ (k + 1) : ℝ) ^ (α + δ) :=
    incWeight_le_of_good hdeg hb (polyGood_subset_goodWalk o α δ k R hX) (X j)
  have hw0 : (0:ℝ) ≤ incWeight G (q.2 * 2 ^ q.1) ((q.2 + 1) * 2 ^ q.1) X (X j) :=
    incWeight_nonneg _ _ _ _
  have hcap : polyLevel G o M0 β (X j) + M ≤ polyCap M0 β M R := by
    rw [polyCap]
    linarith
  rw [abs_mul, abs_of_nonneg hw0]
  exact mul_le_mul hw (le_trans hnum hcap) (abs_nonneg _)
    (Real.rpow_nonneg (by positivity) _)

/-- A site the trajectory reads inside the ball carries a level below the cap. -/
theorem polyLevel_add_le_polyCap {M M0 β α δ : ℝ} (_hM : 0 ≤ M) (hβ : 0 ≤ β)
    {o : V} {k R a b : ℕ} (hb : b ≤ 2 ^ (k + 1)) {X : ℕ → V}
    (hX : X ∈ polyGood G o α δ k R) {v : V} (hv : v ∈ walkSites a b X) :
    polyLevel G o M0 β v + M ≤ polyCap M0 β M R := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hv
  rw [Finset.mem_Ico] at hj
  have hjlt : j < 2 ^ (k + 1) := lt_of_lt_of_le hj.2 hb
  have hlev : polyLevel G o M0 β (X j) ≤ max M0 ((R : ℝ) ^ β) :=
    polyLevel_le_of_edist_le hβ (mem_closedBall_of_polyGood hX hjlt)
  rw [polyCap]
  linarith

/-- **The block variable on the good-walk event.** -/
theorem dyadicY_zetaField_good_le [IsProbabilityMeasure ρ] (hdeg : ∀ v : V, 1 ≤ G.degree v)
    {M M0 β m : ℝ} (hM : 0 ≤ M) (hM0 : 1 ≤ M0) (hβ : 0 ≤ β)
    {o : V} {α δ : ℝ} {k R d : ℕ} {X : ℕ → V} (hX : X ∈ polyGood G o α δ k R) (ξ : V → ℝ) :
    RWRS.dyadicY G (zetaField ρ M m (polyLevel G o M0 β) ξ) m d k X
      ≤ (2 ^ (k + 1) : ℝ) * polyCap M0 β M R := by
  rw [polyCap]
  refine dyadicY_zetaField_le (fun v => neg_le_polyLevel (by linarith) β o v) hdeg ξ d k X
    (T := max M0 ((R : ℝ) ^ β)) ?_ ?_
  · have h1 : M0 ≤ max M0 ((R : ℝ) ^ β) := le_max_left _ _
    linarith
  · intro j hj
    exact polyLevel_le_of_edist_le hβ (mem_closedBall_of_polyGood hX hj)

/-- **The block variable off the good-walk event**, where the trajectory is
still inside the ball of radius the block length. -/
theorem dyadicY_zetaField_bad_le [IsProbabilityMeasure ρ] (hdeg : ∀ v : V, 1 ≤ G.degree v)
    {M M0 β m : ℝ} (hM : 0 ≤ M) (hM0 : 1 ≤ M0) (hβ : 0 ≤ β)
    {o : V} {k d : ℕ} {X : ℕ → V} (hX : ∀ j : ℕ, G.edist (X j) o ≤ (j : ℕ∞)) (ξ : V → ℝ) :
    RWRS.dyadicY G (zetaField ρ M m (polyLevel G o M0 β) ξ) m d k X
      ≤ (2 ^ (k + 1) : ℝ) * polyCap M0 β M (2 ^ (k + 1)) := by
  rw [polyCap]
  refine dyadicY_zetaField_le (fun v => neg_le_polyLevel (by linarith) β o v) hdeg ξ d k X
    (T := max M0 (((2 ^ (k + 1) : ℕ) : ℝ) ^ β)) ?_ ?_
  · have h1 : M0 ≤ max M0 (((2 ^ (k + 1) : ℕ) : ℝ) ^ β) := le_max_left _ _
    linarith
  · intro j hj
    exact polyLevel_le_of_edist_le hβ (edist_le_of_lt hX hj)

/-- The Bernstein bound of `eq:poly-Bernstein` at the `k`-th scale. -/
noncomputable def polyBern (m : ℝ) (d k : ℕ) (Mb Db : ℝ) : ℝ :=
  ((k : ℝ) + 1) * 2 ^ (k + 1)
    * (2 * Real.exp (-((|m| / (d : ℝ) * 2 ^ k / ((k : ℝ) + 1)) ^ 2 / 2)
        / (Db + Mb * (|m| / (d : ℝ) * 2 ^ k / ((k : ℝ) + 1)) / 3)))

/-- **`eq:poly-Bernstein` at the levels of Step 1**: the probability that the
block variable of the recentred field is positive on the good-walk event. -/
theorem meas_zero_lt_dyadicY_polyLevel_le [IsProbabilityMeasure ρ]
    (hBer : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
          B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
    (hdeg : ∀ v : V, 1 ≤ G.degree v)
    {M M0 β m α δ Cm p2 : ℝ} (hM : 0 ≤ M) (hM0 : 1 ≤ M0) (hβ : 0 ≤ β) (hm : m < 0)
    (hCm : 0 ≤ Cm) (hp2 : 0 ≤ 2 - p2) {o : V}
    (hvarbd : ∀ v : V, (∫ z, (siteShift ρ M m (polyLevel G o M0 β v) z - m) ^ 2 ∂ρ)
        ≤ (polyLevel G o M0 β v + M) ^ (2 - p2) * Cm)
    {k R d : ℕ} (hd : 0 < d) {X : ℕ → V} (hX : X ∈ polyGood G o α δ k R) :
    RWRS.iidLaw V ρ
        {ξ : V → ℝ | 0 < RWRS.dyadicY G (zetaField ρ M m (polyLevel G o M0 β) ξ) m d k X}
      ≤ ENNReal.ofReal (polyBern m d k
          ((2 ^ (k + 1) : ℝ) ^ (α + δ) * polyCap M0 β M R)
          ((polyCap M0 β M R) ^ (2 - p2) * Cm
            * ((2 ^ (k + 1) : ℝ) ^ (α + δ) * (2 ^ (k + 1) : ℝ)))) := by
  have hcap : 0 < polyCap M0 β M R := polyCap_pos hM0 hM R
  have hrp : (0:ℝ) < (2 ^ (k + 1) : ℝ) ^ (α + δ) := Real.rpow_pos_of_pos (by positivity) _
  have hMb : (0:ℝ) < (2 ^ (k + 1) : ℝ) ^ (α + δ) * polyCap M0 β M R := by positivity
  have hS0 : (0:ℝ) ≤ (polyCap M0 β M R) ^ (2 - p2) * Cm := by positivity
  have hDb : (0:ℝ) ≤ (polyCap M0 β M R) ^ (2 - p2) * Cm
      * ((2 ^ (k + 1) : ℝ) ^ (α + δ) * (2 ^ (k + 1) : ℝ)) := by positivity
  rw [polyBern]
  refine meas_zero_lt_dyadicY_zetaField_le hBer
    (fun v => neg_le_polyLevel (by linarith) β o v) hm X d k hd _ _ hMb hDb ?_ ?_
  · intro q hq
    exact incWeight_mul_siteShift_le hdeg hM hM0 hβ hX hq
  · intro q hq
    refine sum_incWeight_sq_var_le' hdeg (dyadicIdx_le hq)
      (polyGood_subset_goodWalk o α δ k R hX) hS0 ?_
    intro v hv
    refine le_trans (hvarbd v) ?_
    refine mul_le_mul_of_nonneg_right ?_ hCm
    refine Real.rpow_le_rpow ?_ (polyLevel_add_le_polyCap hM hβ (dyadicIdx_le hq) hX hv) hp2
    have h1 : M0 ≤ polyLevel G o M0 β v := le_polyLevel G o M0 β v
    linarith

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **Step 5 of `prop:poly-growth`**: the `k`-th block moment at the levels of
Step 1, split into the good-walk and the bad-walk contributions. -/
theorem lintegral_dyadicY_polyLevel_le [IsProbabilityMeasure ρ]
    (hBer : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
          B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
    (hdeg : ∀ v : V, 1 ≤ G.degree v)
    {M M0 β m α δ Cm p2 : ℝ} (hM : 0 ≤ M) (hM0 : 1 ≤ M0) (hβ : 0 ≤ β) (hm : m < 0)
    (hCm : 0 ≤ Cm) (hp2 : 0 ≤ 2 - p2) {o : V}
    (hvarbd : ∀ v : V, (∫ z, (siteShift ρ M m (polyLevel G o M0 β v) z - m) ^ 2 ∂ρ)
        ≤ (polyLevel G o M0 β v + M) ^ (2 - p2) * Cm)
    {k R d : ℕ} (hd : 0 < d) :
    (∫⁻ z, ENNReal.ofReal
        (RWRS.dyadicY G (zetaField ρ M m (polyLevel G o M0 β) z.1) m d k z.2)
        ∂(RWRS.jointLaw G ρ o))
      ≤ ENNReal.ofReal ((2 ^ (k + 1) : ℝ) * polyCap M0 β M R
            * polyBern m d k ((2 ^ (k + 1) : ℝ) ^ (α + δ) * polyCap M0 β M R)
                ((polyCap M0 β M R) ^ (2 - p2) * Cm
                  * ((2 ^ (k + 1) : ℝ) ^ (α + δ) * (2 ^ (k + 1) : ℝ))))
        + ENNReal.ofReal ((2 ^ (k + 1) : ℝ) * polyCap M0 β M (2 ^ (k + 1)))
            * RWRS.walkLaw G o (polyGood G o α δ k R)ᶜ := by
  have hcap : 0 < polyCap M0 β M R := polyCap_pos hM0 hM R
  refine lintegral_dyadicY_zetaField_le (fun v => hdeg v) o
    (Bg := (2 ^ (k + 1) : ℝ) * polyCap M0 β M R)
    (pb := polyBern m d k ((2 ^ (k + 1) : ℝ) ^ (α + δ) * polyCap M0 β M R)
      ((polyCap M0 β M R) ^ (2 - p2) * Cm
        * ((2 ^ (k + 1) : ℝ) ^ (α + δ) * (2 ^ (k + 1) : ℝ))))
    (Bb := (2 ^ (k + 1) : ℝ) * polyCap M0 β M (2 ^ (k + 1)))
    (by positivity) ?_ ?_ ?_
  · intro X hX ξ
    exact dyadicY_zetaField_good_le hdeg hM hM0 hβ hX ξ
  · intro X hX
    exact meas_zero_lt_dyadicY_polyLevel_le hBer hdeg hM hM0 hβ hm hCm hp2 hvarbd hd hX
  · intro X hX ξ
    exact dyadicY_zetaField_bad_le hdeg hM hM0 hβ hX ξ

end RWRS.Support
