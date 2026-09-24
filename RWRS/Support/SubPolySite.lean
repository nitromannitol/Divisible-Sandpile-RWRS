/-
Step 2 of `prop:poly-growth`: the site-dependent truncation and the recentring.

`rwrs.tex:1265`: the proposition conditions the scenery on the event
`G = {ξ(v) ≤ M_0 ∨ dist(o,v)^β for all v}`, on which the coordinates stay
independent, and recentres each one at its conditional mean, which is at most
the unconditional mean.  Here the same effect is obtained without conditioning,
by reading each coordinate through a site-dependent map: `siteVal M t` truncates
the mass below at `-M` and above at the site's level `t`, and `siteShift`
recentres it so that the recentred field has the SAME mean `m` at every site.
The recentred field dominates the original one on the scenery event, so the
payoff it produces dominates the payoff of the original scenery there, and its
coordinates are bounded by `t + M`, independent, and centred at `m`, which is
exactly what Bernstein's inequality asks for.
-/
import RWRS.Support.SubPolyPrep

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The mass truncated below at `-M` and above at the level `t`. -/
noncomputable def siteVal (M t z : ℝ) : ℝ := min (lowTrunc M z) t

/-- The mean of the truncated mass under the marginal. -/
noncomputable def siteMean (ρ : Measure ℝ) (M t : ℝ) : ℝ := ∫ z, siteVal M t z ∂ρ

/-- The coordinate map of Step 2: truncate at the site's level and recentre so
that the mean is the global mean `m`. -/
noncomputable def siteShift (ρ : Measure ℝ) (M m t z : ℝ) : ℝ :=
  siteVal M t z - siteMean ρ M t + m

theorem measurable_siteVal (M t : ℝ) : Measurable (siteVal M t) :=
  (measurable_lowTrunc M).min measurable_const

theorem measurable_siteShift (ρ : Measure ℝ) (M m t : ℝ) : Measurable (siteShift ρ M m t) :=
  ((measurable_siteVal M t).sub measurable_const).add measurable_const

theorem neg_le_siteVal {M t : ℝ} (ht : -M ≤ t) (z : ℝ) : -M ≤ siteVal M t z :=
  le_min (le_max_right _ _) ht

theorem siteVal_le (M t z : ℝ) : siteVal M t z ≤ t := min_le_right _ _

theorem abs_siteVal_le {M t : ℝ} (ht : -M ≤ t) (z : ℝ) :
    |siteVal M t z| ≤ max t M := by
  rw [abs_le]
  refine ⟨?_, le_trans (siteVal_le M t z) (le_max_left _ _)⟩
  have h1 : -M ≤ siteVal M t z := neg_le_siteVal ht z
  have h2 : -max t M ≤ -M := by
    have : M ≤ max t M := le_max_right _ _
    linarith
  linarith

/-- The truncated mass is bounded, hence integrable against a probability
measure. -/
theorem integrable_siteVal (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M t : ℝ}
    (ht : -M ≤ t) : Integrable (siteVal M t) ρ := by
  refine Integrable.mono' (integrable_const (max t M))
    (measurable_siteVal M t).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs_siteVal_le ht z

theorem neg_le_siteMean (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M t : ℝ}
    (ht : -M ≤ t) : -M ≤ siteMean ρ M t := by
  have h := integral_mono (integrable_const (-M)) (integrable_siteVal ρ ht)
    (fun z => neg_le_siteVal ht z)
  rwa [integral_const, probReal_univ, one_smul] at h

theorem siteMean_le_level (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M t : ℝ}
    (ht : -M ≤ t) : siteMean ρ M t ≤ t := by
  have h := integral_mono (integrable_siteVal ρ ht) (integrable_const t)
    (fun z => siteVal_le M t z)
  rwa [integral_const, probReal_univ, one_smul] at h

/-- The recentred coordinate is bounded by the site's level plus the lower
truncation level. -/
theorem abs_siteShift_sub_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M m t : ℝ}
    (ht : -M ≤ t) (z : ℝ) :
    |siteShift ρ M m t z - m| ≤ t + M := by
  have h1 : -M ≤ siteVal M t z := neg_le_siteVal ht z
  have h2 : siteVal M t z ≤ t := siteVal_le M t z
  have h3 : -M ≤ siteMean ρ M t := neg_le_siteMean ρ ht
  have h4 : siteMean ρ M t ≤ t := siteMean_le_level ρ ht
  have hval : siteShift ρ M m t z - m = siteVal M t z - siteMean ρ M t := by
    unfold siteShift; ring
  rw [hval, abs_le]
  constructor <;> linarith

theorem siteShift_sub (ρ : Measure ℝ) (M m t z : ℝ) :
    siteShift ρ M m t z - m = siteVal M t z - siteMean ρ M t := by
  unfold siteShift; ring

/-- The recentred coordinate has mean `m`. -/
theorem integral_siteShift_sub (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M m t : ℝ}
    (ht : -M ≤ t) :
    ∫ z, (siteShift ρ M m t z - m) ∂ρ = 0 := by
  have hcong : (fun z => siteShift ρ M m t z - m)
      = fun z => siteVal M t z - siteMean ρ M t := by
    funext z; exact siteShift_sub ρ M m t z
  rw [hcong, integral_sub (integrable_siteVal ρ ht) (integrable_const _),
    integral_const, probReal_univ, one_smul, siteMean, sub_self]

theorem integrable_siteShift_sub (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M m t : ℝ}
    (ht : -M ≤ t) : Integrable (fun z => siteShift ρ M m t z - m) ρ := by
  have hcong : (fun z => siteShift ρ M m t z - m)
      = fun z => siteVal M t z - siteMean ρ M t := by
    funext z; exact siteShift_sub ρ M m t z
  rw [hcong]
  exact (integrable_siteVal ρ ht).sub (integrable_const _)

theorem integrable_sq_siteShift_sub (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M m t : ℝ}
    (ht : -M ≤ t) :
    Integrable (fun z => (siteShift ρ M m t z - m) ^ 2) ρ := by
  refine Integrable.mono' (integrable_const ((t + M) ^ 2))
    (((measurable_siteShift ρ M m t).sub measurable_const).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := abs_siteShift_sub_le ρ (m := m) ht z
  have h2 : (0:ℝ) ≤ t + M := le_trans (abs_nonneg _) h1
  nlinarith [abs_nonneg (siteShift ρ M m t z - m), sq_abs (siteShift ρ M m t z - m)]

/-- **The recentred field dominates the scenery on the scenery event.**  If the
mass at a site is below the site's level, the recentred value is at least the
mass. -/
theorem le_siteShift_of_le (ρ : Measure ℝ) {M m t z : ℝ}
    (hc : siteMean ρ M t ≤ m) (hz : z ≤ t) : z ≤ siteShift ρ M m t z := by
  have hlow : z ≤ lowTrunc M z := le_lowTrunc M z
  have hval : z ≤ siteVal M t z := le_min hlow hz
  unfold siteShift
  linarith

/-! ### The moments of the recentred coordinate -/

/-- A finite `p`-th absolute moment makes the `p`-th absolute power
integrable. -/
theorem integrable_abs_rpow (ρ : Measure ℝ) {p : ℝ} (h : RWRS.absMoment ρ p ≠ ⊤) :
    Integrable (fun z : ℝ => |z| ^ p) ρ := by
  refine ⟨(measurable_id.abs.pow_const p).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg z) p)]
  exact lt_of_le_of_ne le_top h

/-- A finite `p`-th absolute moment with `p ≥ 1` makes the mass integrable. -/
theorem integrable_abs_of_absMoment (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {p : ℝ}
    (hp : 1 ≤ p) (h : RWRS.absMoment ρ p ≠ ⊤) : Integrable (fun z : ℝ => |z|) ρ := by
  have hI := integrable_abs_rpow ρ h
  refine Integrable.mono' ((integrable_const (1:ℝ)).add hI)
    measurable_id.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  simp only [Pi.add_apply]
  rcases le_or_gt |z| 1 with hz | hz
  · have : (0:ℝ) ≤ |z| ^ p := Real.rpow_nonneg (abs_nonneg z) p
    linarith
  · have h1 : |z| ^ (1:ℝ) ≤ |z| ^ p := Real.rpow_le_rpow_of_exponent_le hz.le hp
    rw [Real.rpow_one] at h1
    linarith

/-- Below the square exponent a sum of two nonnegative reals has its power
controlled by four times the sum of the powers. -/
theorem add_rpow_le_four (a b p : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    (a + b) ^ p ≤ 4 * (a ^ p + b ^ p) := by
  have hmax : (0:ℝ) ≤ max a b := le_max_of_le_left ha
  have hstep : a + b ≤ 2 * max a b := by
    have h1 : a ≤ max a b := le_max_left a b
    have h2 : b ≤ max a b := le_max_right a b
    linarith
  have h1 : (a + b) ^ p ≤ (2 * max a b) ^ p :=
    Real.rpow_le_rpow (by linarith) hstep (by linarith)
  have h2 : (2 * max a b) ^ p = 2 ^ p * (max a b) ^ p := Real.mul_rpow (by norm_num) hmax
  have h3 : (2:ℝ) ^ p ≤ 4 := by
    have hle : (2:ℝ) ^ p ≤ (2:ℝ) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
    have h4 : (2:ℝ) ^ (2:ℝ) = 4 := by
      rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    linarith
  have hap : (0:ℝ) ≤ a ^ p := Real.rpow_nonneg ha p
  have hbp : (0:ℝ) ≤ b ^ p := Real.rpow_nonneg hb p
  have h5 : (max a b) ^ p ≤ a ^ p + b ^ p := by
    rcases max_cases a b with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]; linarith
    · rw [he]; linarith
  have hmp : (0:ℝ) ≤ (max a b) ^ p := Real.rpow_nonneg hmax p
  calc (a + b) ^ p ≤ 2 ^ p * (max a b) ^ p := by rw [← h2]; exact h1
    _ ≤ 4 * (max a b) ^ p := by nlinarith
    _ ≤ 4 * (a ^ p + b ^ p) := by linarith

/-- **The `p`-th moment of the recentred coordinate is bounded uniformly in the
site's level**, for `p ≤ 2`. -/
theorem exists_moment_bound (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M m p : ℝ}
    (hM : 0 ≤ M) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (habs : RWRS.absMoment ρ p ≠ ⊤) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ t : ℝ, -M ≤ t →
      ∫ z, |siteShift ρ M m t z - m| ^ p ∂ρ ≤ Cm := by
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hI : Integrable (fun z : ℝ => |z| ^ p) ρ := integrable_abs_rpow ρ habs
  have hA : Integrable (fun z : ℝ => |z|) ρ := integrable_abs_of_absMoment ρ hp1 habs
  set A : ℝ := ∫ y, |y| ∂ρ with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun y => abs_nonneg y
  set K : ℝ := 2 * M + A with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; linarith
  refine ⟨4 * ((∫ z, |z| ^ p ∂ρ) + K ^ p), by positivity, ?_⟩
  intro t ht
  have hbd : ∀ z : ℝ, |siteShift ρ M m t z - m| ≤ |z| + K := by
    intro z
    have hptw : |siteVal M t z| ≤ |z| + M := by
      have h1 : -M ≤ siteVal M t z := neg_le_siteVal ht z
      have h2 : siteVal M t z ≤ max z (-M) := min_le_left _ _
      have h3 : max z (-M) ≤ |z| + M :=
        max_le (by linarith [le_abs_self z]) (by linarith [abs_nonneg z])
      rw [abs_le]
      exact ⟨by linarith [abs_nonneg z], by linarith⟩
    have hmean : |siteMean ρ M t| ≤ A + M := by
      have hle : |∫ z, siteVal M t z ∂ρ| ≤ ∫ z, |siteVal M t z| ∂ρ :=
        abs_integral_le_integral_abs
      have hmono : ∫ z, |siteVal M t z| ∂ρ ≤ ∫ z, (|z| + M) ∂ρ :=
        integral_mono ((integrable_siteVal ρ ht).abs) (hA.add (integrable_const M))
          (fun z => by
            have h1 : -M ≤ siteVal M t z := neg_le_siteVal ht z
            have h2 : siteVal M t z ≤ max z (-M) := min_le_left _ _
            have h3 : max z (-M) ≤ |z| + M :=
        max_le (by linarith [le_abs_self z]) (by linarith [abs_nonneg z])
            rw [abs_le]
            exact ⟨by linarith [abs_nonneg z], by linarith⟩)
      have hval : ∫ z, (|z| + M) ∂ρ = A + M := by
        rw [integral_add hA (integrable_const M), integral_const, probReal_univ, one_smul]
      rw [siteMean]
      linarith
    rw [siteShift_sub]
    have h2 : |siteVal M t z - siteMean ρ M t| ≤ |siteVal M t z| + |siteMean ρ M t| :=
      abs_sub _ _
    rw [hKdef]
    linarith
  have hstep : ∀ z : ℝ, |siteShift ρ M m t z - m| ^ p ≤ 4 * (|z| ^ p + K ^ p) := by
    intro z
    refine le_trans (Real.rpow_le_rpow (abs_nonneg _) (hbd z) hp0.le) ?_
    exact add_rpow_le_four |z| K p (abs_nonneg z) hK0 hp1 hp2
  have hint : Integrable (fun z : ℝ => |siteShift ρ M m t z - m| ^ p) ρ := by
    refine Integrable.mono' ((hI.add (integrable_const (K ^ p))).const_mul 4)
      ((((measurable_siteShift ρ M m t).sub measurable_const).abs).pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    exact hstep z
  calc ∫ z, |siteShift ρ M m t z - m| ^ p ∂ρ
      ≤ ∫ z, 4 * (|z| ^ p + K ^ p) ∂ρ :=
        integral_mono hint ((hI.add (integrable_const _)).const_mul 4) hstep
    _ = 4 * ((∫ z, |z| ^ p ∂ρ) + K ^ p) := by
        rw [integral_const_mul, integral_add hI (integrable_const _), integral_const,
          probReal_univ, one_smul]

/-- Below the square exponent, a bounded variable has its second moment
controlled by its `p`-th absolute moment. -/
theorem integral_sq_le_rpow (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {g : ℝ → ℝ}
    (hg : Measurable g) {K p : ℝ} (hK : 0 < K) (hp2 : p ≤ 2)
    (hbd : ∀ z : ℝ, |g z| ≤ K) (hint : Integrable (fun z : ℝ => |g z| ^ p) ρ) :
    ∫ z, g z ^ 2 ∂ρ ≤ K ^ (2 - p) * ∫ z, |g z| ^ p ∂ρ := by
  have hK0 : (0:ℝ) ≤ K := hK.le
  have hpt : ∀ z : ℝ, g z ^ 2 ≤ K ^ (2 - p) * |g z| ^ p := by
    intro z
    rcases eq_or_lt_of_le (abs_nonneg (g z)) with h0 | h0
    · have hz : g z = 0 := abs_eq_zero.1 h0.symm
      rw [hz]
      have hnn : (0:ℝ) ≤ K ^ (2 - p) * |(0:ℝ)| ^ p := by positivity
      simpa using hnn
    · have hsplit : |g z| ^ (2:ℝ) = |g z| ^ (2 - p) * |g z| ^ p := by
        rw [← Real.rpow_add h0]
        ring_nf
      have hle : |g z| ^ (2 - p) ≤ K ^ (2 - p) :=
        Real.rpow_le_rpow (abs_nonneg _) (hbd z) (by linarith)
      have hsq : g z ^ 2 = |g z| ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
      rw [hsq, hsplit]
      exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg (abs_nonneg _) p)
  have hsqint : Integrable (fun z : ℝ => g z ^ 2) ρ := by
    refine Integrable.mono' (hint.const_mul (K ^ (2 - p))) (hg.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt z
  calc ∫ z, g z ^ 2 ∂ρ ≤ ∫ z, K ^ (2 - p) * |g z| ^ p ∂ρ :=
        integral_mono hsqint (hint.const_mul _) hpt
    _ = K ^ (2 - p) * ∫ z, |g z| ^ p ∂ρ := integral_const_mul _ _

/-- **The variance bound of Step 4**: the second moment of the recentred
coordinate grows at most like the `(2-p)`-th power of the site's level. -/
theorem integral_sq_siteShift_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {M m p Cm t : ℝ}
    (hM : 0 ≤ M) (hp1 : 1 ≤ p) (hp2 : p ≤ 2) (ht : -M ≤ t) (hpos : 0 < t + M)
    (habs : RWRS.absMoment ρ p ≠ ⊤)
    (hCm : ∫ z, |siteShift ρ M m t z - m| ^ p ∂ρ ≤ Cm) :
    ∫ z, (siteShift ρ M m t z - m) ^ 2 ∂ρ ≤ (t + M) ^ (2 - p) * Cm := by
  have hp0 : (0:ℝ) < p := lt_of_lt_of_le zero_lt_one hp1
  have hI : Integrable (fun z : ℝ => |z| ^ p) ρ := integrable_abs_rpow ρ habs
  have hA : Integrable (fun z : ℝ => |z|) ρ := integrable_abs_of_absMoment ρ hp1 habs
  set A : ℝ := ∫ y, |y| ∂ρ with hAdef
  have hA0 : 0 ≤ A := integral_nonneg fun y => abs_nonneg y
  set K : ℝ := 2 * M + A with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; linarith
  have hbdz : ∀ z : ℝ, |siteShift ρ M m t z - m| ≤ |z| + K := by
    intro z
    have hptw : |siteVal M t z| ≤ |z| + M := by
      have h1 : -M ≤ siteVal M t z := neg_le_siteVal ht z
      have h2 : siteVal M t z ≤ max z (-M) := min_le_left _ _
      have h3 : max z (-M) ≤ |z| + M :=
        max_le (by linarith [le_abs_self z]) (by linarith [abs_nonneg z])
      rw [abs_le]
      exact ⟨by linarith [abs_nonneg z], by linarith⟩
    have hmean : |siteMean ρ M t| ≤ A + M := by
      have hle : |∫ z, siteVal M t z ∂ρ| ≤ ∫ z, |siteVal M t z| ∂ρ :=
        abs_integral_le_integral_abs
      have hmono : ∫ z, |siteVal M t z| ∂ρ ≤ ∫ z, (|z| + M) ∂ρ :=
        integral_mono ((integrable_siteVal ρ ht).abs) (hA.add (integrable_const M))
          (fun z => by
            have h1 : -M ≤ siteVal M t z := neg_le_siteVal ht z
            have h2 : siteVal M t z ≤ max z (-M) := min_le_left _ _
            have h3 : max z (-M) ≤ |z| + M :=
              max_le (by linarith [le_abs_self z]) (by linarith [abs_nonneg z])
            rw [abs_le]
            exact ⟨by linarith [abs_nonneg z], by linarith⟩)
      have hval : ∫ z, (|z| + M) ∂ρ = A + M := by
        rw [integral_add hA (integrable_const M), integral_const, probReal_univ, one_smul]
      rw [siteMean]
      linarith
    rw [siteShift_sub]
    have h2 : |siteVal M t z - siteMean ρ M t| ≤ |siteVal M t z| + |siteMean ρ M t| :=
      abs_sub _ _
    rw [hKdef]
    linarith
  have hint : Integrable (fun z : ℝ => |siteShift ρ M m t z - m| ^ p) ρ := by
    refine Integrable.mono' ((hI.add (integrable_const (K ^ p))).const_mul 4)
      ((((measurable_siteShift ρ M m t).sub measurable_const).abs).pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) p)]
    refine le_trans (Real.rpow_le_rpow (abs_nonneg _) (hbdz z) hp0.le) ?_
    exact add_rpow_le_four |z| K p (abs_nonneg z) hK0 hp1 hp2
  have hbd : ∀ z : ℝ, |siteShift ρ M m t z - m| ≤ t + M := fun z =>
    abs_siteShift_sub_le ρ ht z
  have hmain := integral_sq_le_rpow ρ
    ((measurable_siteShift ρ M m t).sub measurable_const) hpos hp2 hbd hint
  have hpow : (0:ℝ) ≤ (t + M) ^ (2 - p) := Real.rpow_nonneg hpos.le _
  exact le_trans hmain (mul_le_mul_of_nonneg_left hCm hpow)

end RWRS.Support
