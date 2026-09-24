/-
The recentred field of Step 2 of `prop:poly-growth`, and the Bernstein tail of
one of its increments.

`rwrs.tex:1274`: the proposition recentres the scenery at the site's conditional
mean, obtaining a field whose coordinates are independent, centred and bounded,
and which dominates the original scenery on the scenery event; the fluctuation
of the recentred field then obeys Bernstein's inequality over every discrete
interval, conditionally on the walk.  Here the recentring is the site-dependent
map of `SubPolySite`, so the recentred field is `zetaField`, its increment over
an interval is a weighted sum of the recentred coordinates over the sites the
interval visits, and part (c) of `lem:fuk-nagaev` applies to it with the
weights of the interval.
-/
import RWRS.Support.SubPolyBern
import RWRS.Support.SubPolySite

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ρ : Measure ℝ}

/-- **The recentred field of Step 2**: the mass at `v` truncated at the site's
level `t v` and recentred so that its mean is the global mean `m`. -/
noncomputable def zetaField (ρ : Measure ℝ) (M m : ℝ) (t ξ : V → ℝ) : V → ℝ :=
  fun v => siteShift ρ M m (t v) (ξ v)

theorem zetaField_sub (ρ : Measure ℝ) (M m : ℝ) (t ξ : V → ℝ) (v : V) :
    zetaField ρ M m t ξ v - m = siteShift ρ M m (t v) (ξ v) - m := rfl

theorem measurable_zetaField (ρ : Measure ℝ) (M m : ℝ) (t : V → ℝ) :
    Measurable fun ξ : V → ℝ => zetaField ρ M m t ξ :=
  measurable_pi_lambda _ fun v => (measurable_siteShift ρ M m (t v)).comp (measurable_pi_apply v)

/-- **The recentred field dominates the scenery on the scenery event.** -/
theorem le_zetaField {M m : ℝ} {t : V → ℝ} (hc : ∀ v : V, siteMean ρ M (t v) ≤ m)
    {ξ : V → ℝ} (hξ : ∀ v, ξ v ≤ t v) (v : V) : ξ v ≤ zetaField ρ M m t ξ v :=
  le_siteShift_of_le ρ (hc v) (hξ v)

/-- The increment of the recentred field over an interval is a weighted sum of
the recentred coordinates over the sites the interval visits. -/
theorem fluctOn_zetaField (M m : ℝ) (t ξ : V → ℝ) (a b : ℕ) (X : ℕ → V) :
    fluctOn G (zetaField ρ M m t ξ) m a b X
      = ∑ v ∈ walkSites a b X,
          incWeight G a b X v * (siteShift ρ M m (t v) (ξ v) - m) :=
  fluctOn_eq_sum_sites _ _ _ _ _

/-- A weighted sum of site-dependent maps whose variance vanishes is almost
surely zero. -/
theorem ae_weighted_sum_site_eq_zero_of_var_zero [IsProbabilityMeasure ρ] (S : Finset V)
    (w : V → ℝ) {f : V → ℝ → ℝ} (hfsq : ∀ v : V, Integrable (fun z => f v z ^ 2) ρ)
    (hD : ∑ v ∈ S, w v ^ 2 * ∫ z, f v z ^ 2 ∂ρ = 0) :
    ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), ∑ v ∈ S, w v * f v (ξ v) = 0 := by
  have hterm : ∀ v ∈ S, w v ^ 2 * ∫ z, f v z ^ 2 ∂ρ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by
      have : (0:ℝ) ≤ ∫ z, f v z ^ 2 ∂ρ := integral_nonneg fun z => sq_nonneg _
      positivity)).1 hD
  have hae : ∀ v ∈ S, ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), w v * f v (ξ v) = 0 := by
    intro v hv
    rcases mul_eq_zero.1 (hterm v hv) with h | h
    · have hw : w v = 0 := by simpa using sq_eq_zero_iff.1 h
      exact Filter.Eventually.of_forall fun ξ => by rw [hw, zero_mul]
    · have hf0 : ∀ᵐ z ∂ρ, f v z = 0 := by
        have h2 := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (f v z)) (hfsq v)).1 h
        filter_upwards [h2] with z hz
        exact pow_eq_zero_iff (two_ne_zero) |>.1 hz
      have hmap : (RWRS.iidLaw V ρ).map (fun ξ : V → ℝ => ξ v) = ρ := map_eval_iidLaw ρ v
      have h3 : ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), f v (ξ v) = 0 :=
        MeasureTheory.ae_of_ae_map (measurable_pi_apply v).aemeasurable (by rw [hmap]; exact hf0)
      filter_upwards [h3] with ξ hξ
      rw [hξ, mul_zero]
  have hall : ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), ∀ v ∈ S, w v * f v (ξ v) = 0 :=
    (Filter.eventually_all_finset S).2 hae
  filter_upwards [hall] with ξ hξ
  exact Finset.sum_eq_zero hξ

/-- **The Bernstein tail with the variance bounded above**, for a weighted sum
of site-dependent maps. -/
theorem meas_weighted_sum_site_bernstein_le [IsProbabilityMeasure ρ]
    (hBer : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
          B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
    (S : Finset V) (w : V → ℝ) {f : V → ℝ → ℝ} (hf : ∀ v : V, Measurable (f v))
    (hfint : ∀ v : V, Integrable (f v) ρ) (hfsq : ∀ v : V, Integrable (fun z => f v z ^ 2) ρ)
    (hf0 : ∀ v : V, ∫ z, f v z ∂ρ = 0)
    (Mb Db : ℝ) (hMb : 0 < Mb) (hDb : 0 ≤ Db)
    (hbd : ∀ v ∈ S, ∀ z : ℝ, |w v * f v z| ≤ Mb)
    (hvar : ∑ v ∈ S, w v ^ 2 * ∫ z, f v z ^ 2 ∂ρ ≤ Db)
    (u : ℝ) (hu : 0 < u) :
    RWRS.iidLaw V ρ {ξ : V → ℝ | u ≤ |∑ v ∈ S, w v * f v (ξ v)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / 2) / (Db + Mb * u / 3))) := by
  set D : ℝ := ∑ v ∈ S, w v ^ 2 * ∫ z, f v z ^ 2 ∂ρ with hDdef
  have hD0 : (0:ℝ) ≤ D := Finset.sum_nonneg fun v _ => by
    have : (0:ℝ) ≤ ∫ z, f v z ^ 2 ∂ρ := integral_nonneg fun z => sq_nonneg _
    positivity
  rcases eq_or_lt_of_le hD0 with hD | hD
  · have hzero : ∀ᵐ ξ ∂(RWRS.iidLaw V ρ), ∑ v ∈ S, w v * f v (ξ v) = 0 :=
      ae_weighted_sum_site_eq_zero_of_var_zero S w hfsq hD.symm
    have hsub : {ξ : V → ℝ | u ≤ |∑ v ∈ S, w v * f v (ξ v)|}
        ⊆ {ξ : V → ℝ | ¬ (∑ v ∈ S, w v * f v (ξ v) = 0)} := by
      intro ξ hξ h0
      rw [Set.mem_setOf_eq, h0, abs_zero] at hξ
      exact absurd hξ (not_le.mpr hu)
    rw [measure_mono_null hsub hzero]
    exact bot_le
  · have hBpos : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
    have hB2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
    have hmain := meas_weighted_sum_ge_bernstein_site hBer S w hf hfint hfsq hf0 Mb
      (Real.sqrt D) hMb hBpos hbd (by rw [hB2]) u hu
    refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
    have hden1 : (0:ℝ) < Real.sqrt D ^ 2 + Mb * u / 3 := by
      rw [hB2]; positivity
    have hden2 : (0:ℝ) < Db + Mb * u / 3 := by positivity
    have hle : -(u ^ 2 / 2) / (Real.sqrt D ^ 2 + Mb * u / 3)
        ≤ -(u ^ 2 / 2) / (Db + Mb * u / 3) := by
      rw [neg_div, neg_div, neg_le_neg_iff]
      refine div_le_div_of_nonneg_left (by positivity) hden1 ?_
      rw [hB2]
      linarith
    have hexp := Real.exp_le_exp.2 hle
    linarith

/-- **Step 4 of `prop:poly-growth`**: the Bernstein tail of an increment of the
recentred field, conditionally on the walk. -/
theorem meas_fluctOn_zetaField_ge [IsProbabilityMeasure ρ]
    (hBer : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
          B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
    {M m : ℝ} {t : V → ℝ} (ht : ∀ v : V, -M ≤ t v)
    (a b : ℕ) (X : ℕ → V) (Mb Db : ℝ) (hMb : 0 < Mb) (hDb : 0 ≤ Db)
    (hbd : ∀ v ∈ walkSites a b X, ∀ z : ℝ,
      |incWeight G a b X v * (siteShift ρ M m (t v) z - m)| ≤ Mb)
    (hvar : ∑ v ∈ walkSites a b X, incWeight G a b X v ^ 2
        * ∫ z, (siteShift ρ M m (t v) z - m) ^ 2 ∂ρ ≤ Db)
    (u : ℝ) (hu : 0 < u) :
    RWRS.iidLaw V ρ {ξ : V → ℝ | u ≤ |fluctOn G (zetaField ρ M m t ξ) m a b X|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(u ^ 2 / 2) / (Db + Mb * u / 3))) := by
  have hset : {ξ : V → ℝ | u ≤ |fluctOn G (zetaField ρ M m t ξ) m a b X|}
      = {ξ : V → ℝ | u ≤ |∑ v ∈ walkSites a b X,
          incWeight G a b X v * (siteShift ρ M m (t v) (ξ v) - m)|} := by
    ext ξ
    simp only [Set.mem_setOf_eq, fluctOn_zetaField]
  rw [hset]
  exact meas_weighted_sum_site_bernstein_le hBer (walkSites a b X) (incWeight G a b X)
    (fun v => (measurable_siteShift ρ M m (t v)).sub measurable_const)
    (fun v => integrable_siteShift_sub ρ (ht v))
    (fun v => integrable_sq_siteShift_sub ρ (ht v))
    (fun v => integral_siteShift_sub ρ (ht v))
    Mb Db hMb hDb hbd hvar u hu

end RWRS.Support
