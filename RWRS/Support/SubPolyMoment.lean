/-
Step 5 of `prop:poly-growth`: the `k`-th block moment of the recentred field.

`rwrs.tex:1305`: the block moment splits into a good-walk part, where the block
variable is bounded by a deterministic multiple of `N R_N^β` and is positive
only with the Bernstein probability of `eq:poly-Bernstein`, and a bad-walk part,
where the block variable is bounded by a deterministic multiple of `N^{1+β}`
because a walk cannot travel further than its own length, and the walk event has
the probability of `eq:poly-good-walk`.
-/
import RWRS.Support.SubPolyRadius

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ρ : Measure ℝ}
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- The good-walk event of `prop:poly-growth` is measurable. -/
theorem measurableSet_polyGood (o : V) (α δ : ℝ) (k R : ℕ) :
    MeasurableSet (polyGood G o α δ k R) := by
  have h2 : {X : ℕ → V | ((2 ^ (k + 1) : ℕ) : ℕ∞)
      < RWRS.exitTime (RWRS.closedBall G o R) X}
      = LatticeProb.Graph.stayIn (RWRS.closedBall G o R) (2 ^ (k + 1)) := by
    rw [LatticeProb.Graph.stayIn_eq_lt_exitTime]
    rfl
  unfold polyGood
  refine (measurableSet_goodWalk α δ k).inter ?_
  rw [h2]
  exact LatticeProb.Graph.measurableSet_stayIn _ _

/-- A nonnegative bounded variable has its mean at most the bound times the
probability that it is positive. -/
theorem lintegral_le_of_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) {B : ℝ}
    (hbd : ∀ ω, Y ω ≤ B) :
    (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ) ≤ ENNReal.ofReal B * μ {ω | 0 < Y ω} := by
  have hmeas : MeasurableSet {ω | 0 < Y ω} := measurableSet_lt measurable_const hY
  have hpt : ∀ ω, ENNReal.ofReal (Y ω)
      ≤ Set.indicator {ω | 0 < Y ω} (fun _ => ENNReal.ofReal B) ω := by
    intro ω
    by_cases h : 0 < Y ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | 0 < Y ω} from h)]
      exact ENNReal.ofReal_le_ofReal (hbd ω)
    · have hz : Y ω = 0 := le_antisymm (not_lt.1 h) (hY0 ω)
      rw [Set.indicator_of_notMem (show ω ∉ {ω | 0 < Y ω} from h), hz, ENNReal.ofReal_zero]
  calc (∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ)
      ≤ ∫⁻ ω, Set.indicator {ω | 0 < Y ω} (fun _ => ENNReal.ofReal B) ω ∂μ :=
        lintegral_mono hpt
    _ = ENNReal.ofReal B * μ {ω | 0 < Y ω} := by
        rw [MeasureTheory.lintegral_indicator hmeas, lintegral_const,
          Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

omit [MeasurableSingletonClass V] [Countable V] in
/-- Recentring the scenery is measurable on the product with path space. -/
theorem measurable_zetaField_prod (ρ : Measure ℝ) (M m : ℝ) (t : V → ℝ) :
    Measurable fun z : (V → ℝ) × (ℕ → V) =>
      ((zetaField ρ M m t z.1 : V → ℝ), (z.2 : ℕ → V)) :=
  ((measurable_zetaField ρ M m t).comp measurable_fst).prodMk measurable_snd

/-- The block variable of the recentred field is jointly measurable in the
scenery and the trajectory. -/
theorem measurable_dyadicY_zetaField (ρ : Measure ℝ) (M m : ℝ) (t : V → ℝ) (d k : ℕ) :
    Measurable fun z : (V → ℝ) × (ℕ → V) =>
      RWRS.dyadicY G (zetaField ρ M m t z.1) m d k z.2 := by
  have h := (measurable_dyadicY (G := G) m d k).comp (measurable_zetaField_prod ρ M m t)
  simpa [Function.comp_def] using h

/-- The block variable of the recentred field is measurable in the scenery, for
a fixed trajectory. -/
theorem measurable_dyadicY_zetaField_left (ρ : Measure ℝ) (M m : ℝ) (t : V → ℝ) (d k : ℕ)
    (X : ℕ → V) :
    Measurable fun ξ : V → ℝ => RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X := by
  have h := (measurable_dyadicY_zetaField (G := G) ρ M m t d k).comp
    (measurable_id.prodMk (measurable_const (a := X)))
  simpa [Function.comp_def] using h

/-- The joint integral is the walk average of the scenery average. -/
theorem lintegral_jointLaw_swap (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (o : V)
    {F : (V → ℝ) × (ℕ → V) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂(RWRS.jointLaw G ρ o))
      = ∫⁻ X, (∫⁻ ξ, F (ξ, X) ∂(RWRS.iidLaw V ρ)) ∂(RWRS.walkLaw G o) := by
  haveI : IsProbabilityMeasure (RWRS.walkLaw G o) := by rw [walkLaw_eq_lib]; infer_instance
  rw [RWRS.jointLaw]
  exact MeasureTheory.lintegral_prod_symm _ hF.aemeasurable

/-- **The `k`-th block moment of the recentred field**, split into the good-walk
and the bad-walk contributions. -/
theorem lintegral_dyadicY_zetaField_le [IsProbabilityMeasure ρ] (hdeg : ∀ v : V, 0 < G.degree v)
    {M m : ℝ} {t : V → ℝ} (o : V) {α δ : ℝ} {k R d : ℕ} {Bg pb Bb : ℝ}
    (hBg : 0 ≤ Bg)
    (hgood : ∀ X ∈ polyGood G o α δ k R, ∀ ξ : V → ℝ,
      RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X ≤ Bg)
    (hprob : ∀ X ∈ polyGood G o α δ k R,
      RWRS.iidLaw V ρ {ξ : V → ℝ | 0 < RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X}
        ≤ ENNReal.ofReal pb)
    (hbad : ∀ X : ℕ → V, (∀ j : ℕ, G.edist (X j) o ≤ (j : ℕ∞)) → ∀ ξ : V → ℝ,
      RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X ≤ Bb) :
    (∫⁻ z, ENNReal.ofReal (RWRS.dyadicY G (zetaField ρ M m t z.1) m d k z.2)
        ∂(RWRS.jointLaw G ρ o))
      ≤ ENNReal.ofReal (Bg * pb)
        + ENNReal.ofReal Bb * RWRS.walkLaw G o (polyGood G o α δ k R)ᶜ := by
  haveI : IsProbabilityMeasure (RWRS.walkLaw G o) := by rw [walkLaw_eq_lib]; infer_instance
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ρ) := instIsProbabilityMeasureIid ρ
  have hmeas := measurable_dyadicY_zetaField (G := G) ρ M m t d k
  rw [lintegral_jointLaw_swap ρ o hmeas.ennreal_ofReal]
  have hstep : ∀ᵐ X ∂(RWRS.walkLaw G o),
      (∫⁻ ξ, ENNReal.ofReal (RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X) ∂(RWRS.iidLaw V ρ))
        ≤ ENNReal.ofReal (Bg * pb)
          + Set.indicator (polyGood G o α δ k R)ᶜ (fun _ => ENNReal.ofReal Bb) X := by
    filter_upwards [ae_edist_le hdeg o] with X hX
    by_cases hg : X ∈ polyGood G o α δ k R
    · have hb := lintegral_le_of_bound (RWRS.iidLaw V ρ)
        (fun ξ => RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X)
        (measurable_dyadicY_zetaField_left ρ M m t d k X)
        (fun ξ => le_max_right _ _) (hgood X hg)
      refine le_trans (le_trans hb ?_) le_self_add
      calc ENNReal.ofReal Bg
            * RWRS.iidLaw V ρ {ξ : V → ℝ | 0 < RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X}
          ≤ ENNReal.ofReal Bg * ENNReal.ofReal pb :=
            mul_le_mul_right (hprob X hg) _
        _ = ENNReal.ofReal (Bg * pb) := (ENNReal.ofReal_mul hBg).symm
    · have hb : ∀ ξ : V → ℝ, RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X ≤ Bb :=
        hbad X hX
      have hle : (∫⁻ ξ, ENNReal.ofReal (RWRS.dyadicY G (zetaField ρ M m t ξ) m d k X)
          ∂(RWRS.iidLaw V ρ)) ≤ ENNReal.ofReal Bb := by
        refine le_trans (lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal (hb ξ)) ?_
        rw [lintegral_const, measure_univ, mul_one]
      rw [Set.indicator_of_mem (show X ∈ (polyGood G o α δ k R)ᶜ from hg)]
      exact le_trans hle le_add_self
  refine le_trans (lintegral_mono_ae hstep) (le_of_eq ?_)
  rw [lintegral_add_left measurable_const,
    MeasureTheory.lintegral_indicator (measurableSet_polyGood o α δ k R).compl,
    setLIntegral_const, lintegral_const, measure_univ, mul_one]

end RWRS.Support
