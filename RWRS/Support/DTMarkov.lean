import RWRS.Support.DTStopMeas
import LatticeProb.Graph.MarkovAE
import LatticeProb.Graph.PathSpace

open LatticeProb LatticeProb.Graph MeasureTheory
open scoped ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **The strong Markov property for indicators.**  For a stopping time
`τ`, finite almost surely, the lintegral of the indicator of a measurable
set along the shifted trajectory equals the iterated lintegral through the
walk restarted at the stopping position. -/
theorem lintegral_indicator_markov_stop (hdeg : ∀ v : V, 0 < G.degree v)
    (x : V) (τ : (ℕ → V) → ℕ∞) (hτ : IsWalkStoppingE τ)
    (hfin : ∀ᵐ X ∂(walkLaw G x), τ X ≠ ⊤) (A : Set (ℕ → V)) (hAm : MeasurableSet A) :
    ∫⁻ X, Set.indicator A (fun _ => (1 : ℝ≥0∞)) (shiftPath (τ X).toNat X)
        ∂(walkLaw G x)
      = ∫⁻ X, (∫⁻ Y, Set.indicator A (fun _ => (1 : ℝ≥0∞)) Y
          ∂(walkLaw G (X ((τ X).toNat)))) ∂(walkLaw G x) := by
  classical
  set S : Set (ℕ → V) := {X | shiftPath (τ X).toNat X ∈ A} with hS
  have hSm : MeasurableSet S := hAm.preimage (measurable_shiftPath_stop τ hτ)
  set F : (ℕ → V) → ℝ := fun X => Set.indicator A (fun _ => (1 : ℝ)) X with hF
  have hFm : Measurable F := Measurable.indicator measurable_const hAm
  have hFb : ∀ X, ‖F X‖ ≤ 1 := by
    intro X
    by_cases h : X ∈ A <;> simp [hF, h]
  have hHdep : ∀ (k : ℕ) (X Y : ℕ → V), (∀ j ≤ k, X j = Y j) →
      τ X = (k : ℕ∞) → (1 : ℝ) = (1 : ℝ) := fun _ _ _ _ _ => rfl
  have hmain := markov_stopping_ae hdeg x τ hτ hfin F hFm 1 hFb
    (fun _ => (1 : ℝ)) 1 (fun X => by simp) hHdep
  simp only [mul_one] at hmain
  have hLi : ∫⁻ X, Set.indicator A (fun X => (1 : ℝ≥0∞))
      (shiftPath (τ X).toNat X) ∂(walkLaw G x)
      = (walkLaw G x) S := by
    have hfun : ∀ X : ℕ → V, Set.indicator A (fun _ => (1 : ℝ≥0∞))
        (shiftPath (τ X).toNat X)
        = Set.indicator S (fun _ => (1 : ℝ≥0∞)) X := fun X => rfl
    rw [lintegral_congr hfun]
    exact lintegral_indicator_one hSm
  have hRi : ∀ y : V, (∫⁻ Y, Set.indicator A (fun _ => (1 : ℝ≥0∞)) Y
      ∂(walkLaw G y)) = (walkLaw G y) A :=
    fun y => lintegral_indicator_one hAm
  have hLle : ((walkLaw G x) S) ≤ 1 := by
    refine le_trans (measure_mono fun X _ => Set.mem_univ X) ?_
    simp
  have hone : ∀ y : V, (walkLaw G y) A ≤ 1 := fun y =>
    le_trans (measure_mono fun X _ => Set.mem_univ X) (by simp)
  have hRle : (∫⁻ X, (∫⁻ Y, Set.indicator A (fun _ => (1 : ℝ≥0∞)) Y
      ∂(walkLaw G (X ((τ X).toNat)))) ∂(walkLaw G x)) ≤ 1 :=
    le_trans (lintegral_mono fun X => (hRi _).symm ▸ hone _)
      (by rw [lintegral_one]; simp)
  rw [hLi]
  refine (ENNReal.toReal_eq_toReal_iff'
    (ne_top_of_le_ne_top ENNReal.one_ne_top hLle)
    (ne_top_of_le_ne_top ENNReal.one_ne_top hRle)).mp ?_
  have hLt : (((walkLaw G x) S).toReal)
      = ∫ X, F (shiftPath (τ X).toNat X) ∂(walkLaw G x) := by
    have hfun : ∀ X : ℕ → V, F (shiftPath (τ X).toNat X)
        = Set.indicator S (fun _ => (1 : ℝ)) X := fun X => rfl
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
    have hio : ∫ (Y : ℕ → V), S.indicator (fun x => (1 : ℝ)) Y ∂(walkLaw G x)
        = (walkLaw G x).real S := integral_indicator_one hSm
    rw [hio, measureReal_def]
  have hRt : ((∫⁻ X, (∫⁻ Y, Set.indicator A (fun _ => (1 : ℝ≥0∞)) Y
      ∂(walkLaw G (X ((τ X).toNat)))) ∂(walkLaw G x)).toReal)
      = ∫ X, pathExp G F (X ((τ X).toNat)) ∂(walkLaw G x) := by
    have hstopm : Measurable fun X : ℕ → V => X ((τ X).toNat) :=
      (measurable_pi_apply 0).comp (measurable_shiftPath_stop τ hτ)
    have hmeas : Measurable fun X : ℕ → V =>
        (∫⁻ Y, Set.indicator A (fun _ => (1 : ℝ≥0∞)) Y
          ∂(walkLaw G (X ((τ X).toNat)))) :=
      (measurable_of_countable
        (fun y : V => (∫⁻ Y, Set.indicator A (fun _ => (1 : ℝ≥0∞)) Y
          ∂(walkLaw G y)))).comp hstopm
    rw [← integral_toReal hmeas.aemeasurable
      (Filter.Eventually.of_forall fun X =>
        lt_of_le_of_lt ((hRi _).symm ▸ hone _) ENNReal.one_lt_top)]
    have hpath : ∀ X : ℕ → V, pathExp G F (X ((τ X).toNat))
        = ((∫⁻ Y, Set.indicator A (fun _ => (1 : ℝ≥0∞)) Y
          ∂(walkLaw G (X ((τ X).toNat)))).toReal) := by
      intro X
      show (∫ Y, F Y ∂(walkLaw G (X ((τ X).toNat)))) = _
      rw [hF]
      have hio : ∫ (Y : ℕ → V), A.indicator (fun x => (1 : ℝ)) Y
          ∂(walkLaw G (X ((τ X).toNat)))
          = (walkLaw G (X ((τ X).toNat))).real A := integral_indicator_one hAm
      rw [hio, measureReal_def, hRi]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpath)]
  rw [hLt, hRt]
  exact hmain

end RWRS.Support