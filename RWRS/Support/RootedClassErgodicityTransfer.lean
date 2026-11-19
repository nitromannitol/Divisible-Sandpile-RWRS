import RWRS.Support.RootedClassErgodicityCriterion

/-!
# Transferring ergodicity to network codes

A probability measure supported on connected networks is ergodic whenever its
rooted-class law is trivial on every rerooting-invariant class event.
-/

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- Invariant network events and their descended class events have equal probabilities. -/
theorem measure_eq_goodNetClassLaw_of_invariant (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N) {A : Set (Net 0)}
    (hA : MeasurableSet[invariantSigma 0] A) :
    ∃ D : Set RootedBallClass, MeasurableSet[rootedClassInvariantSigma] D ∧
      Q A = goodNetClassLaw Q D := by
  obtain ⟨D, hD, hdesc⟩ := exists_classInvariant_event hA
  refine ⟨D, hD, ?_⟩
  have hf : Measurable (D.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hD.1
  have hlin : (∫⁻ N, A.indicator (fun _ => (1 : ℝ≥0∞)) N ∂Q) =
      ∫⁻ N, goodNetExtend ((D.indicator (fun _ => (1 : ℝ≥0∞))) ∘ goodNetClass) N ∂Q := by
    apply lintegral_congr_ae
    filter_upwards [hgood] with N hN
    rw [goodNetExtend_of_good _ N hN]
    change A.indicator (fun _ => (1 : ℝ≥0∞)) N =
      D.indicator (fun _ => (1 : ℝ≥0∞)) (goodNetClass ⟨N, hN⟩)
    by_cases h : N ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hdesc ⟨N, hN⟩).1 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hd => h ((hdesc ⟨N, hN⟩).2 hd))]
  calc
    Q A = ∫⁻ N, A.indicator (fun _ => (1 : ℝ≥0∞)) N ∂Q := (lintegral_indicator_one hA.1).symm
    _ = ∫⁻ N, goodNetExtend ((D.indicator (fun _ => (1 : ℝ≥0∞))) ∘ goodNetClass) N ∂Q := hlin
    _ = ∫⁻ c, D.indicator (fun _ => (1 : ℝ≥0∞)) c ∂goodNetClassLaw Q :=
      (lintegral_goodNetClassLaw Q hgood hf).symm
    _ = goodNetClassLaw Q D := lintegral_indicator_one hD.1

/-- Triviality of invariant class events implies ergodicity of the supported network law. -/
theorem isErgodicNet_of_goodNetClassLaw (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N)
    (htriv : ∀ D, MeasurableSet[rootedClassInvariantSigma] D →
      goodNetClassLaw Q D = 0 ∨ goodNetClassLaw Q D = 1) : IsErgodicNet Q := by
  intro A hA
  obtain ⟨D, hD, heq⟩ := measure_eq_goodNetClassLaw_of_invariant Q hgood hA
  rw [heq]
  exact htriv D hD

end RWRS.Support
