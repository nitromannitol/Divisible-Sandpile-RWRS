/-
The conditional law of an i.i.d. marked network given the rerooting-invariant
events of the underlying rooted graph.

The paper conditions the marked network on `I_G ⊆ σ(G,ρ)` and says that "since
the masses are sampled independently of `(G,ρ)`, conditionally on `I_G` they
remain i.i.d. and independent of `(G,ρ)`" (`rwrs.tex:337-340`).  That is proved
here, not assumed: the law of the marked network is the image of a product, the
conditioning reads the first factor only, so the conditional law is the i.i.d.
marking of the conditional law of the rooted graph.
-/
import RWRS.Support.ErgKernel
import RWRS.Support.ErgMarking
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- A rerooting-invariant event of the rooted graph is a rerooting-invariant
event of the network. -/
theorem graphInvariantSigma_le {m : ℕ} :
    RWRS.graphInvariantSigma m ≤ RWRS.invariantSigma m := by
  rintro A ⟨B, ⟨hBmeas, hBiso, hBre⟩, rfl⟩
  refine ⟨measurable_forgetMarks hBmeas, ?_, ?_⟩
  · intro N N' h
    exact hBiso _ _ (netIso_forgetMarks h)
  · intro N y hy
    exact hBre (RWRS.forgetMarks N) y hy

/-- Every event of the graph σ-algebra is measurable. -/
theorem graphInvariantSigma_le_ambient {m : ℕ} :
    RWRS.graphInvariantSigma m ≤ (inferInstance : MeasurableSpace (RWRS.Net m)) :=
  le_trans graphInvariantSigma_le invariantSigma_le

/-- The rooted graph underlying an i.i.d. marked network has the law of the
rooted graph. -/
theorem map_forgetMarks_markIid (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (RWRS.markIid Q ν).map RWRS.forgetMarks = Q := by
  haveI := instIsProbabilityMeasureIidLaw (V := ℕ) ν
  rw [markIid_eq_map, Measure.map_map measurable_forgetMarks measurable_markMap,
    show RWRS.forgetMarks ∘ markMap = Prod.fst from funext forgetMarks_markMap,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- The mark average of the indicator of an event met with a graph event. -/
theorem markAvg_indicator_inter (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (A : Set (RWRS.Net 1)) (B : Set (RWRS.Net 0)) (N : RWRS.Net 0) :
    markAvg ν ((A ∩ RWRS.forgetMarks ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞))) N
      = B.indicator (fun _ => (1 : ℝ≥0∞)) N
          * markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N := by
  unfold markAvg
  by_cases hB : N ∈ B
  · rw [Set.indicator_of_mem hB, one_mul]
    refine lintegral_congr fun ξ => ?_
    have hmem : markMap (N, ξ) ∈ RWRS.forgetMarks ⁻¹' B := by
      rw [Set.mem_preimage, forgetMarks_markMap]; exact hB
    by_cases hA : markMap (N, ξ) ∈ A
    · rw [Set.indicator_of_mem (Set.mem_inter hA hmem), Set.indicator_of_mem hA]
    · rw [Set.indicator_of_notMem (fun hx => hA hx.1), Set.indicator_of_notMem hA]
  · rw [Set.indicator_of_notMem hB, zero_mul]
    have hzero : ∀ ξ : ℕ → ℝ,
        ((A ∩ RWRS.forgetMarks ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞))) (markMap (N, ξ)) = 0 := by
      intro ξ
      have hmem : markMap (N, ξ) ∉ RWRS.forgetMarks ⁻¹' B := by
        rw [Set.mem_preimage, forgetMarks_markMap]; exact hB
      exact Set.indicator_of_notMem (fun hx => hmem hx.2) _
    simp only [hzero]
    exact lintegral_zero

/-- The probability of an event met with a graph event, as an integral of the
mark average over the graph event. -/
theorem markIid_inter_graph (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {A : Set (RWRS.Net 1)} (hA : MeasurableSet A)
    {B : Set (RWRS.Net 0)} (hB : MeasurableSet B) :
    RWRS.markIid Q ν (A ∩ RWRS.forgetMarks ⁻¹' B)
      = ∫⁻ N in B, markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N ∂Q := by
  have hmeas : MeasurableSet (A ∩ RWRS.forgetMarks ⁻¹' B) :=
    hA.inter (measurable_forgetMarks hB)
  have hstep : RWRS.markIid Q ν (A ∩ RWRS.forgetMarks ⁻¹' B)
      = ∫⁻ M, ((A ∩ RWRS.forgetMarks ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞))) M
          ∂(RWRS.markIid Q ν) := by
    rw [lintegral_indicator_const hmeas, one_mul]
  rw [hstep, lintegral_markIid Q ν (measurable_const.indicator hmeas)]
  simp only [markAvg_indicator_inter ν A B]
  rw [← lintegral_indicator hB]
  refine lintegral_congr fun N => ?_
  by_cases h : N ∈ B
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- An integral of a function of the underlying rooted graph over a graph event
is the integral over that event under the law of the rooted graph. -/
theorem lintegral_forgetMarks_restrict (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {h : RWRS.Net 0 → ℝ≥0∞} (hh : Measurable h)
    {B : Set (RWRS.Net 0)} (hB : MeasurableSet B) :
    (∫⁻ M in RWRS.forgetMarks ⁻¹' B, h (RWRS.forgetMarks M) ∂(RWRS.markIid Q ν))
      = ∫⁻ N in B, h N ∂Q := by
  conv_rhs => rw [← map_forgetMarks_markIid Q ν]
  rw [Measure.restrict_map measurable_forgetMarks hB, lintegral_map hh measurable_forgetMarks]

/-- An i.i.d. marked network is a probability measure. -/
theorem isProbabilityMeasure_markIid (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] : IsProbabilityMeasure (RWRS.markIid Q ν) := by
  haveI := instIsProbabilityMeasureIidLaw (V := ℕ) ν
  rw [markIid_eq_map]
  exact Measure.isProbabilityMeasure_map measurable_markMap.aemeasurable


/-- The conditional law of an i.i.d. marked network given the rerooting-invariant
events of the underlying rooted graph is the i.i.d. marking of the conditional
law of the rooted graph.  This is the step of `rwrs.tex:337-340` at which the
marks stay i.i.d.: the conditioning reads the first factor of the product the
marked law is the image of. -/
theorem condExp_indicator_markIid
    (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (K : RWRS.Net 0 → Measure (RWRS.Net 0)) (hKprob : ∀ N, IsProbabilityMeasure (K N))
    (hKmeas : ∀ A : Set (RWRS.Net 0), MeasurableSet A →
      Measurable[RWRS.invariantSigma 0] fun N => K N A)
    (hKid : ∀ A : Set (RWRS.Net 0), MeasurableSet A →
      ∀ B : Set (RWRS.Net 0), MeasurableSet[RWRS.invariantSigma 0] B →
        (∫⁻ N in B, K N A ∂Q) = Q (A ∩ B))
    {A : Set (RWRS.Net 1)} (hA : MeasurableSet A) :
    (fun M => (RWRS.markIid (K (RWRS.forgetMarks M)) ν A).toReal)
      =ᵐ[RWRS.markIid Q ν]
        (RWRS.markIid Q ν)[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1] := by
  haveI : IsProbabilityMeasure (RWRS.markIid Q ν) := isProbabilityMeasure_markIid Q ν
  have humeas : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have hmavg : Measurable (markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞)))) :=
    measurable_markAvg ν humeas
  obtain ⟨hh0meas, hh0id⟩ := kernel_lintegral Q K hKmeas hKid hmavg
  set h0 : RWRS.Net 0 → ℝ≥0∞ :=
    fun N => ∫⁻ M, markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) M ∂(K N) with hh0
  -- the value of the component at the event
  have hval : ∀ N, RWRS.markIid (K N) ν A = h0 N := by
    intro N
    haveI := hKprob N
    have hstep : RWRS.markIid (K N) ν A
        = ∫⁻ M, (A.indicator (fun _ => (1 : ℝ≥0∞))) M ∂(RWRS.markIid (K N) ν) := by
      rw [lintegral_indicator_const hA, one_mul]
    rw [hstep, lintegral_markIid (K N) ν humeas]
  have hle1 : ∀ N, h0 N ≤ 1 := by
    intro N
    haveI := hKprob N
    calc h0 N ≤ ∫⁻ _M : RWRS.Net 0, (1 : ℝ≥0∞) ∂(K N) :=
          lintegral_mono fun M => markAvg_indicator_le_one ν A M
      _ = 1 := by rw [lintegral_const, measure_univ, mul_one]
  simp only [hval]
  -- the candidate is measurable for the graph σ-algebra
  have hgm : Measurable[RWRS.graphInvariantSigma 1] fun M => (h0 (RWRS.forgetMarks M)).toReal :=
    (hh0meas.ennreal_toReal).comp (_root_.comap_measurable RWRS.forgetMarks)
  have hgm0 : Measurable fun M : RWRS.Net 1 => (h0 (RWRS.forgetMarks M)).toReal :=
    hgm.mono graphInvariantSigma_le_ambient le_rfl
  have hbound : ∀ M : RWRS.Net 1, ‖(h0 (RWRS.forgetMarks M)).toReal‖ ≤ 1 := by
    intro M
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (hle1 (RWRS.forgetMarks M))
  have hgint : Integrable (fun M : RWRS.Net 1 => (h0 (RWRS.forgetMarks M)).toReal)
      (RWRS.markIid Q ν) :=
    (integrable_const (1 : ℝ)).mono' hgm0.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq graphInvariantSigma_le_ambient
    ((integrable_const (1 : ℝ)).indicator hA) (fun s _ _ => hgint.integrableOn)
    (fun s hs _ => ?_) (hgm.stronglyMeasurable.aestronglyMeasurable)
  obtain ⟨B, hB, rfl⟩ := hs
  have hBmeas : MeasurableSet B := hB.1
  -- the left side
  have hleft : ∫ M in RWRS.forgetMarks ⁻¹' B, (h0 (RWRS.forgetMarks M)).toReal
      ∂(RWRS.markIid Q ν)
      = (∫⁻ N in B, markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N ∂Q).toReal := by
    rw [MeasureTheory.integral_toReal (f := fun M : RWRS.Net 1 => h0 (RWRS.forgetMarks M))
      ((hh0meas.mono invariantSigma_le le_rfl).comp measurable_forgetMarks).aemeasurable
      (Filter.Eventually.of_forall fun M =>
        lt_of_le_of_lt (hle1 (RWRS.forgetMarks M)) ENNReal.one_lt_top),
      lintegral_forgetMarks_restrict Q ν
        ((hh0meas.mono invariantSigma_le le_rfl)) hBmeas, hh0id B hB]
  -- the right side
  have hright : ∫ M in RWRS.forgetMarks ⁻¹' B, (A.indicator (fun _ => (1 : ℝ))) M
      ∂(RWRS.markIid Q ν)
      = (∫⁻ N in B, markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N ∂Q).toReal := by
    rw [MeasureTheory.setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def, Set.inter_comm, markIid_inter_graph Q ν hA hBmeas]
  rw [hleft, hright]

end RWRS.Support
