/-
The conditioning event of the phase transition on a stationary graph.

`thm:stationary-phase` sets `B := {P(A | I_G) = 1}` for the stabilization event
`A` and argues under the two conditional laws `P(· | B)` and `P(· | Bᶜ)`
(`rwrs.tex:343-347`).  Two facts make that argument work, and both are proved
here: when the conditional probability takes only the values `0` and `1` the
event `B` has the same probability as `A`, and conditioning on a
rerooting-invariant event of the rooted GRAPH leaves the marked law an i.i.d.
marking of a stationary law of rooted graphs, with the same mark law.
-/
import RWRS.Support.ErgCondLaw

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The event where the conditional probability of `A` given the graph events is
one carries all of `A` that it meets: `P (A ∩ B) = P B`.  This is `P(Aᶜ ∩ B) = 0`
of `rwrs.tex:344`. -/
theorem measure_inter_condExpOne (P : Measure (RWRS.Net 1)) [IsProbabilityMeasure P]
    {A : Set (RWRS.Net 1)} (hA : MeasurableSet A) :
    P (A ∩ {M | (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1})
      = P {M | (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1} := by
  set B := {M | (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1} with hBdef
  have hm : RWRS.graphInvariantSigma 1 ≤ (inferInstance : MeasurableSpace (RWRS.Net 1)) :=
    graphInvariantSigma_le_ambient
  have hBm : MeasurableSet[RWRS.graphInvariantSigma 1] B :=
    stronglyMeasurable_condExp.measurable (measurableSet_singleton 1)
  have hBm0 : MeasurableSet B := hm _ hBm
  have hint : Integrable (A.indicator (fun _ => (1 : ℝ))) P := (integrable_const 1).indicator hA
  have hB1 : ∫ M in B, (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M ∂P
      = ∫ M in B, A.indicator (fun _ => (1 : ℝ)) M ∂P := setIntegral_condExp hm hint hBm
  have hBleft : ∫ M in B, (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M ∂P
      = (P B).toReal := by
    rw [setIntegral_congr_fun hBm0
      (fun M hM => hM : ∀ M ∈ B,
        (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have hBright : ∫ M in B, A.indicator (fun _ => (1 : ℝ)) M ∂P = (P (B ∩ A)).toReal := by
    rw [MeasureTheory.setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def]
  have h := hBleft.symm.trans (hB1.trans hBright)
  rw [Set.inter_comm A B]
  exact ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top P B) (measure_ne_top P _)).mp h).symm

/-- Off that event the conditional probability is zero, so `A` is null there.
This is `P(A ∩ Bᶜ) = 0` of `rwrs.tex:344`. -/
theorem measure_inter_compl_condExpOne (P : Measure (RWRS.Net 1)) [IsProbabilityMeasure P]
    {A : Set (RWRS.Net 1)} (hA : MeasurableSet A)
    (h01 : ∀ᵐ M ∂P,
      (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 0 ∨
      (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1) :
    P (A ∩ {M | (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1}ᶜ)
      = 0 := by
  set B := {M | (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1} with hBdef
  have hm : RWRS.graphInvariantSigma 1 ≤ (inferInstance : MeasurableSpace (RWRS.Net 1)) :=
    graphInvariantSigma_le_ambient
  have hBm : MeasurableSet[RWRS.graphInvariantSigma 1] B :=
    stronglyMeasurable_condExp.measurable (measurableSet_singleton 1)
  have hBm0 : MeasurableSet B := hm _ hBm
  have hint : Integrable (A.indicator (fun _ => (1 : ℝ))) P := (integrable_const 1).indicator hA
  have hC1 : ∫ M in Bᶜ, (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M ∂P
      = ∫ M in Bᶜ, A.indicator (fun _ => (1 : ℝ)) M ∂P := setIntegral_condExp hm hint hBm.compl
  have hCleft : ∫ M in Bᶜ, (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M ∂P
      = 0 := by
    have hae : ∀ᵐ M ∂(P.restrict Bᶜ),
        (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 0 := by
      filter_upwards [ae_restrict_of_ae h01, ae_restrict_mem hBm0.compl] with M hM hMB
      rcases hM with hM | hM
      · exact hM
      · exact absurd hM hMB
    rw [integral_congr_ae hae, integral_zero]
  have hCright : ∫ M in Bᶜ, A.indicator (fun _ => (1 : ℝ)) M ∂P = (P (Bᶜ ∩ A)).toReal := by
    rw [MeasureTheory.setIntegral_indicator hA, setIntegral_const, smul_eq_mul, mul_one,
      measureReal_def]
  have h := hCleft.symm.trans (hC1.trans hCright)
  rw [Set.inter_comm A Bᶜ]
  have h2 := (ENNReal.toReal_eq_toReal_iff' (x := (0 : ℝ≥0∞)) (y := P (Bᶜ ∩ A))
    (by simp) (measure_ne_top P _)).mp (by simpa using h)
  exact h2.symm

/-- When the conditional probability of `A` given the graph events is `0` or `1`
almost surely, the event where it is `1` has the probability of `A`. -/
theorem measure_eq_condExp_eq_one (P : Measure (RWRS.Net 1)) [IsProbabilityMeasure P]
    {A : Set (RWRS.Net 1)} (hA : MeasurableSet A)
    (h01 : ∀ᵐ M ∂P,
      (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 0 ∨
      (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1) :
    P A = P {M | (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1} := by
  set B := {M | (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1} with hBdef
  have hBm0 : MeasurableSet B :=
    graphInvariantSigma_le_ambient _
      (stronglyMeasurable_condExp.measurable (measurableSet_singleton 1))
  have hsplit : P (A ∩ B) + P (A \ B) = P A := measure_inter_add_sdiff A hBm0
  have hdiff : P (A \ B) = 0 := by
    rw [Set.sdiff_eq]
    exact measure_inter_compl_condExpOne P hA h01
  rw [← hsplit, hdiff, add_zero]
  exact measure_inter_condExpOne P hA

/-- Restricting an i.i.d. marked network to an event of the rooted graph is the
i.i.d. marking, with the SAME mark law, of the restricted law of the rooted
graph.  This is the step of `rwrs.tex:347` at which graph measurability of the
conditioning event keeps the marks i.i.d. with their original law. -/
theorem markIid_restrict (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {E : Set (RWRS.Net 0)} (hE : MeasurableSet E) :
    (RWRS.markIid Q ν).restrict (RWRS.forgetMarks ⁻¹' E) = RWRS.markIid (Q.restrict E) ν := by
  haveI := instIsProbabilityMeasureIidLaw (V := ℕ) ν
  rw [markIid_eq_map, markIid_eq_map,
    Measure.restrict_map measurable_markMap (measurable_forgetMarks hE)]
  congr 1
  have hpre : markMap ⁻¹' (RWRS.forgetMarks ⁻¹' E) = E ×ˢ (Set.univ : Set (ℕ → ℝ)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, forgetMarks_markMap]
  rw [hpre, ← Measure.prod_restrict, Measure.restrict_univ]

/-- The i.i.d. marking is homogeneous in the law of the rooted graph. -/
theorem markIid_smul (Q : Measure (RWRS.Net 0)) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (c : ℝ≥0∞) : RWRS.markIid (c • Q) ν = c • RWRS.markIid Q ν := by
  haveI := instIsProbabilityMeasureIidLaw (V := ℕ) ν
  rw [markIid_eq_map, markIid_eq_map, Measure.prod_smul_left, Measure.map_smul]

/-- A stationary law restricted to a rerooting-invariant event is stationary.
This is the step of `rwrs.tex:347` at which rerooting invariance of the
conditioning event keeps the law of the rooted graph stationary. -/
theorem isStationaryNet_restrict {m : ℕ} {P : Measure (RWRS.Net m)}
    (hstat : RWRS.IsStationaryNet P) {E : Set (RWRS.Net m)} (hEmeas : MeasurableSet E)
    (hEiso : RWRS.NetInvariantSet E) (hEre : RWRS.RerootInvariant E) :
    RWRS.IsStationaryNet (P.restrict E) := by
  have hleft : ∀ g : RWRS.Net m → ℝ≥0∞,
      (∫⁻ N, E.indicator (fun _ => (1 : ℝ≥0∞)) N * g N ∂P) = ∫⁻ N in E, g N ∂P := by
    intro g
    rw [← lintegral_indicator hEmeas]
    refine lintegral_congr fun N => ?_
    by_cases hN : N ∈ E
    · rw [Set.indicator_of_mem hN, Set.indicator_of_mem hN, one_mul]
    · rw [Set.indicator_of_notMem hN, Set.indicator_of_notMem hN, zero_mul]
  intro h hmeas hinv
  have hinv' : RWRS.NetInvariant fun N => E.indicator (fun _ => (1 : ℝ≥0∞)) N * h N := by
    intro N N' hiso
    show E.indicator (fun _ => (1 : ℝ≥0∞)) N * h N
      = E.indicator (fun _ => (1 : ℝ≥0∞)) N' * h N'
    rw [hinv N N' hiso]
    congr 1
    by_cases hN : N ∈ E
    · rw [Set.indicator_of_mem hN, Set.indicator_of_mem ((hEiso N N' hiso).mp hN)]
    · rw [Set.indicator_of_notMem hN,
        Set.indicator_of_notMem (fun hc => hN ((hEiso N N' hiso).mpr hc))]
  have hkey := hstat (fun N => E.indicator (fun _ => (1 : ℝ≥0∞)) N * h N)
    ((measurable_const.indicator hEmeas).mul hmeas) hinv'
  rw [hleft] at hkey
  rw [hkey, ← hleft]
  refine lintegral_congr fun N => ?_
  by_cases hN : N ∈ E
  · rw [Set.indicator_of_mem hN, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Set.indicator_of_mem ((hEre N y (by simpa using hy)).mp hN), one_mul]
  · rw [Set.indicator_of_notMem hN, zero_mul]
    refine ENNReal.div_eq_zero_iff.mpr (Or.inl ?_)
    refine Finset.sum_eq_zero fun y hy => ?_
    rw [Set.indicator_of_notMem (fun hc => hN ((hEre N y (by simpa using hy)).mpr hc)), zero_mul]

/-- Stationarity is homogeneous. -/
theorem isStationaryNet_smul {m : ℕ} {P : Measure (RWRS.Net m)}
    (hstat : RWRS.IsStationaryNet P) (c : ℝ≥0∞) : RWRS.IsStationaryNet (c • P) := by
  intro h hmeas hinv
  rw [lintegral_smul_measure, lintegral_smul_measure, hstat h hmeas hinv]

/-- The conditioning event of `thm:stationary-phase` as an event of the rooted
graph: when the conditional probability of `A` given the graph events is `0` or
`1` almost surely, there is a rerooting-invariant event `B` of the rooted graph
carrying the whole of `A`.  This is `B ∈ I_G` with `P(A Δ B) = 0` of
`rwrs.tex:343-345`. -/
theorem exists_graph_event_of_zeroOne (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {A : Set (RWRS.Net 1)} (hA : MeasurableSet A)
    (h01 : ∀ᵐ M ∂(RWRS.markIid Q ν),
      ((RWRS.markIid Q ν)[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 0 ∨
      ((RWRS.markIid Q ν)[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1) :
    ∃ B : Set (RWRS.Net 0), MeasurableSet[RWRS.invariantSigma 0] B ∧
      RWRS.markIid Q ν A = Q B ∧
      RWRS.markIid Q ν (A ∩ RWRS.forgetMarks ⁻¹' B)
        = RWRS.markIid Q ν (RWRS.forgetMarks ⁻¹' B) ∧
      RWRS.markIid Q ν (A ∩ (RWRS.forgetMarks ⁻¹' B)ᶜ) = 0 := by
  haveI : IsProbabilityMeasure (RWRS.markIid Q ν) := isProbabilityMeasure_markIid Q ν
  set P := RWRS.markIid Q ν with hP
  set S := {M : RWRS.Net 1 |
    (P[A.indicator (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1]) M = 1} with hS
  have hSm : MeasurableSet[RWRS.graphInvariantSigma 1] S :=
    stronglyMeasurable_condExp.measurable (measurableSet_singleton 1)
  obtain ⟨B, hB, hBS⟩ := hSm
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · rw [measure_eq_condExp_eq_one P hA h01, ← hS, ← hBS, hP,
      ← Measure.map_apply measurable_forgetMarks (invariantSigma_le _ hB),
      map_forgetMarks_markIid Q ν]
  · rw [hBS]
    exact measure_inter_condExpOne P hA
  · rw [hBS]
    exact measure_inter_compl_condExpOne P hA h01

end RWRS.Support
