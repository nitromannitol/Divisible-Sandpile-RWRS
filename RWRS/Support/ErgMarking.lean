/-
The ergodicity half of `lem:ergodic-marked-stationary`.

The decoration map `markMap` copies the neighbour lists and the root and
touches neither.  So an event of decorated networks that reads only those two
coordinates is the decoration of the corresponding event of rooted graphs, its
probability under the decorated law is the probability of that event under the
law of the rooted graph, and isomorphism invariance and rerooting invariance
transfer along the decoration in both directions.  These are the graph-side
facts the conditioning argument of the lemma uses.
-/
import RWRS.Support.Marking

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The event of rooted graphs underlying a graph-measurable event of decorated
networks. -/
def graphPart (B : Set ((ℕ → List ℕ) × ℕ)) : Set (RWRS.Net 0) :=
  (fun N : RWRS.Net 0 => (N.1, N.2.1)) ⁻¹' B

/-- The neighbour lists and the root of a network are a measurable function of
it. -/
theorem measurable_graphCoord {m : ℕ} : Measurable fun N : RWRS.Net m => (N.1, N.2.1) :=
  measurable_fst.prodMk (measurable_fst.comp measurable_snd)

/-- The decoration of the underlying event is the event. -/
theorem markMap_preimage (B : Set ((ℕ → List ℕ) × ℕ)) :
    markMap ⁻¹' ((fun N : RWRS.Net 1 => (N.1, N.2.1)) ⁻¹' B)
      = (graphPart B) ×ˢ (Set.univ : Set (ℕ → ℝ)) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, graphPart, markMap]

/-- A graph-measurable event has the same probability under the decorated law
as its underlying event has under the law of the rooted graph. -/
theorem measure_markIid_graph (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (B : Set ((ℕ → List ℕ) × ℕ)) (hB : MeasurableSet B) :
    RWRS.markIid Q ν ((fun N : RWRS.Net 1 => (N.1, N.2.1)) ⁻¹' B) = Q (graphPart B) := by
  rw [markIid_eq_map, Measure.map_apply measurable_markMap (measurable_graphCoord hB),
    markMap_preimage, Measure.prod_prod, measure_univ, mul_one]

/-- An isomorphism of rooted graphs is an isomorphism of the two networks it
decorates with the same constant mark. -/
theorem netIso_markMap_const {N N' : RWRS.Net 0} (h : RWRS.NetIso N N') (c : ℝ) :
    RWRS.NetIso (markMap (N, fun _ => c)) (markMap (N', fun _ => c)) := by
  obtain ⟨φ, hadj, hroot, -⟩ := h
  exact ⟨φ, hadj, hroot, fun i => rfl⟩

/-- Membership in a graph-measurable event is read off the decoration. -/
theorem mem_graphPart_iff (B : Set ((ℕ → List ℕ) × ℕ)) (N : RWRS.Net 0) (c : ℝ) :
    N ∈ graphPart B ↔ markMap (N, fun _ => c) ∈ (fun M : RWRS.Net 1 => (M.1, M.2.1)) ⁻¹' B :=
  Iff.rfl

/-- The underlying event of a rerooting-invariant graph-measurable event is
rerooting invariant. -/
theorem invariantSigma_graphPart {B : Set ((ℕ → List ℕ) × ℕ)} (hB : MeasurableSet B)
    (hiso : RWRS.NetInvariantSet ((fun M : RWRS.Net 1 => (M.1, M.2.1)) ⁻¹' B))
    (hre : RWRS.RerootInvariant ((fun M : RWRS.Net 1 => (M.1, M.2.1)) ⁻¹' B)) :
    (RWRS.invariantSigma 0).MeasurableSet' (graphPart B) := by
  refine ⟨measurable_graphCoord hB, ?_, ?_⟩
  · intro N N' h
    rw [mem_graphPart_iff B N 0, mem_graphPart_iff B N' 0]
    exact hiso _ _ (netIso_markMap_const h 0)
  · intro N y hadj
    rw [mem_graphPart_iff B N 0, mem_graphPart_iff B (RWRS.netReroot N y) 0]
    exact hre (markMap (N, fun _ => 0)) y hadj

/-! ### An invariant function is constant under an ergodic law -/

/-- Under an ergodic law an invariant `[0,1]`-valued function is almost surely
constant. -/
theorem ae_eq_const_of_isErgodicNet {m : ℕ} {P : Measure (RWRS.Net m)}
    [IsProbabilityMeasure P] (herg : RWRS.IsErgodicNet P) {q : RWRS.Net m → ℝ}
    (hmeas : Measurable q) (hq0 : ∀ N, 0 ≤ q N) (hq1 : ∀ N, q N ≤ 1)
    (hiso : ∀ N N', RWRS.NetIso N N' → q N = q N')
    (hre : ∀ (N : RWRS.Net m) (y : ℕ),
      (RWRS.netGraph N).Adj (RWRS.netRoot N) y → q N = q (RWRS.netReroot N y)) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ᵐ N ∂P, q N = c := by
  classical
  set S : ℝ → Set (RWRS.Net m) := fun t => {N | q N ≤ t} with hSdef
  have hSmeas : ∀ t, MeasurableSet (S t) := fun t => measurableSet_le hmeas measurable_const
  have hdich : ∀ t, P (S t) = 0 ∨ P (S t) = 1 := by
    intro t
    refine herg (S t) ⟨hSmeas t, ?_, ?_⟩
    · intro N N' h
      simp only [hSdef, Set.mem_setOf_eq, hiso N N' h]
    · intro N y hadj
      simp only [hSdef, Set.mem_setOf_eq, hre N y hadj]
  set T : Set ℝ := {t : ℝ | P (S t) = 1} with hTdef
  have h1T : (1:ℝ) ∈ T := by
    have hu : S 1 = Set.univ := by
      ext N
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact hq1 N
    simp only [hTdef, Set.mem_setOf_eq, hu, measure_univ]
  have hTlb : ∀ t ∈ T, (0:ℝ) ≤ t := by
    intro t ht
    by_contra hlt
    push Not at hlt
    have he : S t = ∅ := by
      ext N
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le.2 (lt_of_lt_of_le hlt (hq0 N))
    rw [hTdef, Set.mem_setOf_eq, he, measure_empty] at ht
    exact zero_ne_one ht
  have hTbdd : BddBelow T := ⟨0, hTlb⟩
  set c : ℝ := sInf T with hcdef
  have hc0 : (0:ℝ) ≤ c := le_csInf ⟨1, h1T⟩ hTlb
  have hc1 : c ≤ 1 := csInf_le hTbdd h1T
  have hSc : P (S c) = 1 := by
    have hinter : S c = ⋂ n : ℕ, S (c + 1 / ((n : ℝ) + 1)) := by
      ext N
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h n
        have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro h
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        exact le_trans (h n) (by linarith)
    have hone : ∀ n : ℕ, P (S (c + 1 / ((n : ℝ) + 1))) = 1 := by
      intro n
      have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨t, htT, hts⟩ := exists_lt_of_csInf_lt ⟨1, h1T⟩ (by linarith : c < c + 1 / ((n : ℝ) + 1))
      have hsub : S t ⊆ S (c + 1 / ((n : ℝ) + 1)) := by
        intro N hN
        exact le_trans hN hts.le
      have := measure_mono (μ := P) hsub
      rw [htT] at this
      exact le_antisymm (prob_le_one) this
    rw [hinter]
    rw [← prob_compl_eq_zero_iff (MeasurableSet.iInter fun n => hSmeas _)]
    rw [Set.compl_iInter]
    refine measure_iUnion_null fun n => ?_
    rw [prob_compl_eq_zero_iff (hSmeas _)]
    exact hone n
  have hlow : P {N : RWRS.Net m | q N < c} = 0 := by
    have hunion : {N : RWRS.Net m | q N < c} = ⋃ n : ℕ, S (c - 1 / ((n : ℝ) + 1)) := by
      ext N
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : (0:ℝ) < c - q N)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    rw [hunion]
    refine measure_iUnion_null fun n => ?_
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rcases hdich (c - 1 / ((n : ℝ) + 1)) with h | h
    · exact h
    · exact absurd (csInf_le hTbdd h) (by linarith)
  refine ⟨c, hc0, hc1, ?_⟩
  have hnull : P {N : RWRS.Net m | ¬ (q N = c)} = 0 := by
    have hsub : {N : RWRS.Net m | ¬ (q N = c)} ⊆ (S c)ᶜ ∪ {N : RWRS.Net m | q N < c} := by
      intro N hN
      rcases lt_trichotomy (q N) c with h | h | h
      · exact Or.inr h
      · exact absurd h hN
      · exact Or.inl (by simpa [hSdef] using not_le.2 h)
    refine measure_mono_null hsub ?_
    rw [measure_union_null_iff]
    exact ⟨(prob_compl_eq_zero_iff (hSmeas c)).2 hSc, hlow⟩
  exact hnull


/-! ### The conditional probability of a mark event given the graph -/

/-- `q(G,o) = P((G,o,σ) ∈ A | G,o)`, the conditional probability of a mark event
given the graph and the root. -/
noncomputable def markProb (ν : Measure ℝ) (A : Set (RWRS.Net 1)) (N : RWRS.Net 0) : ℝ :=
  (markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N).toReal

theorem markAvg_indicator_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (A : Set (RWRS.Net 1)) (N : RWRS.Net 0) :
    markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N ≤ 1 := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw ℕ ν) := instIsProbabilityMeasureIidLaw ν
  have h1 : markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N
      ≤ ∫⁻ _ξ : ℕ → ℝ, (1 : ℝ≥0∞) ∂(RWRS.iidLaw ℕ ν) := by
    refine lintegral_mono fun ξ => ?_
    exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => bot_le)
  rw [lintegral_const, measure_univ, mul_one] at h1
  exact h1

theorem markProb_nonneg (ν : Measure ℝ) (A : Set (RWRS.Net 1)) (N : RWRS.Net 0) :
    0 ≤ markProb ν A N := ENNReal.toReal_nonneg

theorem markProb_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (A : Set (RWRS.Net 1))
    (N : RWRS.Net 0) : markProb ν A N ≤ 1 := by
  rw [markProb]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact markAvg_indicator_le_one ν A N)

theorem measurable_markProb (ν : Measure ℝ) [IsProbabilityMeasure ν] {A : Set (RWRS.Net 1)}
    (hA : MeasurableSet A) : Measurable (markProb ν A) :=
  (measurable_markAvg ν ((measurable_const).indicator hA)).ennreal_toReal

theorem markProb_invariant (ν : Measure ℝ) [IsProbabilityMeasure ν] {A : Set (RWRS.Net 1)}
    (hA : MeasurableSet A) (hiso : RWRS.NetInvariantSet A) :
    ∀ N N', RWRS.NetIso N N' → markProb ν A N = markProb ν A N' := by
  intro N N' h
  have hinv : RWRS.NetInvariant (A.indicator (fun _ => (1 : ℝ≥0∞))) := by
    intro M M' hM
    by_cases hmem : M ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hiso M M' hM).1 hmem)]
    · rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (fun hc => hmem ((hiso M M' hM).2 hc))]
  rw [markProb, markProb, markAvg_invariant ν ((measurable_const).indicator hA) hinv N N' h]

theorem markProb_reroot (ν : Measure ℝ) [IsProbabilityMeasure ν] {A : Set (RWRS.Net 1)}
    (hre : RWRS.RerootInvariant A) (N : RWRS.Net 0) (y : ℕ)
    (hadj : (RWRS.netGraph N).Adj (RWRS.netRoot N) y) :
    markProb ν A N = markProb ν A (RWRS.netReroot N y) := by
  have hpt : ∀ ξ : ℕ → ℝ,
      A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ))
        = A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (RWRS.netReroot N y, ξ)) := by
    intro ξ
    have hadj' : (RWRS.netGraph (markMap (N, ξ))).Adj
        (RWRS.netRoot (markMap (N, ξ))) y := hadj
    have hmem := hre (markMap (N, ξ)) y hadj'
    rw [← netReroot_markMap N ξ y]
    by_cases h : markMap (N, ξ) ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.1 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hmem.2 hc))]
  rw [markProb, markProb, markAvg, markAvg]
  exact congrArg ENNReal.toReal (lintegral_congr hpt)

/-- **The conditional probability of an invariant mark event is almost surely
the probability of the event.**  This is the first step of the proof of
`lem:ergodic-marked-stationary` at `rwrs.tex:315`. -/
theorem exists_markProb_ae_eq (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (herg : RWRS.IsErgodicNet Q)
    {A : Set (RWRS.Net 1)} (hA : MeasurableSet A) (hiso : RWRS.NetInvariantSet A)
    (hre : RWRS.RerootInvariant A) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧ (∀ᵐ N ∂Q, markProb ν A N = c) ∧
      RWRS.markIid Q ν A = ENNReal.ofReal c := by
  haveI : IsProbabilityMeasure (RWRS.markIid Q ν) := by
    rw [markIid_eq_map]
    exact Measure.isProbabilityMeasure_map measurable_markMap.aemeasurable
  obtain ⟨c, hc0, hc1, hae⟩ := ae_eq_const_of_isErgodicNet herg
    (measurable_markProb ν hA) (markProb_nonneg ν A) (markProb_le_one ν A)
    (markProb_invariant ν hA hiso) (fun N y hadj => markProb_reroot ν hre N y hadj)
  refine ⟨c, hc0, hc1, hae, ?_⟩
  have hmeasA : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) := (measurable_const).indicator hA
  have hval : RWRS.markIid Q ν A
      = ∫⁻ M, A.indicator (fun _ => (1 : ℝ≥0∞)) M ∂(RWRS.markIid Q ν) := by
    rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, one_mul]
  rw [hval, lintegral_markIid Q ν hmeasA]
  have hpt : ∀ᵐ N ∂Q, markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N = ENNReal.ofReal c := by
    filter_upwards [hae] with N hN
    have hne : markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (markAvg_indicator_le_one ν A N)
    rw [← hN, markProb, ENNReal.ofReal_toReal hne]
  rw [lintegral_congr_ae hpt, lintegral_const, measure_univ, mul_one]


end RWRS.Support
