/-
Averaging a function of a marked network over the marks outside a ball.

The proof of `lem:ergodic-marked-stationary` needs a function of the marked ball
of radius `r` around the root that approximates the indicator of an invariant
event.  The function is the average of that indicator over an independent
resampling of every mark outside the ball, and the resampling is the splice of
two independent copies of the mark field along the ball.  Splicing preserves the
field law, so the splice average has the same integral as the function itself,
and it reads the marks only inside the ball, which is what makes two such
averages at distant roots independent.
-/
import RWRS.Support.ErgReroot
import LatticeProb.Prob.Splice

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

/-- The mark field that reads `ξ` inside the ball of radius `r` around the root
of `N` and `η` outside it. -/
noncomputable def netComb (N : RWRS.Net 0) (r : ℕ) (ξ η : ℕ → ℝ) : ℕ → ℝ :=
  fun i => if i ∈ netBallX N r then ξ i else η i

theorem netComb_eq_comb (N : RWRS.Net 0) (r : ℕ) (ξ η : ℕ → ℝ) :
    netComb N r ξ η = LatticeProb.comb (netBallX N r) ξ η := by
  funext i
  by_cases h : i ∈ netBallX N r
  · rw [netComb, if_pos h, LatticeProb.comb_apply_of_mem h]
  · rw [netComb, if_neg h, LatticeProb.comb_apply_of_notMem h]

theorem netComb_of_mem {N : RWRS.Net 0} {r i : ℕ} (h : i ∈ netBallX N r) (ξ η : ℕ → ℝ) :
    netComb N r ξ η i = ξ i := by rw [netComb, if_pos h]

theorem netComb_of_notMem {N : RWRS.Net 0} {r i : ℕ} (h : i ∉ netBallX N r) (ξ η : ℕ → ℝ) :
    netComb N r ξ η i = η i := by rw [netComb, if_neg h]

theorem netComb_idem (N : RWRS.Net 0) (r : ℕ) (ξ η η' : ℕ → ℝ) :
    netComb N r (netComb N r ξ η) η' = netComb N r ξ η' := by
  funext i
  by_cases h : i ∈ netBallX N r
  · rw [netComb_of_mem h, netComb_of_mem h, netComb_of_mem h]
  · rw [netComb_of_notMem h, netComb_of_notMem h]

/-- **Splicing along a ball preserves the law of the mark field.** -/
theorem measurePreserving_netComb (ν : Measure ℝ) [IsProbabilityMeasure ν] (N : RWRS.Net 0)
    (r : ℕ) :
    MeasurePreserving (fun p : (ℕ → ℝ) × (ℕ → ℝ) => netComb N r p.1 p.2)
      ((RWRS.iidLaw ℕ ν).prod (RWRS.iidLaw ℕ ν)) (RWRS.iidLaw ℕ ν) := by
  have h := LatticeProb.measurePreserving_comb (X := fun _ : ℕ => ℝ) (fun _ : ℕ => ν)
    (netBallX N r)
  have hfun : (fun p : (ℕ → ℝ) × (ℕ → ℝ) => netComb N r p.1 p.2)
      = fun p : (ℕ → ℝ) × (ℕ → ℝ) => LatticeProb.comb (netBallX N r) p.1 p.2 :=
    funext fun p => netComb_eq_comb N r p.1 p.2
  rw [hfun]
  exact h

theorem measurable_netComb (r : ℕ) :
    Measurable fun p : RWRS.Net 0 × (ℕ → ℝ) × (ℕ → ℝ) => netComb p.1 r p.2.1 p.2.2 := by
  refine measurable_pi_lambda _ fun i => ?_
  have hset : MeasurableSet {p : RWRS.Net 0 × (ℕ → ℝ) × (ℕ → ℝ) | i ∈ netBallX p.1 r} :=
    measurable_fst (measurableSet_mem_netBallX i r)
  exact Measurable.ite hset (((measurable_pi_apply i).comp measurable_fst).comp measurable_snd)
    (((measurable_pi_apply i).comp measurable_snd).comp measurable_snd)

/-- The average of `h` over an independent resampling of every mark outside the
ball of radius `r` around the root. -/
noncomputable def ballAvg (ν : Measure ℝ) (r : ℕ) (h : RWRS.Net 1 → ℝ≥0∞)
    (N : RWRS.Net 0) (ξ : ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ η, h (markMap (N, netComb N r ξ η)) ∂(RWRS.iidLaw ℕ ν)

theorem measurable_ballAvg (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ)
    {h : RWRS.Net 1 → ℝ≥0∞} (hm : Measurable h) :
    Measurable fun p : RWRS.Net 0 × (ℕ → ℝ) => ballAvg ν r h p.1 p.2 := by
  have hre : Measurable fun q : (RWRS.Net 0 × (ℕ → ℝ)) × (ℕ → ℝ) =>
      ((q.1.1, (q.1.2, q.2)) : RWRS.Net 0 × (ℕ → ℝ) × (ℕ → ℝ)) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have h3 : Measurable fun q : (RWRS.Net 0 × (ℕ → ℝ)) × (ℕ → ℝ) =>
      markMap (q.1.1, netComb q.1.1 r q.1.2 q.2) :=
    measurable_markMap.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_netComb r).comp hre))
  have huc : Measurable (Function.uncurry fun (p : RWRS.Net 0 × (ℕ → ℝ)) (η : ℕ → ℝ) =>
      h (markMap (p.1, netComb p.1 r p.2 η))) := hm.comp h3
  exact huc.lintegral_prod_right'

theorem ballAvg_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ)
    {h : RWRS.Net 1 → ℝ≥0∞} (hle : ∀ M, h M ≤ 1) (N : RWRS.Net 0) (ξ : ℕ → ℝ) :
    ballAvg ν r h N ξ ≤ 1 := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw ℕ ν) := instIsProbabilityMeasureIidLaw ν
  have h1 : ballAvg ν r h N ξ ≤ ∫⁻ _η : ℕ → ℝ, (1 : ℝ≥0∞) ∂(RWRS.iidLaw ℕ ν) :=
    lintegral_mono fun η => hle _
  rwa [lintegral_const, measure_univ, mul_one] at h1

/-- **The splice average reads the marks only inside the ball.** -/
theorem ballAvg_netComb (ν : Measure ℝ) (r : ℕ) (h : RWRS.Net 1 → ℝ≥0∞) (N : RWRS.Net 0)
    (ξ η : ℕ → ℝ) : ballAvg ν r h N (netComb N r ξ η) = ballAvg ν r h N ξ := by
  simp only [ballAvg]
  exact lintegral_congr fun η' => by rw [netComb_idem]

/-- **The splice average has the same mark average as the function itself.** -/
theorem lintegral_ballAvg (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ)
    {h : RWRS.Net 1 → ℝ≥0∞} (hm : Measurable h) (N : RWRS.Net 0) :
    ∫⁻ ξ, ballAvg ν r h N ξ ∂(RWRS.iidLaw ℕ ν) = markAvg ν h N := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw ℕ ν) := instIsProbabilityMeasureIidLaw ν
  have hmc : Measurable fun ζ : ℕ → ℝ => h (markMap (N, ζ)) :=
    (hm.comp measurable_markMap).comp ((measurable_const (a := N)).prodMk measurable_id)
  have hprod : ∫⁻ p : (ℕ → ℝ) × (ℕ → ℝ), h (markMap (N, netComb N r p.1 p.2))
      ∂((RWRS.iidLaw ℕ ν).prod (RWRS.iidLaw ℕ ν)) = ∫⁻ ζ, h (markMap (N, ζ)) ∂(RWRS.iidLaw ℕ ν) :=
    (measurePreserving_netComb ν N r).lintegral_comp hmc
  have hdef : markAvg ν h N = ∫⁻ ζ, h (markMap (N, ζ)) ∂(RWRS.iidLaw ℕ ν) := rfl
  have hae : AEMeasurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => h (markMap (N, netComb N r p.1 p.2)))
      ((RWRS.iidLaw ℕ ν).prod (RWRS.iidLaw ℕ ν)) :=
    (hmc.comp (measurePreserving_netComb ν N r).measurable).aemeasurable
  rw [hdef, ← hprod, lintegral_prod _ hae]
  rfl

/-! ### The distance between two values of `[0,∞]` -/

/-- The distance between two values of `[0,∞]`, written with the truncated
subtraction so that no sign appears. -/
noncomputable def esub (x y : ℝ≥0∞) : ℝ≥0∞ := (x - y) + (y - x)

theorem esub_comm (x y : ℝ≥0∞) : esub x y = esub y x := by
  simp only [esub]; ring

@[simp] theorem esub_self (x : ℝ≥0∞) : esub x x = 0 := by simp [esub]

theorem le_add_esub (x y : ℝ≥0∞) : x ≤ y + esub x y := by
  refine le_trans (le_add_tsub (a := x) (b := y)) ?_
  gcongr
  exact le_self_add

theorem esub_le_of_le_add {x y d : ℝ≥0∞} (h1 : x ≤ y + d) (h2 : y ≤ x + d) : esub x y ≤ d := by
  rcases le_total x y with h | h
  · rw [esub, tsub_eq_zero_of_le h, zero_add, tsub_le_iff_left]
    exact h2
  · rw [esub, tsub_eq_zero_of_le h, add_zero, tsub_le_iff_left]
    exact h1

theorem esub_triangle (x y z : ℝ≥0∞) : esub x z ≤ esub x y + esub y z := by
  refine esub_le_of_le_add ?_ ?_
  · calc x ≤ y + esub x y := le_add_esub x y
      _ ≤ (z + esub y z) + esub x y := by gcongr; exact le_add_esub y z
      _ = z + (esub x y + esub y z) := by ring
  · calc z ≤ y + esub z y := le_add_esub z y
      _ ≤ (x + esub y x) + esub z y := by gcongr; exact le_add_esub y x
      _ = x + (esub x y + esub y z) := by rw [esub_comm y x, esub_comm z y]; ring

theorem measurable_esub {α : Type*} [MeasurableSpace α] {f g : α → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => esub (f a) (g a) :=
  (hf.sub hg).add (hg.sub hf)

theorem esub_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    esub (∫⁻ a, f a ∂μ) (∫⁻ a, g a ∂μ) ≤ ∫⁻ a, esub (f a) (g a) ∂μ := by
  refine esub_le_of_le_add ?_ ?_
  · calc ∫⁻ a, f a ∂μ ≤ ∫⁻ a, (g a + esub (f a) (g a)) ∂μ :=
        lintegral_mono fun a => le_add_esub (f a) (g a)
      _ = ∫⁻ a, g a ∂μ + ∫⁻ a, esub (f a) (g a) ∂μ := lintegral_add_left hg _
  · calc ∫⁻ a, g a ∂μ ≤ ∫⁻ a, (f a + esub (g a) (f a)) ∂μ :=
        lintegral_mono fun a => le_add_esub (g a) (f a)
      _ = ∫⁻ a, f a ∂μ + ∫⁻ a, esub (g a) (f a) ∂μ := lintegral_add_left hf _
      _ = ∫⁻ a, f a ∂μ + ∫⁻ a, esub (f a) (g a) ∂μ := by
          rw [lintegral_congr fun a => esub_comm (g a) (f a)]

theorem esub_indicator {α : Type*} (S T : Set α) (a : α) :
    esub (S.indicator (fun _ => (1 : ℝ≥0∞)) a) (T.indicator (fun _ => (1 : ℝ≥0∞)) a)
      = (symmDiff S T).indicator (fun _ => (1 : ℝ≥0∞)) a := by
  by_cases hS : a ∈ S <;> by_cases hT : a ∈ T <;>
    simp [esub, hS, hT, Set.mem_symmDiff]

/-! ### The events that read only the marks inside a ball -/

/-- A measurable set of mark fields that reads only the marks inside the ball of
some radius around the root of `N`. -/
def ballLocalSets (N : RWRS.Net 0) : Set (Set (ℕ → ℝ)) :=
  {S | MeasurableSet S ∧ ∃ r : ℕ, ∀ ξ η : ℕ → ℝ, (netComb N r ξ η ∈ S ↔ ξ ∈ S)}

theorem netComb_netComb_of_le {N : RWRS.Net 0} {r s : ℕ} (hrs : r ≤ s) (ξ η : ℕ → ℝ) :
    netComb N r ξ (netComb N s ξ η) = netComb N s ξ η := by
  funext i
  by_cases h : i ∈ netBallX N r
  · rw [netComb_of_mem h, netComb_of_mem (netBallX_mono N hrs h)]
  · rw [netComb_of_notMem h]

theorem ballLocal_of_le {N : RWRS.Net 0} {S : Set (ℕ → ℝ)} {r : ℕ}
    (hr : ∀ ξ η : ℕ → ℝ, (netComb N r ξ η ∈ S ↔ ξ ∈ S)) {s : ℕ} (hrs : r ≤ s) :
    ∀ ξ η : ℕ → ℝ, (netComb N s ξ η ∈ S ↔ ξ ∈ S) := by
  intro ξ η
  have := hr ξ (netComb N s ξ η)
  rwa [netComb_netComb_of_le hrs] at this

theorem isSetRing_ballLocalSets (N : RWRS.Net 0) : MeasureTheory.IsSetRing (ballLocalSets N) where
  empty_mem := ⟨MeasurableSet.empty, 0, fun _ _ => Iff.rfl⟩
  union_mem := by
    rintro S T ⟨hS, rS, hrS⟩ ⟨hT, rT, hrT⟩
    refine ⟨hS.union hT, max rS rT, fun ξ η => ?_⟩
    have h1 := ballLocal_of_le hrS (le_max_left rS rT) ξ η
    have h2 := ballLocal_of_le hrT (le_max_right rS rT) ξ η
    simp only [Set.mem_union]
    exact or_congr h1 h2
  sdiff_mem := by
    rintro S T ⟨hS, rS, hrS⟩ ⟨hT, rT, hrT⟩
    refine ⟨hS.diff hT, max rS rT, fun ξ η => ?_⟩
    have h1 := ballLocal_of_le hrS (le_max_left rS rT) ξ η
    have h2 := ballLocal_of_le hrT (le_max_right rS rT) ξ η
    simp only [Set.mem_sdiff]
    exact and_congr h1 (not_congr h2)

theorem generateFrom_ballLocalSets (N : RWRS.Net 0) :
    (inferInstance : MeasurableSpace (ℕ → ℝ)) = MeasurableSpace.generateFrom (ballLocalSets N) := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun S hS => hS.1)
  refine iSup_le fun i => ?_
  rintro _ ⟨B, hB, rfl⟩
  obtain ⟨r, hr⟩ := exists_mem_netBallX N i
  refine MeasurableSpace.measurableSet_generateFrom ⟨?_, r, fun ξ η => ?_⟩
  · exact (measurable_pi_apply i) hB
  · simp only [Set.mem_preimage, netComb_of_mem hr]

theorem indicator_markMap (A : Set (RWRS.Net 1)) (N : RWRS.Net 0) (ξ : ℕ → ℝ) :
    A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ))
      = ((fun ζ : ℕ → ℝ => markMap (N, ζ)) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) ξ := by
  by_cases h : markMap (N, ξ) ∈ A
  · rw [Set.indicator_of_mem h,
      Set.indicator_of_mem (show ξ ∈ (fun ζ : ℕ → ℝ => markMap (N, ζ)) ⁻¹' A from h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (show ξ ∉ (fun ζ : ℕ → ℝ => markMap (N, ζ)) ⁻¹' A from h)]

/-- The splice average of radius `r` is within the measure of a symmetric
difference of the indicator, for every event that reads only the marks inside
the ball of radius `r`. -/
theorem lintegral_esub_ballAvg_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (N : RWRS.Net 0)
    (r : ℕ) {A : Set (RWRS.Net 1)} (hA : MeasurableSet A) {T : Set (ℕ → ℝ)}
    (hTmeas : MeasurableSet T) (hTloc : ∀ ξ η : ℕ → ℝ, (netComb N r ξ η ∈ T ↔ ξ ∈ T)) :
    ∫⁻ ξ, esub (A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ)))
        (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ) ∂(RWRS.iidLaw ℕ ν)
      ≤ 2 * (RWRS.iidLaw ℕ ν) (symmDiff T ((fun ζ : ℕ → ℝ => markMap (N, ζ)) ⁻¹' A)) := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw ℕ ν) := instIsProbabilityMeasureIidLaw ν
  set P : Measure (ℕ → ℝ) := RWRS.iidLaw ℕ ν with hP
  set S : Set (ℕ → ℝ) := (fun ζ : ℕ → ℝ => markMap (N, ζ)) ⁻¹' A with hS
  have hSmeas : MeasurableSet S :=
    (measurable_markMap.comp ((measurable_const (a := N)).prodMk measurable_id)) hA
  set u : (ℕ → ℝ) → ℝ≥0∞ := S.indicator (fun _ => (1 : ℝ≥0∞)) with hu
  have humeas : Measurable u := measurable_const.indicator hSmeas
  set v : (ℕ → ℝ) → ℝ≥0∞ := T.indicator (fun _ => (1 : ℝ≥0∞)) with hv
  have hvmeas : Measurable v := measurable_const.indicator hTmeas
  have hball : ∀ ξ : ℕ → ℝ,
      ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ = ∫⁻ η, u (netComb N r ξ η) ∂P := by
    intro ξ
    simp only [ballAvg, hP]
    exact lintegral_congr fun η => indicator_markMap A N _
  have hstep1 : ∀ ξ : ℕ → ℝ,
      esub (A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ)))
          (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ)
        ≤ esub (u ξ) (v ξ)
          + esub (v ξ) (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ) := by
    intro ξ
    rw [indicator_markMap A N ξ]
    exact esub_triangle _ _ _
  have hsplit : ∫⁻ ξ, esub (A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ)))
        (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ) ∂P
      ≤ (∫⁻ ξ, esub (u ξ) (v ξ) ∂P)
        + ∫⁻ ξ, esub (v ξ) (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ) ∂P := by
    refine le_trans (lintegral_mono hstep1) ?_
    exact le_of_eq (lintegral_add_left (measurable_esub humeas hvmeas) _)
  have hfirst : ∫⁻ ξ, esub (u ξ) (v ξ) ∂P = P (symmDiff S T) := by
    rw [lintegral_congr fun ξ => esub_indicator S T ξ, lintegral_indicator (hSmeas.symmDiff hTmeas),
      lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul]
  have hvconst : ∀ ξ : ℕ → ℝ, v ξ = ∫⁻ η, v (netComb N r ξ η) ∂P := by
    intro ξ
    have hcst : ∀ η : ℕ → ℝ, v (netComb N r ξ η) = v ξ := by
      intro η
      simp only [hv]
      by_cases h : ξ ∈ T
      · rw [Set.indicator_of_mem ((hTloc ξ η).2 h), Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem (fun hc => h ((hTloc ξ η).1 hc)),
          Set.indicator_of_notMem h]
    rw [lintegral_congr hcst, lintegral_const, measure_univ, mul_one]
  have hsecond : ∫⁻ ξ, esub (v ξ) (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ) ∂P
      ≤ P (symmDiff T S) := by
    have hpt : ∀ ξ : ℕ → ℝ,
        esub (v ξ) (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ)
          ≤ ∫⁻ η, esub (v (netComb N r ξ η)) (u (netComb N r ξ η)) ∂P := by
      intro ξ
      rw [hball ξ, hvconst ξ]
      exact esub_lintegral_le (hvmeas.comp ((measurable_netComb r).comp
          (((measurable_const (a := N)).prodMk ((measurable_const (a := ξ)).prodMk
            measurable_id)))))
        (humeas.comp ((measurable_netComb r).comp
          (((measurable_const (a := N)).prodMk ((measurable_const (a := ξ)).prodMk
            measurable_id)))))
    refine le_trans (lintegral_mono hpt) (le_of_eq ?_)
    have hprod : ∫⁻ p : (ℕ → ℝ) × (ℕ → ℝ), esub (v (netComb N r p.1 p.2)) (u (netComb N r p.1 p.2))
        ∂(P.prod P) = ∫⁻ ζ, esub (v ζ) (u ζ) ∂P :=
      (measurePreserving_netComb ν N r).lintegral_comp (measurable_esub hvmeas humeas)
    have hae : AEMeasurable
        (fun p : (ℕ → ℝ) × (ℕ → ℝ) => esub (v (netComb N r p.1 p.2)) (u (netComb N r p.1 p.2)))
        (P.prod P) :=
      ((measurable_esub hvmeas humeas).comp
        (measurePreserving_netComb ν N r).measurable).aemeasurable
    rw [← lintegral_prod _ hae, hprod,
      lintegral_congr fun ζ => esub_indicator T S ζ,
      lintegral_indicator (hTmeas.symmDiff hSmeas), lintegral_const,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, one_mul]
  refine le_trans hsplit ?_
  rw [hfirst, symmDiff_comm S T, two_mul]
  exact add_le_add le_rfl hsecond

/-! ### A single radius for the law of the network and the marks together -/

/-- A measurable set of pairs (network, mark field) that reads the marks only
inside the ball of some radius around the root. -/
def prodLocalSets : Set (Set (RWRS.Net 0 × (ℕ → ℝ))) :=
  {T | MeasurableSet T ∧ ∃ r : ℕ, ∀ (N : RWRS.Net 0) (ξ η : ℕ → ℝ),
    ((N, netComb N r ξ η) ∈ T ↔ (N, ξ) ∈ T)}

theorem prodLocal_of_le {T : Set (RWRS.Net 0 × (ℕ → ℝ))} {r : ℕ}
    (hr : ∀ (N : RWRS.Net 0) (ξ η : ℕ → ℝ), ((N, netComb N r ξ η) ∈ T ↔ (N, ξ) ∈ T)) {s : ℕ}
    (hrs : r ≤ s) : ∀ (N : RWRS.Net 0) (ξ η : ℕ → ℝ), ((N, netComb N s ξ η) ∈ T ↔ (N, ξ) ∈ T) := by
  intro N ξ η
  have h := hr N ξ (netComb N s ξ η)
  rwa [netComb_netComb_of_le hrs] at h

theorem isSetRing_prodLocalSets : MeasureTheory.IsSetRing prodLocalSets where
  empty_mem := ⟨MeasurableSet.empty, 0, fun _ _ _ => Iff.rfl⟩
  union_mem := by
    rintro S T ⟨hS, rS, hrS⟩ ⟨hT, rT, hrT⟩
    refine ⟨hS.union hT, max rS rT, fun N ξ η => ?_⟩
    exact or_congr (prodLocal_of_le hrS (le_max_left rS rT) N ξ η)
      (prodLocal_of_le hrT (le_max_right rS rT) N ξ η)
  sdiff_mem := by
    rintro S T ⟨hS, rS, hrS⟩ ⟨hT, rT, hrT⟩
    refine ⟨hS.diff hT, max rS rT, fun N ξ η => ?_⟩
    exact and_congr (prodLocal_of_le hrS (le_max_left rS rT) N ξ η)
      (not_congr (prodLocal_of_le hrT (le_max_right rS rT) N ξ η))

theorem generateFrom_prodLocalSets :
    (inferInstance : MeasurableSpace (RWRS.Net 0 × (ℕ → ℝ)))
      = MeasurableSpace.generateFrom prodLocalSets := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le fun T hT => hT.1)
  refine sup_le ?_ ?_
  · rintro _ ⟨B, hB, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨measurable_fst hB, 0, fun _ _ _ => Iff.rfl⟩
  · rw [show (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ))
        = ⨆ i : ℕ, (inferInstance : MeasurableSpace ℝ).comap (fun f : ℕ → ℝ => f i) from rfl,
      MeasurableSpace.comap_iSup]
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_comp]
    rintro _ ⟨E, hE, rfl⟩
    have hunion : ((fun f : ℕ → ℝ => f i) ∘ (Prod.snd : RWRS.Net 0 × (ℕ → ℝ) → ℕ → ℝ)) ⁻¹' E
        = ⋃ r : ℕ, {p : RWRS.Net 0 × (ℕ → ℝ) | i ∈ netBallX p.1 r ∧ p.2 i ∈ E} := by
      ext p
      simp only [Set.mem_preimage, Function.comp_apply, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro hp
        obtain ⟨r, hr⟩ := exists_mem_netBallX p.1 i
        exact ⟨r, hr, hp⟩
      · rintro ⟨r, -, hp⟩
        exact hp
    rw [hunion]
    refine MeasurableSet.iUnion fun r => MeasurableSpace.measurableSet_generateFrom ⟨?_, r, ?_⟩
    · exact (measurable_fst (measurableSet_mem_netBallX i r)).inter
        (((measurable_pi_apply i).comp measurable_snd) hE)
    · intro N ξ η
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [netComb_of_mem h1] at h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [netComb_of_mem h1]⟩

/-- **A single radius approximates the event for the law of the network and the
marks together.**  This is the approximation of `rwrs.tex:317`. -/
theorem exists_ballAvg_approx (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {A : Set (RWRS.Net 1)} (hA : MeasurableSet A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ r : ℕ, ∫⁻ N, (∫⁻ ξ, esub (A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ)))
        (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ) ∂(RWRS.iidLaw ℕ ν)) ∂Q < ε := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw ℕ ν) := instIsProbabilityMeasureIidLaw ν
  set μ : Measure (RWRS.Net 0 × (ℕ → ℝ)) := Q.prod (RWRS.iidLaw ℕ ν) with hμ
  set S : Set (RWRS.Net 0 × (ℕ → ℝ)) := markMap ⁻¹' A with hS
  have hSmeas : MeasurableSet S := measurable_markMap hA
  obtain ⟨T, hT, hTlt⟩ := MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (μ := μ) isSetRing_prodLocalSets
    ⟨{Set.univ}, Set.countable_singleton _,
      by simpa using ⟨MeasurableSet.univ, 0, fun _ _ _ => Iff.rfl⟩, by simp⟩
    generateFrom_prodLocalSets hSmeas (ENNReal.half_pos hε.ne')
  obtain ⟨hTmeas, r, hTloc⟩ := hT
  refine ⟨r, ?_⟩
  have hfib : ∀ N : RWRS.Net 0, ∫⁻ ξ, esub (A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ)))
        (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ) ∂(RWRS.iidLaw ℕ ν)
      ≤ 2 * (RWRS.iidLaw ℕ ν) (Prod.mk N ⁻¹' symmDiff T S) := by
    intro N
    have hle := lintegral_esub_ballAvg_le ν N r hA (measurable_prodMk_left hTmeas)
      (fun ξ η => hTloc N ξ η)
    have hset : symmDiff (Prod.mk N ⁻¹' T) ((fun ζ : ℕ → ℝ => markMap (N, ζ)) ⁻¹' A)
        = Prod.mk N ⁻¹' symmDiff T S := rfl
    rwa [hset] at hle
  refine lt_of_le_of_lt (lintegral_mono hfib) ?_
  rw [lintegral_const_mul 2 ((measurable_measure_prodMk_left (hTmeas.symmDiff hSmeas)))]
  rw [← Measure.prod_apply (hTmeas.symmDiff hSmeas)]
  have h2 : μ (symmDiff T S) * 2 < ε / 2 * 2 :=
    ENNReal.mul_lt_mul_left two_ne_zero ENNReal.ofNat_ne_top hTlt
  rw [ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top] at h2
  rwa [mul_comm]

end RWRS.Support
