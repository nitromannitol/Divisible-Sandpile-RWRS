/-
Disjoint blocks of the scenery, and the two correlation bounds Step 1 of
`prop:doubly-transient-really-general` needs.

The trap sets selected along the walk are pairwise disjoint and are functions of
the walk alone, so conditionally on the walk the events `A_{Y_i}` read disjoint
blocks of coordinates of the i.i.d. scenery.  Two facts follow, and they are the
whole of the paper's bookkeeping: a coordinate outside every block used is
independent of the conditioning and, being centred, contributes nothing; and a
coordinate inside an earlier block contributes at most `E|ξ|` times the
probability of the conditioning, divided by the probability of the block event
it sits in.
-/
import RWRS.Support.DTAdmissible
import LatticeProb.Prob.Blocks

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

variable {V : Type*} {ν : Measure ℝ}

open scoped Classical in
/-- Filling the coordinates outside `S` with zero. -/
noncomputable def blockExtend (S : Set V) (z : ↥S → ℝ) : V → ℝ :=
  fun w => if h : w ∈ S then z ⟨w, h⟩ else 0

theorem measurable_blockExtend (S : Set V) : Measurable (blockExtend (V := V) S) := by
  classical
  refine measurable_pi_lambda _ fun w => ?_
  by_cases h : w ∈ S
  · simpa [blockExtend, h] using measurable_pi_apply (⟨w, h⟩ : ↥S)
  · simp [blockExtend, h]

theorem blockExtend_restrict {S : Set V} (ξ : V → ℝ) {w : V} (hw : w ∈ S) :
    blockExtend S (S.restrict ξ) w = ξ w := by
  classical
  simp [blockExtend, hw, Set.restrict]

/-- **Disjoint blocks of coordinates of an i.i.d. field are independent.** -/
theorem indepFun_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν] {S T : Set V}
    (hd : Disjoint S T) :
    IndepFun (fun ω : V → ℝ => S.restrict ω) (fun ω : V → ℝ => T.restrict ω)
      (RWRS.iidLaw V ν) := by
  classical
  have hdisj : Pairwise (Function.onFun Disjoint (fun b : Bool => if b then S else T)) := by
    intro a b hab
    cases a <;> cases b <;> simp_all [Function.onFun, hd.symm]
  have h := LatticeProb.iIndepFun_restrict_of_pairwise_disjoint (V := V) ν
    (fun b : Bool => if b then S else T) hdisj
  exact h.indepFun (show (true : Bool) ≠ false by decide)

/-- **Two functions of disjoint blocks of coordinates are uncorrelated.** -/
theorem integral_mul_of_disjoint (ν : Measure ℝ) [IsProbabilityMeasure ν] {S T : Set V}
    (hd : Disjoint S T) {f g : (V → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ ξ η : V → ℝ, (∀ w ∈ S, ξ w = η w) → f ξ = f η)
    (hgT : ∀ ξ η : V → ℝ, (∀ w ∈ T, ξ w = η w) → g ξ = g η) :
    ∫ ξ, f ξ * g ξ ∂(RWRS.iidLaw V ν)
      = (∫ ξ, f ξ ∂(RWRS.iidLaw V ν)) * (∫ ξ, g ξ ∂(RWRS.iidLaw V ν)) := by
  classical
  have hfeq : f = (f ∘ blockExtend S) ∘ (fun ω : V → ℝ => S.restrict ω) := by
    funext ξ
    exact hfS _ _ fun w hw => (blockExtend_restrict ξ hw).symm
  have hgeq : g = (g ∘ blockExtend T) ∘ (fun ω : V → ℝ => T.restrict ω) := by
    funext ξ
    exact hgT _ _ fun w hw => (blockExtend_restrict ξ hw).symm
  have hind : IndepFun f g (RWRS.iidLaw V ν) := by
    rw [hfeq, hgeq]
    exact (indepFun_restrict ν hd).comp (hf.comp (measurable_blockExtend S))
      (hg.comp (measurable_blockExtend T))
  exact hind.integral_fun_mul_eq_mul_integral hf.aestronglyMeasurable hg.aestronglyMeasurable

/-- **A centred coordinate outside a block is uncorrelated with a function of the
block.** -/
theorem integral_coord_mul_of_notMem (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h0 : RWRS.extMean ν = 0) {S : Set V} {v : V} (hv : v ∉ S) {g : (V → ℝ) → ℝ}
    (hg : Measurable g) (hgS : ∀ ξ η : V → ℝ, (∀ w ∈ S, ξ w = η w) → g ξ = g η) :
    ∫ ξ, ξ v * g ξ ∂(RWRS.iidLaw V ν) = 0 := by
  have hd : Disjoint ({v} : Set V) S := by simpa using hv
  have hf : Measurable fun ξ : V → ℝ => ξ v := measurable_pi_apply v
  have hfS : ∀ ξ η : V → ℝ, (∀ w ∈ ({v} : Set V), ξ w = η w) → ξ v = η v :=
    fun ξ η h => h v rfl
  rw [integral_mul_of_disjoint ν hd hf hg hfS hgS]
  have hzero : ∫ ξ : V → ℝ, ξ v ∂(RWRS.iidLaw V ν) = 0 := by
    have := integral_coord (V := V) ν v (f := fun z : ℝ => z) aestronglyMeasurable_id
    rw [this]
    exact integral_id_zero h0
  rw [hzero, zero_mul]

/-- **The measures of events reading disjoint blocks multiply.** -/
theorem measure_inter_of_disjoint (ν : Measure ℝ) [IsProbabilityMeasure ν] {S T : Set V}
    (hd : Disjoint S T) {A B : Set (V → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : ∀ ξ η : V → ℝ, (∀ w ∈ S, ξ w = η w) → (ξ ∈ A ↔ η ∈ A))
    (hBT : ∀ ξ η : V → ℝ, (∀ w ∈ T, ξ w = η w) → (ξ ∈ B ↔ η ∈ B)) :
    RWRS.iidLaw V ν (A ∩ B) = RWRS.iidLaw V ν A * RWRS.iidLaw V ν B := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have hfun : ∀ ξ : V → ℝ,
      (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ
        = A.indicator (fun _ => (1 : ℝ)) ξ * B.indicator (fun _ => (1 : ℝ)) ξ := by
    intro ξ
    by_cases ha : ξ ∈ A <;> by_cases hb : ξ ∈ B <;>
      simp [ha, hb, Set.mem_inter_iff]
  have hmul := integral_mul_of_disjoint ν hd
    (g := B.indicator (fun _ => (1 : ℝ))) (f := A.indicator (fun _ => (1 : ℝ)))
    ((measurable_const.indicator hA)) ((measurable_const.indicator hB))
    (fun ξ η h => by
      by_cases hx : ξ ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hAS ξ η h).1 hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hc => hx ((hAS ξ η h).2 hc))])
    (fun ξ η h => by
      by_cases hx : ξ ∈ B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hBT ξ η h).1 hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hc => hx ((hBT ξ η h).2 hc))])
  have hAB : MeasurableSet (A ∩ B) := hA.inter hB
  have hEq : ∫ ξ, (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      = (∫ ξ, A.indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν))
        * ∫ ξ, B.indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν) := by
    rw [← hmul]
    exact integral_congr_ae (Filter.Eventually.of_forall hfun)
  rw [integral_indicator_const _ hAB, integral_indicator_const _ hA,
    integral_indicator_const _ hB] at hEq
  simp only [smul_eq_mul, mul_one] at hEq
  have h1 : RWRS.iidLaw V ν (A ∩ B) ≠ ⊤ := measure_ne_top _ _
  have h2 : RWRS.iidLaw V ν A ≠ ⊤ := measure_ne_top _ _
  have h3 : RWRS.iidLaw V ν B ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.toReal_eq_toReal_iff' h1 (ENNReal.mul_ne_top h2 h3), ENNReal.toReal_mul]
  simpa [measureReal_def] using hEq

/-- **The bias of a coordinate of an earlier block.**  Under an event that is the
intersection of an event of the block containing `v` with an event of the other
blocks, the mean of `ξ(v)` is at most `E|ξ|` times the probability of the second
event. -/
theorem abs_integral_coord_mul_indicator_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℝ => z) ν)
    {S T : Set V} (hd : Disjoint S T) {v : V} (hv : v ∈ S)
    {A B : Set (V → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : ∀ ξ η : V → ℝ, (∀ w ∈ S, ξ w = η w) → (ξ ∈ A ↔ η ∈ A))
    (hBT : ∀ ξ η : V → ℝ, (∀ w ∈ T, ξ w = η w) → (ξ ∈ B ↔ η ∈ B)) :
    |∫ ξ, ξ v * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)|
      ≤ (∫ z, |z| ∂ν) * (RWRS.iidLaw V ν B).toReal := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  set μ : Measure (V → ℝ) := RWRS.iidLaw V ν with hμ
  have hfun : ∀ ξ : V → ℝ,
      ξ v * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ
        = (ξ v * A.indicator (fun _ => (1 : ℝ)) ξ) * B.indicator (fun _ => (1 : ℝ)) ξ := by
    intro ξ
    by_cases ha : ξ ∈ A <;> by_cases hb : ξ ∈ B <;>
      simp [ha, hb, Set.mem_inter_iff]
  have hfmeas : Measurable fun ξ : V → ℝ => ξ v * A.indicator (fun _ => (1 : ℝ)) ξ :=
    (measurable_pi_apply v).mul (measurable_const.indicator hA)
  have hmul := integral_mul_of_disjoint ν hd
    (f := fun ξ : V → ℝ => ξ v * A.indicator (fun _ => (1 : ℝ)) ξ)
    (g := B.indicator (fun _ => (1 : ℝ))) hfmeas (measurable_const.indicator hB)
    (fun ξ η h => by
      have hvv : ξ v = η v := h v hv
      by_cases hx : ξ ∈ A
      · rw [hvv, Set.indicator_of_mem hx, Set.indicator_of_mem ((hAS ξ η h).1 hx)]
      · rw [hvv, Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (fun hc => hx ((hAS ξ η h).2 hc))])
    (fun ξ η h => by
      by_cases hx : ξ ∈ B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hBT ξ η h).1 hx)]
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (fun hc => hx ((hBT ξ η h).2 hc))])
  rw [integral_congr_ae (Filter.Eventually.of_forall hfun), hmul,
    integral_indicator_const _ hB]
  simp only [smul_eq_mul, mul_one, abs_mul]
  have hBnn : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  have hcoord : Integrable (fun ξ : V → ℝ => ξ v) μ := integrable_coord ν v hint
  have habs : |∫ ξ, ξ v * A.indicator (fun _ => (1 : ℝ)) ξ ∂μ| ≤ ∫ z, |z| ∂ν := by
    have hint1 : Integrable (fun ξ : V → ℝ => ξ v * A.indicator (fun _ => (1 : ℝ)) ξ) μ := by
      refine Integrable.mono' hcoord.abs hfmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => ?_)
      by_cases hx : ξ ∈ A <;> simp [hx, Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs).trans ?_
    have hle : ∀ ξ : V → ℝ, |ξ v * A.indicator (fun _ => (1 : ℝ)) ξ| ≤ |ξ v| := by
      intro ξ
      by_cases hx : ξ ∈ A <;> simp [hx]
    refine (integral_mono hint1.abs hcoord.abs hle).trans (le_of_eq ?_)
    exact integral_coord (V := V) ν v (f := fun z : ℝ => |z|) (by fun_prop)
  have habs2 : |(RWRS.iidLaw V ν).real B| = (μ B).toReal := by
    rw [measureReal_def, ← hμ]
    exact abs_of_nonneg hBnn
  rw [habs2]
  exact mul_le_mul_of_nonneg_right habs hBnn

/-! ### Weighted sums under a block event -/

open scoped Classical in
/-- **The sites outside the blocks contribute nothing.**  A weighted sum of the
scenery over sites none of which the event reads has mean zero under that event. -/
theorem integral_sum_outside_eq_zero (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h0 : RWRS.extMean ν = 0) (K F : Finset V) (w : V → ℝ) {E : Set (V → ℝ)}
    (hE : MeasurableSet E)
    (hEF : ∀ ξ η : V → ℝ, (∀ u ∈ (F : Set V), ξ u = η u) → (ξ ∈ E ↔ η ∈ E)) :
    ∫ ξ, (∑ v ∈ K \ F, w v * ξ v) * E.indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν) = 0 := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  have hEmeas : Measurable (E.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hE
  have hgdep : ∀ ξ η : V → ℝ, (∀ u ∈ (F : Set V), ξ u = η u) →
      E.indicator (fun _ => (1 : ℝ)) ξ = E.indicator (fun _ => (1 : ℝ)) η := by
    intro ξ η h
    by_cases hx : ξ ∈ E
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hEF ξ η h).1 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun hc => hx ((hEF ξ η h).2 hc))]
  have hterm : ∀ v ∈ K \ F,
      ∫ ξ, (w v * ξ v) * E.indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν) = 0 := by
    intro v hv
    have hvF : v ∉ (F : Set V) := by
      intro hc
      exact (Finset.mem_sdiff.1 hv).2 (by exact_mod_cast hc)
    have hzero := integral_coord_mul_of_notMem ν h0 hvF hEmeas hgdep
    have hcongr : ∀ ξ : V → ℝ, (w v * ξ v) * E.indicator (fun _ => (1 : ℝ)) ξ
        = w v * (ξ v * E.indicator (fun _ => (1 : ℝ)) ξ) := fun ξ => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hcongr), integral_const_mul, hzero,
      mul_zero]
  have hint : ∀ v ∈ K \ F,
      Integrable (fun ξ : V → ℝ => (w v * ξ v) * E.indicator (fun _ => (1 : ℝ)) ξ)
        (RWRS.iidLaw V ν) := by
    intro v _
    have hc : Integrable (fun ξ : V → ℝ => ξ v) (RWRS.iidLaw V ν) :=
      integrable_coord ν v (integrable_id_of_extMean_zero h0)
    refine Integrable.mono' (hc.abs.const_mul |w v|)
      (((measurable_pi_apply v).const_mul (w v)).mul hEmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    by_cases hx : ξ ∈ E
    · simp [hx, Real.norm_eq_abs]
    · simp only [Set.indicator_of_notMem hx, mul_zero, norm_zero]
      positivity
  have hsum : ∀ ξ : V → ℝ, (∑ v ∈ K \ F, w v * ξ v) * E.indicator (fun _ => (1 : ℝ)) ξ
      = ∑ v ∈ K \ F, (w v * ξ v) * E.indicator (fun _ => (1 : ℝ)) ξ := by
    intro ξ
    rw [Finset.sum_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsum), integral_finsetSum _ hint]
  exact Finset.sum_eq_zero hterm

/-- **A block of sites contributes at most `E|ξ|` per unit weight.** -/
theorem integral_sum_block_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℝ => z) ν) {S T : Set V} (hd : Disjoint S T) (F : Finset V)
    (hFS : (F : Set V) ⊆ S) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    {A B : Set (V → ℝ)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAS : ∀ ξ η : V → ℝ, (∀ u ∈ S, ξ u = η u) → (ξ ∈ A ↔ η ∈ A))
    (hBT : ∀ ξ η : V → ℝ, (∀ u ∈ T, ξ u = η u) → (ξ ∈ B ↔ η ∈ B)) :
    ∫ ξ, (∑ v ∈ F, w v * ξ v) * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      ≤ (∫ z, |z| ∂ν) * (∑ v ∈ F, w v) * (RWRS.iidLaw V ν B).toReal := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  set μ : Measure (V → ℝ) := RWRS.iidLaw V ν with hμ
  set c : ℝ := (∫ z, |z| ∂ν) * (μ B).toReal with hc
  have hcnn : 0 ≤ c := by
    refine mul_nonneg (integral_nonneg fun z => abs_nonneg z) ENNReal.toReal_nonneg
  have hABmeas : Measurable ((A ∩ B).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (hA.inter hB)
  have hintF : ∀ v ∈ F,
      Integrable (fun ξ : V → ℝ =>
        (w v * ξ v) * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ) μ := by
    intro v _
    have hc0 : Integrable (fun ξ : V → ℝ => ξ v) μ := integrable_coord ν v hint
    refine Integrable.mono' (hc0.abs.const_mul |w v|)
      (((measurable_pi_apply v).const_mul (w v)).mul hABmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    by_cases hx : ξ ∈ A ∩ B
    · simp [hx, Real.norm_eq_abs]
    · simp only [Set.indicator_of_notMem hx, mul_zero, norm_zero]
      positivity
  have hsplit : ∀ ξ : V → ℝ,
      (∑ v ∈ F, w v * ξ v) * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ
        = ∑ v ∈ F, (w v * ξ v) * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ := fun ξ => by
    rw [Finset.sum_mul]
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_finsetSum _ hintF]
  have hterm : ∀ v ∈ F,
      ∫ ξ, (w v * ξ v) * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ ∂μ ≤ c * w v := by
    intro v hv
    have hvS : v ∈ S := hFS (by exact_mod_cast hv)
    have hb := abs_integral_coord_mul_indicator_le ν hint hd hvS hA hB hAS hBT
    have hcongr : ∀ ξ : V → ℝ, (w v * ξ v) * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ
        = w v * (ξ v * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ) := fun ξ => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hcongr), integral_const_mul]
    have hle : ∫ ξ, ξ v * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ ∂μ
        ≤ (∫ z, |z| ∂ν) * (μ B).toReal := le_trans (le_abs_self _) hb
    calc w v * ∫ ξ, ξ v * (A ∩ B).indicator (fun _ => (1 : ℝ)) ξ ∂μ
        ≤ w v * c := by
          exact mul_le_mul_of_nonneg_left hle (hw v)
      _ = c * w v := mul_comm _ _
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [← Finset.mul_sum]
  ring

/-! ### The trap event -/

/-- The event that the scenery is at most `-ε` at every site of `C`. -/
def trapEvent (C : Finset V) (ε : ℝ) : Set (V → ℝ) := {ξ : V → ℝ | ∀ v ∈ C, ξ v ≤ -ε}

theorem trapEvent_eq_pi (C : Finset V) (ε : ℝ) :
    trapEvent C ε = Set.pi (C : Set V) (fun _ => Set.Iic (-ε)) := by
  ext ξ
  simp [trapEvent, Set.mem_pi]

theorem measurableSet_trapEvent (C : Finset V) (ε : ℝ) :
    MeasurableSet (trapEvent (V := V) C ε) := by
  rw [trapEvent_eq_pi]
  exact MeasurableSet.pi (Set.to_countable _) fun i _ => measurableSet_Iic

theorem trapEvent_dependsOn (C : Finset V) (ε : ℝ) (ξ η : V → ℝ)
    (h : ∀ w ∈ (C : Set V), ξ w = η w) : ξ ∈ trapEvent C ε ↔ η ∈ trapEvent C ε := by
  constructor
  · intro hξ v hv
    rw [← h v (by exact_mod_cast hv)]
    exact hξ v hv
  · intro hη v hv
    rw [h v (by exact_mod_cast hv)]
    exact hη v hv

/-- **The trap event has the product probability.** -/
theorem measure_trapEvent (ν : Measure ℝ) [IsProbabilityMeasure ν] (C : Finset V) (ε : ℝ) :
    RWRS.iidLaw V ν (trapEvent C ε) = ν (Set.Iic (-ε)) ^ C.card := by
  rw [trapEvent_eq_pi]
  have hpi := MeasureTheory.Measure.infinitePi_pi (μ := fun _ : V => ν) (s := C)
    (t := fun _ : V => Set.Iic (-ε)) (fun i _ => measurableSet_Iic)
  rw [RWRS.iidLaw, hpi, Finset.prod_const]

end RWRS.Support
