/-
The block-wise bias bounds of Step 1 of
`prop:doubly-transient-really-general` (`rwrs.tex:918-921`): conditionally on
the walk, the potential at the stage centre splits over the trap blocks, and
each block contributes its share of the conditional bias.  The current block
contributes the full negative bias on the trap event; an earlier block
contributes at most its interaction with the centre, weighted by the
conditional probability of the stage event.

The pathwise current-block bound is `currentBlock_le` in `DTPotential.lean`;
this file carries the integrated earlier-block bound, where the stage event
`J = i` factors as the complement of the earlier trap event intersected with
the rest event, and the rest-event probability is controlled by the
stage-event probability through `measure_restEvent_le`.
-/
import RWRS.Support.DTStageEvents
import RWRS.Support.DTAdmissibleCap
import RWRS.Support.DTPotential
import LatticeProb.Network.KilledGreenEscape

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

omit [DecidableEq V] in
/-- **The earlier-block contribution to the conditional bias bound of Step 1**
(`rwrs.tex:920`): an earlier trap block `C j` (`j < i`) contributes at most
`E|ξ| · (∑_{v ∈ C j} g_K(v, y))` times the probability of the hit event. -/
theorem integral_earlierBlock_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℝ => z) ν)
    (K : Finset V) (C : ℕ → Finset V) (ε : ℝ) {i j : ℕ} (hji : j < i) (y : V)
    (hdisj : ∀ a ≤ i, ∀ b ≤ i, a ≠ b → Disjoint ((C a : Set V)) ((C b : Set V)))
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) {q : ℝ} (hq : 0 < q)
    (hcompl : ENNReal.ofReal q ≤ RWRS.iidLaw V ν ((trapEvent (C j) ε)ᶜ)) :
    ∫ ξ, (∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      ≤ (∫ z, |z| ∂ν)
          * (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y)
          * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q) := by
  have hgnn : ∀ v, 0 ≤ RWRS.killedGreenReal G (K : Set V) v y :=
    fun v => killedGreenReal_nonneg_of_escape K hescK v y
  have hrest := integral_sum_block_le ν hint
    (S := ((C j : Finset V) : Set V))
    (T := ((stageSitesExcept C i j : Finset V) : Set V))
    (disjoint_block_stageSitesExcept C (le_of_lt hji) (fun a b hab => by exact_mod_cast hdisj a b hab))
    (F := C j) (hFS := fun v hv => hv)
    (w := fun v => RWRS.killedGreenReal G (K : Set V) v y) hgnn
    (A := (trapEvent (C j) ε)ᶜ) (B := restEvent C ε i j)
    (MeasurableSet.compl (measurableSet_trapEvent _ _))
    (measurableSet_restEvent C ε i j)
    (fun ξ η h => Iff.not (trapEvent_dependsOn (C j) ε ξ η h))
    (fun ξ η h => restEvent_dependsOn C ε hji ξ η h)
  have hset : ((trapEvent (C j) ε)ᶜ ∩ restEvent C ε i j)
      = hitEvent C ε i := (hitEvent_eq_compl_inter_rest C ε hji).symm
  rw [hset] at hrest
  have hmeas := measure_restEvent_le ν C ε hji (fun a b hab => by exact_mod_cast hdisj a b hab) hq hcompl
  have hnn : 0 ≤ (∫ z, |z| ∂ν) * (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y) := by
    refine mul_nonneg (integral_nonneg fun z => abs_nonneg z) ?_
    exact Finset.sum_nonneg fun v _ => hgnn v
  have hmul : (∫ z, |z| ∂ν) * (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y)
      * ((RWRS.iidLaw V ν (restEvent C ε i j)).toReal)
      ≤ (∫ z, |z| ∂ν) * (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y)
          * (((RWRS.iidLaw V ν (hitEvent C ε i)).toReal) / q) := by
    refine mul_le_mul_of_nonneg_left hmeas hnn
  have hcomm : ∀ ξ : V → ℝ, (∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
      = (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y * ξ v) :=
    fun ξ => Finset.sum_congr rfl fun v _ => mul_comm _ _
  calc ∫ ξ, (∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      = ∫ ξ, (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y * ξ v)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        show (∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
            * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
          = (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y * ξ v)
            * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
        rw [hcomm ξ]
    _ ≤ (∫ z, |z| ∂ν) * (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y)
          * ((RWRS.iidLaw V ν (restEvent C ε i j)).toReal) := hrest
    _ ≤ (∫ z, |z| ∂ν) * (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y)
          * (((RWRS.iidLaw V ν (hitEvent C ε i)).toReal) / q) := hmul


omit [DecidableEq V] in
/-- **On the trap event, the current block contributes at most `-8m`.** -/
theorem currentBlock_le (K : Finset V) (C : ℕ → Finset V) (i : ℕ) (y : V) (m ε : ℝ)
    (hε : 0 < ε) (_hm : 0 ≤ m) (hdeg : ∀ w : V, 0 < G.degree w)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C i : Set V))
    (hCK : (C i : Set V) ⊆ (K : Set V))
    (hΘ : ENNReal.ofReal (8 * m / ε) ≤ thetaExit G (C i : Set V) y)
    {ξ : V → ℝ} (hξ : ξ ∈ hitEvent C ε i) :
    ∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y ≤ -(8 * m) := by
  have htrap : ∀ v ∈ C i, ξ v ≤ -ε := by
    intro v hv
    have h := hitEvent_subset_trapEvent C ε i hξ
    exact h v hv
  have h8 := sum_trap_le (C i) K hCK hescC hescK hdeg y ξ ε (8 * m / ε) hε.le htrap hΘ
  have hred : ε * (8 * m / ε) = 8 * m := by
    field_simp
  rwa [hred] at h8

omit [DecidableEq V] in
/-- **The current-block contribution to the conditional bias bound.** -/
theorem integral_currentBlock_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℝ => z) ν)
    (K : Finset V) (C : ℕ → Finset V) (i : ℕ) (y : V) (m ε : ℝ)
    (hε : 0 < ε) (hm : 0 ≤ m) (hdeg : ∀ w : V, 0 < G.degree w)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C i : Set V))
    (hCK : (C i : Set V) ⊆ (K : Set V))
    (hΘ : ENNReal.ofReal (8 * m / ε) ≤ thetaExit G (C i : Set V) y) :
    ∫ ξ, (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      ≤ -(8 * m) * (RWRS.iidLaw V ν (hitEvent C ε i)).toReal := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw V ν) := instIsProbabilityMeasureIid ν
  set μ := RWRS.iidLaw V ν with hμ
  have hmeas : MeasurableSet (hitEvent C ε i) := measurableSet_hitEvent C ε i
  have hint : Integrable (fun ξ : V → ℝ =>
      (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) μ := by
    have hpush : ∀ ξ : V → ℝ,
        (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
        = ∑ v ∈ C i, (ξ v * RWRS.killedGreenReal G (K : Set V) v y)
            * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ := by
      intro ξ
      rw [Finset.sum_mul]
    have hterm : ∀ v ∈ C i, Integrable (fun ξ : V → ℝ =>
        (ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) μ := by
      intro v _
      have hc : Integrable (fun ξ : V → ℝ => ξ v) μ := integrable_coord ν v hint
      have hmeas2 : Measurable fun ξ : V → ℝ =>
          ξ v * RWRS.killedGreenReal G (K : Set V) v y
            * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ :=
        ((measurable_pi_apply v).mul measurable_const).mul
          (measurable_const.indicator hmeas)
      refine Integrable.mono' (hc.abs.const_mul
          |RWRS.killedGreenReal G (K : Set V) v y|) hmeas2.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => ?_)
      by_cases hx : ξ ∈ hitEvent C ε i
      · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul, mul_one]
        exact (mul_comm _ _).le
      · simp only [Set.indicator_of_notMem hx, mul_zero, norm_zero]
        exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hfun : (fun ξ : V → ℝ =>
        ∑ v ∈ C i, (ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ)
      = (fun ξ : V → ℝ =>
        (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) :=
      funext fun ξ => (hpush ξ).symm
    rw [← hfun, ← Finset.sum_fn]
    exact integrable_finsetSum' (C i) (fun v hv => hterm v hv)
  have hle : ∀ ξ : V → ℝ,
      (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
      ≤ (-(8 * m)) * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ := by
    intro ξ
    by_cases hx : ξ ∈ hitEvent C ε i
    · simp only [Set.indicator_of_mem hx]
      have h8 := currentBlock_le K C i y m ε hε hm hdeg hescK hescC hCK hΘ hx
      nlinarith [h8]
    · have h0 : (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ = 0 :=
        Set.indicator_of_notMem hx _
      rw [h0, mul_zero, mul_zero]
  have hintg : Integrable (fun ξ : V → ℝ =>
      (-(8 * m)) * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) μ := by
    refine Integrable.mono' (integrable_const |-(8 * m)|)
      ((measurable_const).mul (measurable_const.indicator hmeas)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    by_cases hx : ξ ∈ hitEvent C ε i
    · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs, mul_one]
      exact le_refl _
    · simp only [Set.indicator_of_notMem hx, mul_zero, norm_zero]
      exact abs_nonneg _
  have hmono := integral_mono hint hintg hle
  have hintg2 : ∫ ξ : V → ℝ,
      (-(8 * m)) * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂μ
      = (-(8 * m)) * (μ (hitEvent C ε i)).toReal := by
    rw [integral_const_mul, integral_indicator_const _ hmeas]
    simp [Measure.real]
  rw [hintg2] at hmono
  exact hmono



/-- **The summed earlier-block contribution to the conditional bias bound.**
Summing `integral_earlierBlock_le` over `j < i` and capping the total weight
by admissibility (`sum_earlierBlocks_le_one`), the earlier blocks contribute at
most `B₀` times the hit probability, where `B₀ = E|ξ| / q`. -/
theorem integral_sum_earlierBlocks_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℝ => z) ν)
    (K F : Finset V) (C : ℕ → Finset V) (ε : ℝ) (i : ℕ) (y : V) (r : ℕ)
    (hdisj : ∀ a ≤ i, ∀ b ≤ i, a ≠ b → Disjoint ((C a : Set V)) ((C b : Set V)))
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    {q : ℝ} (hq : 0 < q)
    (hcompl : ∀ j < i, ENNReal.ofReal q ≤ RWRS.iidLaw V ν ((trapEvent (C j) ε)ᶜ))
    (hCF : ∀ j < i, C j ⊆ F)
    (hadm : RWRS.Support.Admissible G r F y)
    (hgreen : ∀ v ∈ F, RWRS.green G v y ≠ ⊤) :
    ∑ j ∈ Finset.range i, ∫ ξ, (∑ v ∈ C j,
        ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      ≤ (∫ z, |z| ∂ν) * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q) := by
  have hstep : ∀ j ∈ Finset.range i,
      ∫ ξ, (∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      ≤ (∫ z, |z| ∂ν) * (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y)
          * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q) :=
    fun j hj => integral_earlierBlock_le ν hint K C ε (Finset.mem_range.1 hj) y hdisj hescK hq (hcompl j (Finset.mem_range.1 hj))
  have hsum := Finset.sum_le_sum hstep
  have hcap := sum_earlierBlocks_le_one G C i y F K r hescK hCF
    (fun a ha b hb hab => by
      have := hdisj a (Nat.le_of_lt ha) b (Nat.le_of_lt hb) hab
      exact_mod_cast this)
    hadm hgreen
  have hsplit : ∑ j ∈ Finset.range i, (∫ z, |z| ∂ν) * (∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y) * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q)
      = (∫ z, |z| ∂ν) * (∑ j ∈ Finset.range i, ∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y) * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [hsplit] at hsum
  have hP : 0 ≤ (RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q :=
    div_nonneg ENNReal.toReal_nonneg (le_of_lt hq)
  have hA : 0 ≤ ∫ z, |z| ∂ν := integral_nonneg fun z => abs_nonneg z
  calc ∑ j ∈ Finset.range i, ∫ ξ, (∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y) * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      ≤ (∫ z, |z| ∂ν) * (∑ j ∈ Finset.range i, ∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y) * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q) := hsum
    _ ≤ (∫ z, |z| ∂ν) * 1 * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q) := by
        refine mul_le_mul_of_nonneg_right ?_ hP
        exact mul_le_mul_of_nonneg_left hcap hA
    _ = (∫ z, |z| ∂ν) * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q) := by ring
omit [DecidableEq V] in
open scoped Classical in
/-- **The conditional bias estimate of Step 1.**  On the stage-`i` hit event,
the conditional expectation of the trap potential at the stage centre is at
most `-8m` from the current block plus the `B₀` bias from the earlier blocks. -/
theorem integral_conditionalBias_le (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h0 : RWRS.extMean ν = 0) (hint : Integrable (fun z : ℝ => z) ν)
    (K : Finset V) (C : ℕ → Finset V) (ε : ℝ) (i : ℕ) (y : V) (m : ℝ) (r : ℕ)
    (hdisj : ∀ a ≤ i, ∀ b ≤ i, a ≠ b → Disjoint ((C a : Set V)) ((C b : Set V)))
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C i : Set V))
    (hCK : ∀ j ≤ i, (C j : Set V) ⊆ (K : Set V))
    (hΘ : ENNReal.ofReal (8 * m / ε) ≤ thetaExit G (C i : Set V) y)
    (hdeg : ∀ w : V, 0 < G.degree w)
    (hε : 0 < ε) (hm : 0 ≤ m) {q : ℝ} (hq : 0 < q)
    (hcompl : ∀ j < i, ENNReal.ofReal q
      ≤ RWRS.iidLaw V ν ((trapEvent (C j) ε)ᶜ))
    (hgreen : ∀ v ∈ (stageSitesBelow C i : Finset V),
      (RWRS.green G v y) ≠ ⊤)
    (hadm : RWRS.Support.Admissible G r (stageSitesBelow C i) y)
    (hCF : ∀ j < i, C j ⊆ stageSitesBelow C i) :
    ∫ ξ, (RWRS.Support.trapPotential G K ξ y) *
        (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ ∂(RWRS.iidLaw V ν)
      ≤ (-8 * m) * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal)
        + (∫ z, |z| ∂ν) * ((RWRS.iidLaw V ν (hitEvent C ε i)).toReal / q) := by
  have hsplit : ∀ ξ : V → ℝ, RWRS.Support.trapPotential G K ξ y
      = (∑ v ∈ K ∩ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        + (∑ j ∈ Finset.range i, ∑ v ∈ K ∩ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        + (∑ v ∈ K \ (Finset.range (i + 1)).biUnion (fun j => K ∩ C j),
            ξ v * RWRS.killedGreenReal G (K : Set V) v y) :=
    fun ξ => trapPotential_split_range (G := G) K C i hdisj ξ y
  have hKC : ∀ j ≤ i, K ∩ C j = C j := by
    intro j hj
    refine Finset.ext fun v => ?_
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨_, hv⟩; exact hv
    · intro hv
      exact ⟨by exact_mod_cast hCK j hj hv, hv⟩
  have hrest : K \ (Finset.range (i + 1)).biUnion (fun j => K ∩ C j)
      = K \ (Finset.range (i + 1)).biUnion C := by
    refine Finset.ext fun v => ?_
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, Finset.mem_inter]
    constructor
    · rintro ⟨hvK, hn⟩
      exact ⟨hvK, fun ⟨a, ha, hCa⟩ => hn ⟨a, ha, hvK, hCa⟩⟩
    · rintro ⟨hvK, hn⟩
      exact ⟨hvK, fun ⟨a, ha, hvK', hCa⟩ => hn ⟨a, ha, hCa⟩⟩
  have hsplit2 : ∀ ξ : V → ℝ, RWRS.Support.trapPotential G K ξ y
      = (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        + (∑ j ∈ Finset.range i, ∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        + (∑ v ∈ K \ (Finset.range (i + 1)).biUnion C,
            ξ v * RWRS.killedGreenReal G (K : Set V) v y) := by
    intro ξ
    rw [hsplit ξ, hKC i (le_refl i), hrest]
    have hmid : (∑ j ∈ Finset.range i, ∑ v ∈ K ∩ C j,
        ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        = ∑ j ∈ Finset.range i, ∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y :=
      Finset.sum_congr rfl fun j hj => by rw [hKC j (Nat.le_of_lt (Finset.mem_range.1 hj))]
    rw [hmid]
  have hdist : ∀ ξ : V → ℝ,
      (RWRS.Support.trapPotential G K ξ y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
      = (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
        + (∑ j ∈ Finset.range i, ∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
        + (∑ v ∈ K \ (Finset.range (i + 1)).biUnion C,
              ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ := by
    intro ξ
    rw [hsplit2 ξ, add_mul, add_mul]
  simp only [hdist]
  have hEmeas : Measurable (fun ξ : V → ℝ => (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) :=
    measurable_const.indicator (measurableSet_hitEvent C ε i)
  have hint1 : Integrable (fun ξ : V → ℝ =>
      (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) (RWRS.iidLaw V ν) := by
    have hs : Integrable (fun ξ : V → ℝ =>
        ∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y) (RWRS.iidLaw V ν) :=
      integrable_finsetSum _ fun v _ =>
        (integrable_coord ν v hint).mul_const _
    exact (hs.indicator (measurableSet_hitEvent C ε i)).congr
      (Filter.Eventually.of_forall fun ξ => by
        by_cases hx : ξ ∈ hitEvent C ε i <;> simp [hx])
  have hint2 : Integrable (fun ξ : V → ℝ =>
      (∑ j ∈ Finset.range i, ∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) (RWRS.iidLaw V ν) := by
    have hs : Integrable (fun ξ : V → ℝ =>
        ∑ j ∈ Finset.range i, ∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        (RWRS.iidLaw V ν) :=
      integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun v _ =>
          (integrable_coord ν v hint).mul_const _
    exact (hs.indicator (measurableSet_hitEvent C ε i)).congr
      (Filter.Eventually.of_forall fun ξ => by
        by_cases hx : ξ ∈ hitEvent C ε i <;> simp [hx])
  have hint3 : Integrable (fun ξ : V → ℝ =>
      (∑ v ∈ K \ (Finset.range (i + 1)).biUnion C,
          ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) (RWRS.iidLaw V ν) := by
    have hs : Integrable (fun ξ : V → ℝ =>
        ∑ v ∈ K \ (Finset.range (i + 1)).biUnion C,
            ξ v * RWRS.killedGreenReal G (K : Set V) v y) (RWRS.iidLaw V ν) :=
      integrable_finsetSum _ fun v _ =>
        (integrable_coord ν v hint).mul_const _
    exact (hs.indicator (measurableSet_hitEvent C ε i)).congr
      (Filter.Eventually.of_forall fun ξ => by
        by_cases hx : ξ ∈ hitEvent C ε i <;> simp [hx])
  have hint12 : Integrable (fun ξ : V → ℝ =>
      (∑ v ∈ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y) *
          (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
        + (∑ j ∈ Finset.range i, ∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) (RWRS.iidLaw V ν) :=
    hint1.add hint2
  rw [integral_add hint12 hint3, integral_add hint1 hint2]
  have hint2' : ∀ j ∈ Finset.range i, Integrable (fun ξ : V → ℝ =>
      (∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ) (RWRS.iidLaw V ν) := by
    intro j _
    have hs : Integrable (fun ξ : V → ℝ =>
        ∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y) (RWRS.iidLaw V ν) :=
      integrable_finsetSum _ fun v _ => (integrable_coord ν v hint).mul_const _
    exact (hs.indicator (measurableSet_hitEvent C ε i)).congr
      (Filter.Eventually.of_forall fun ξ => by
        by_cases hx : ξ ∈ hitEvent C ε i <;> simp [hx])
  have hpush : ∀ ξ : V → ℝ, (∑ j ∈ Finset.range i, ∑ v ∈ C j,
      ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
      = ∑ j ∈ Finset.range i, (∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
          * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ :=
    fun ξ => Finset.sum_mul
      (Finset.range i)
      (fun j => ∑ v ∈ C j, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
      ((hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpush), integral_finsetSum _ hint2']
  have hb1 := integral_currentBlock_le ν hint K C i y m ε hε hm hdeg hescK hescC
    (hCK i (le_refl i)) hΘ
  have hb2 := integral_sum_earlierBlocks_le ν hint K (stageSitesBelow C i) C ε i y r
    hdisj hescK hq hcompl hCF hadm hgreen
  have hb3 := integral_sum_outside_eq_zero ν h0 K (stageSites C i)
    (fun v => RWRS.killedGreenReal G (K : Set V) v y)
    (measurableSet_hitEvent C ε i)
    (fun ξ η h => hitEvent_dependsOn C ε i ξ η h)
  have hrest2 : ∀ ξ : V → ℝ, (∑ v ∈ K \ (Finset.range (i + 1)).biUnion C,
      ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ
      = (∑ v ∈ K \ (stageSites C i), RWRS.killedGreenReal G (K : Set V) v y * ξ v)
        * (hitEvent C ε i).indicator (fun _ => (1 : ℝ)) ξ := by
    intro ξ
    have hset : (Finset.range (i + 1)).biUnion C = stageSites C i := by
      simp [stageSites]
    rw [hset]
    refine congrArg (fun t => t * _) ?_
    refine Finset.sum_congr rfl fun v _ => ?_
    exact mul_comm _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hrest2), hb3, add_zero]
  linarith [hb1, hb2]


end RWRS.Support
