/-
The annealed assembly of Step 1.

Averaging the per-trajectory conditional estimate over the walk: the good
trajectories, of probability at least three quarters, each carry the gain
`-8m` on at least three quarters of the scenery, the trajectories that leave
`K` before the horizon carry no loss at all, and the remaining ones are
controlled by the size of the killed potential on `K` times their probability.
-/
import RWRS.Support.DTPerTraj
import RWRS.Support.DTWalkProb
import RWRS.Support.NestedLower
import RWRS.Support.VoltageIdentity
import RWRS.Support.Representation
import RWRS.Support.DTVariance
import RWRS.Support.DTCappedFubini
import RWRS.Support.DTAnnealed

open scoped Classical ENNReal
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [Infinite V]

omit [Infinite V] in
/-- **The walk average of a functional settled by the first `N` positions is
its integral against the walk law.** -/
theorem walkExp_eq_walkLaw_integral (hdeg : ∀ v : V, 0 < G.degree v) (N : ℕ) (o : V)
    (F : (ℕ → V) → ℝ) (c : ℝ) (hb : ∀ X, ‖F X‖ ≤ c)
    (hdep : LatticeProb.Graph.DependsUpTo N F) :
    RWRS.walkExp G N o F = ∫ X, F X ∂(LatticeProb.Graph.walkLaw G o) := by
  rw [walkExp_eq_lib N o F]
  exact LatticeProb.Graph.walkExp_eq_integral hdeg N o F
    (LatticeProb.Graph.measurable_of_dependsUpTo hdep) c hb hdep

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- **Every bounded rule is below the finite-horizon value.** -/
theorem walkExp_payoff_le_value (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (o : V)
    (τ : (ℕ → V) → ℕ) (hτ : RWRS.IsStopping τ) (hle : ∀ X, τ X ≤ n) :
    RWRS.walkExp G n o (fun X => RWRS.payoff G ξ (τ X) X) ≤ RWRS.value G ξ n o := by
  have hmem : RWRS.walkExp G n o (fun X => RWRS.payoff G ξ (τ X) X)
      ∈ RWRS.stopValues G ξ n o := ⟨τ, hτ, hle, rfl⟩
  have h := (odometer_isLUB hG (fun u => ξ u + 1) n o).1
  rw [excess_add_one] at h
  rw [value_eq_odometer hG ξ n o]
  exact h _ hmem

/-- **The annealed conditional estimate.** -/
theorem walkExp_conditional_le (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h0 : RWRS.extMean ν = 0)
    (hint : Integrable (fun z : ℝ => z) ν)
    (r M ℓ : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ) (o : V)
    (m : ℝ)
    (hCball : ∀ y : V, ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r)
    (hCself : ∀ y : V, y ∈ C y) (hcard : ∀ y : V, (C y).card ≤ M)
    (hΘ : ∀ y : V, ENNReal.ofReal (8 * m / ε) ≤ RWRS.thetaExit G (C y : Set V) y)
    (hε : 0 < ε) (hm : 0 ≤ m) {q : ℝ} (hq : 0 < q)
    (hcompl : ∀ y : V, ENNReal.ofReal q ≤ RWRS.iidLaw V ν ((trapEvent (C y) ε)ᶜ))
    (hℓ : (1 - ν (Set.Iic (-ε)) ^ M) ^ (ℓ + 1) ≤ ENNReal.ofReal (1 / 4))
    (hgain : (∫ z, |z| ∂ν) / q ≤ 8 * m)
    {δ : ℝ}
    (hW : (3 : ℝ) / 4 ≤ ((LatticeProb.Graph.walkLaw G o)
      (walkGoodEvent G r C ℓ K N)).toReal)
    (hEc : ((LatticeProb.Graph.walkLaw G o) (exitEvent K N)ᶜ).toReal ≤ δ) :
    RWRS.walkExp G N o (fun X => ∫ ξ : V → ℝ,
        trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X)) ∂(RWRS.iidLaw V ν))
      ≤ (3 / 4) * ((3 / 4) * ((∫ z, |z| ∂ν) / q - 8 * m))
        + ((∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v)
            * ((K.card : ℝ) * ∫ z, |z| ∂ν)) * δ := by
  set A : ℝ := (3 / 4) * ((∫ z, |z| ∂ν) / q - 8 * m) with hAdef
  set B : ℝ := (∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v)
    * ((K.card : ℝ) * ∫ z, |z| ∂ν) with hBdef
  have hescK : ∀ x : V, ∃ (qq : V) (_ : G.Walk x qq), qq ∉ (K : Set V) := esc_of_finset hG K
  have hescC : ∀ y x : V, ∃ (qq : V) (_ : G.Walk x qq), qq ∉ (C y : Set V) :=
    fun y => esc_of_finset hG (C y)
  have hA0 : A ≤ 0 := by
    have : (∫ z, |z| ∂ν) / q - 8 * m ≤ 0 := by linarith
    nlinarith
  have hB0 : 0 ≤ B := by
    refine mul_nonneg (Finset.sum_nonneg fun v _ => ENNReal.toReal_nonneg) ?_
    exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun z => abs_nonneg _)
  -- the pointwise bound
  have hpt : ∀ X : ℕ → V,
      (∫ ξ : V → ℝ, trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
          ∂(RWRS.iidLaw V ν))
        ≤ (walkGoodEvent G r C ℓ K N).indicator (fun _ => A) X
          + ((exitEvent K N)ᶜ).indicator (fun _ => B) X := by
    intro X
    by_cases hX : X ∈ walkGoodEvent G r C ℓ K N
    · have hE : X ∈ exitEvent K N := walkGoodEvent_subset_exitEvent r C ℓ K N hX
      rw [Set.indicator_of_mem hX, Set.indicator_of_notMem (by simpa using hE), add_zero]
      have hcnt : stageCnt G r C ℓ K N X = ℓ + 1 :=
        stageCnt_eq_of_walkGood r C ℓ K hN X hX
      have hdisj := disjoint_walkBlocks r C K hCball hCself X ℓ (by omega : ℓ < stageCnt G r C ℓ K N X)
      have hfail : RWRS.iidLaw V ν {ξ : V → ℝ | ∀ j < ℓ + 1,
          ξ ∉ trapEvent (C (X ((uncTime G r C X j).toNat))) ε} ≤ ENNReal.ofReal (1 / 4) := by
        refine le_trans (measure_noHit_le ν (fun j => C (X ((uncTime G r C X j).toNat))) ε
          (ℓ + 1) M (fun i _ => hcard _) ?_) hℓ
        intro i hi j hj hij
        exact hdisj i (by omega) j (by omega) hij
      exact integral_trapPotential_cappedRule_good_le ν h0 hint r C ℓ K hN ε X hX m
        hCball hCself hescK hescC hΘ hdeg hε hm hq hcompl hfail hgain
    · by_cases hE : X ∈ exitEvent K N
      · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (by simpa using hE)]
        simp only [add_zero]
        exact integral_trapPotential_cappedRule_nonpos ν h0 hint r C ℓ K hN ε X m
          hCball hCself hescK hescC hΘ hdeg hε hm hq hcompl hE hgain
      · rw [Set.indicator_of_notMem hX, Set.indicator_of_mem (by simpa using hE)]
        simp only [zero_add]
        exact integral_trapPotential_cappedRule_le_const ν hint r C ℓ K N ε X hescK
          (fun v _ => hdeg v)
  -- average over the walk
  have hmono := walkExp_mono (G := G) (n := N) (x := o) hpt
  refine le_trans hmono ?_
  have hdepW := dependsUpTo_walkGoodEvent (G := G) r C ℓ K hN A
  have hdepE := dependsUpTo_exitEvent (V := V) K N B
  have hdep : LatticeProb.Graph.DependsUpTo N
      (fun X : ℕ → V => (walkGoodEvent G r C ℓ K N).indicator (fun _ => A) X
        + ((exitEvent K N)ᶜ).indicator (fun _ => B) X) := by
    intro X Y hXY
    show (walkGoodEvent G r C ℓ K N).indicator (fun _ => A) X
        + ((exitEvent K N)ᶜ).indicator (fun _ => B) X
      = (walkGoodEvent G r C ℓ K N).indicator (fun _ => A) Y
        + ((exitEvent K N)ᶜ).indicator (fun _ => B) Y
    have e1 : (walkGoodEvent G r C ℓ K N).indicator (fun _ => A) X
        = (walkGoodEvent G r C ℓ K N).indicator (fun _ => A) Y := hdepW X Y hXY
    have e2 : ((exitEvent K N)ᶜ).indicator (fun _ => B) X
        = ((exitEvent K N)ᶜ).indicator (fun _ => B) Y := hdepE X Y hXY
    rw [e1, e2]
  have hbd : ∀ X : ℕ → V, ‖(walkGoodEvent G r C ℓ K N).indicator (fun _ => A) X
      + ((exitEvent K N)ᶜ).indicator (fun _ => B) X‖ ≤ |A| + |B| := by
    intro X
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · by_cases h : X ∈ walkGoodEvent G r C ℓ K N
      · rw [Set.indicator_of_mem h]; exact le_of_eq rfl
      · rw [Set.indicator_of_notMem h]; simp
    · by_cases h : X ∈ (exitEvent K N)ᶜ
      · rw [Set.indicator_of_mem h]; exact le_of_eq rfl
      · rw [Set.indicator_of_notMem h]; simp
  rw [walkExp_eq_walkLaw_integral hdeg N o _ (|A| + |B|) hbd hdep]
  have hmeasW : MeasurableSet (walkGoodEvent G r C ℓ K N) := by
    have hfm := LatticeProb.Graph.measurable_of_dependsUpTo
      (dependsUpTo_walkGoodEvent (G := G) r C ℓ K hN (1 : ℝ))
    have hset : walkGoodEvent G r C ℓ K N
        = (fun X : ℕ → V => (walkGoodEvent G r C ℓ K N).indicator (fun _ => (1 : ℝ)) X)
          ⁻¹' {(1 : ℝ)} := by
      ext X
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hX
        rw [Set.indicator_of_mem hX]
      · intro hX
        by_contra hnot
        rw [Set.indicator_of_notMem hnot] at hX
        exact absurd hX (by norm_num)
    rw [hset]
    exact hfm (measurableSet_singleton (1 : ℝ))
  have hmeasE : MeasurableSet ((exitEvent K N)ᶜ) := (measurableSet_exitEvent K N).compl
  rw [integral_add ((integrable_const A).indicator hmeasW)
      ((integrable_const B).indicator hmeasE),
    MeasureTheory.integral_indicator_const A hmeasW,
    MeasureTheory.integral_indicator_const B hmeasE]
  have hWfin : ((LatticeProb.Graph.walkLaw G o) (walkGoodEvent G r C ℓ K N)).toReal * A
      ≤ (3 / 4) * A := by
    have := mul_le_mul_of_nonpos_right hW hA0
    simpa using this
  have hEfin : ((LatticeProb.Graph.walkLaw G o) (exitEvent K N)ᶜ).toReal * B ≤ δ * B :=
    mul_le_mul_of_nonneg_right hEc hB0
  simp only [smul_eq_mul, MeasureTheory.measureReal_def]
  nlinarith [hWfin, hEfin]

/-- **The mean value at the horizon is at least the annealed gain.** -/
theorem integral_value_ge (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (h0 : RWRS.extMean ν = 0)
    (hint : Integrable (fun z : ℝ => z) ν) (hsq : RWRS.evar ν < ⊤)
    (r M ℓ : ℕ) (C : V → Finset V) (K : Finset V) {N : ℕ} (hN : 0 < N) (ε : ℝ) (o : V)
    (m : ℝ)
    (hCball : ∀ y : V, ((C y : Finset V) : Set V) ⊆ RWRS.closedBall G y r)
    (hCself : ∀ y : V, y ∈ C y) (hcard : ∀ y : V, (C y).card ≤ M)
    (hΘ : ∀ y : V, ENNReal.ofReal (8 * m / ε) ≤ RWRS.thetaExit G (C y : Set V) y)
    (hε : 0 < ε) (hm : 0 ≤ m) {q : ℝ} (hq : 0 < q)
    (hcompl : ∀ y : V, ENNReal.ofReal q ≤ RWRS.iidLaw V ν ((trapEvent (C y) ε)ᶜ))
    (hℓ : (1 - ν (Set.Iic (-ε)) ^ M) ^ (ℓ + 1) ≤ ENNReal.ofReal (1 / 4))
    (hgain : (∫ z, |z| ∂ν) / q ≤ 8 * m)
    {δ : ℝ}
    (hW : (3 : ℝ) / 4 ≤ ((LatticeProb.Graph.walkLaw G o)
      (walkGoodEvent G r C ℓ K N)).toReal)
    (hEc : ((LatticeProb.Graph.walkLaw G o) (exitEvent K N)ᶜ).toReal ≤ δ) :
    (9 / 16) * (8 * m - (∫ z, |z| ∂ν) / q)
        - ((∑ v ∈ K, RWRS.killedGreenReal G (K : Set V) v v)
            * ((K.card : ℝ) * ∫ z, |z| ∂ν)) * δ
      ≤ ∫ ξ : V → ℝ, RWRS.value G ξ N o ∂(RWRS.iidLaw V ν) := by
  have habs : Integrable (fun z : ℝ => |z|) ν := hint.abs
  have hescK : ∀ x : V, ∃ (qq : V) (_ : G.Walk x qq), qq ∉ (K : Set V) := esc_of_finset hG K
  have hdegK : ∀ v ∈ K, 0 < G.degree v := fun v _ => hdeg v
  -- the dominating function
  have hdom : Integrable (fun ξ : V → ℝ => ((N : ℝ) + 1) * ∑ v ∈ K, |ξ v|)
      (RWRS.iidLaw V ν) :=
    (integrable_finsetSum _ fun v _ => integrable_coord ν v habs).const_mul _
  -- the payoff is integrable in the scenery, for each trajectory
  have hintP : ∀ X : ℕ → V, Integrable (fun ξ : V → ℝ =>
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X) (RWRS.iidLaw V ν) := by
    intro X
    refine Integrable.mono' hdom
      (measurable_payoff_trapRuleCapped r C ℓ K N ε X).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs]
    refine le_trans (abs_payoff_trapRuleCapped_le r C ℓ K N ε hdegK ξ X) ?_
    have hnn : (0 : ℝ) ≤ ∑ v ∈ K, |ξ v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    nlinarith
  have hintQ : ∀ X : ℕ → V, Integrable (fun ξ : V → ℝ =>
      trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))) (RWRS.iidLaw V ν) :=
    fun X => integrable_trapPotential_cappedRule ν hint r C ℓ K N ε X
  -- the annealed payoff identity
  have hzero := integral_payoffCapped_add_trapPotential_eq_zero hG r C ℓ K hN ε o ν hescK h0
  rw [integral_rulePayoffCapped_add_trapPotential hG r C ℓ K N ε o ν hdegK hescK habs] at hzero
  have hsplit : ∀ X : ℕ → V, (∫ ξ : V → ℝ,
      (RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
        + trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))) ∂(RWRS.iidLaw V ν))
      - (∫ ξ : V → ℝ, trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))
          ∂(RWRS.iidLaw V ν))
      = ∫ ξ : V → ℝ, RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
          ∂(RWRS.iidLaw V ν) := by
    intro X
    rw [integral_add (hintP X) (hintQ X)]
    ring
  have hPQ : RWRS.walkExp G N o (fun X => ∫ ξ : V → ℝ,
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X ∂(RWRS.iidLaw V ν))
      = - RWRS.walkExp G N o (fun X => ∫ ξ : V → ℝ,
        trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X)) ∂(RWRS.iidLaw V ν)) := by
    have hcongr := walkExp_congr (G := G) (n := N) (x := o) (fun X _ => (hsplit X).symm)
    rw [hcongr, walkExp_sub, hzero, zero_sub]
  -- the scenery average of the payoff
  have hfub : ∫ ξ : V → ℝ, RWRS.walkExp G N o (fun X =>
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X) ∂(RWRS.iidLaw V ν)
      = RWRS.walkExp G N o (fun X => ∫ ξ : V → ℝ,
        RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X ∂(RWRS.iidLaw V ν)) := by
    refine integral_walkExp hG hdom N o
      (fun ξ X => RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X)
      (fun X => measurable_payoff_trapRuleCapped r C ℓ K N ε X) (fun ξ X => ?_)
    refine le_trans (abs_payoff_trapRuleCapped_le r C ℓ K N ε hdegK ξ X) ?_
    have hnn : (0 : ℝ) ≤ ∑ v ∈ K, |ξ v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    nlinarith
  -- the payoff is below the value
  have hle : ∫ ξ : V → ℝ, RWRS.walkExp G N o (fun X =>
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X) ∂(RWRS.iidLaw V ν)
      ≤ ∫ ξ : V → ℝ, RWRS.value G ξ N o ∂(RWRS.iidLaw V ν) := by
    refine integral_mono ?_ (integrable_value hG (by infer_instance) h0 hsq N o) ?_
    · refine Integrable.mono' hdom
        (measurable_walkExp N o (fun ξ X =>
          RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X)
          (fun X => measurable_payoff_trapRuleCapped r C ℓ K N ε X)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs]
      refine abs_walkExp_le hG N o _ fun X => ?_
      refine le_trans (abs_payoff_trapRuleCapped_le r C ℓ K N ε hdegK ξ X) ?_
      have hnn : (0 : ℝ) ≤ ∑ v ∈ K, |ξ v| := Finset.sum_nonneg fun v _ => abs_nonneg _
      nlinarith
    · intro ξ
      exact walkExp_payoff_le_value hG ξ N o _
        (isStopping_trapRuleCapped r C ℓ K hN ε ξ) (trapRuleCapped_le r C ℓ K N ε ξ)
  have hQ := walkExp_conditional_le hG hdeg ν h0 hint r M ℓ C K hN ε o m hCball hCself hcard
    hΘ hε hm hq hcompl hℓ hgain hW hEc
  rw [hfub, hPQ] at hle
  linarith

end RWRS.Support
