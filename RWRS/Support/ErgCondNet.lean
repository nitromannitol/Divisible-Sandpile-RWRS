/-
The two conditional laws of `thm:stationary-phase`.

The proof conditions on a rerooting-invariant event `B` of the rooted graph and
on its complement (`rwrs.tex:345-347`).  Under each, the law of the rooted graph
is again a stationary probability law carried by connected rooted graphs, the
marked law is its i.i.d. marking by the SAME mark law, and stabilization has
probability `1` under the first and `0` under the second.
-/
import RWRS.Support.ErgPhase
import RWRS.Support.ErgMass
import Mathlib.Probability.ConditionalProbability

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The reciprocal of the degree of the root. -/
noncomputable def degWeight (N : RWRS.Net 0) : ℝ :=
  (((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ))⁻¹

/-- The reciprocal degree at a named vertex. -/
noncomputable def degWeightAt (N : RWRS.Net 0) (r : ℕ) : ℝ :=
  (((RWRS.netGraph N).degree r : ℝ))⁻¹

set_option maxHeartbeats 1000000 in
theorem measurable_degWeight : Measurable degWeight := by
  have hpair : Measurable fun q : RWRS.Net 0 × ℕ => degWeightAt q.1 q.2 := by
    refine measurable_from_prod_countable_left fun r => ?_
    simp only [degWeightAt]
    exact (measurable_degree r).inv
  have hsplit : degWeight
      = (fun q : RWRS.Net 0 × ℕ => degWeightAt q.1 q.2) ∘ fun N : RWRS.Net 0 => (N, RWRS.netRoot N) :=
    rfl
  rw [hsplit]
  exact hpair.comp (measurable_id.prodMk measurable_netRoot)

theorem degWeight_nonneg (N : RWRS.Net 0) : 0 ≤ degWeight N :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

theorem degWeight_le_one (N : RWRS.Net 0) : degWeight N ≤ 1 := by
  rcases Nat.eq_zero_or_pos ((RWRS.netGraph N).degree (RWRS.netRoot N)) with h | h
  · rw [degWeight, h]; simp
  · rw [degWeight, inv_le_one_iff₀]
    right
    exact_mod_cast h

theorem integrable_degWeight (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q] :
    Integrable degWeight Q :=
  (integrable_const (1 : ℝ)).mono' measurable_degWeight.aestronglyMeasurable
    (Filter.Eventually.of_forall fun N => by
      rw [Real.norm_eq_abs, abs_of_nonneg (degWeight_nonneg N)]
      exact degWeight_le_one N)

/-- The degree-weighted mass at the root is the mark at the root times a
function of the rooted graph. -/
theorem netWeightedMass_eq_mul (M : RWRS.Net 1) :
    RWRS.netWeightedMass M
      = RWRS.netConfig M (RWRS.netRoot M) * degWeight (RWRS.forgetMarks M) := by
  rw [RWRS.netWeightedMass, degWeight, div_eq_mul_inv]
  rfl

/-! ### Conditioning on an event of the rooted graph -/

/-- The law of the rooted graph conditioned on a rerooting-invariant event is
stationary. -/
theorem isStationaryNet_cond {Q : Measure (RWRS.Net 0)} (hstat : RWRS.IsStationaryNet Q)
    {B : Set (RWRS.Net 0)} (hBmeas : MeasurableSet B) (hBiso : RWRS.NetInvariantSet B)
    (hBre : RWRS.RerootInvariant B) : RWRS.IsStationaryNet (Q[|B]) :=
  isStationaryNet_smul (isStationaryNet_restrict hstat hBmeas hBiso hBre) _

/-- Conditioning keeps the rooted graph connected almost surely. -/
theorem ae_netGood_cond {Q : Measure (RWRS.Net 0)} (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N)
    (B : Set (RWRS.Net 0)) : ∀ᵐ N ∂(Q[|B]), RWRS.NetGood N :=
  cond_absolutelyContinuous hgood

/-- The marked law conditioned on an event of the rooted graph is the i.i.d.
marking, by the same mark law, of the conditioned law of the rooted graph. -/
theorem markIid_cond (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {B : Set (RWRS.Net 0)} (hB : MeasurableSet B) :
    RWRS.markIid (Q[|B]) ν = (RWRS.markIid Q ν)[|RWRS.forgetMarks ⁻¹' B] := by
  have hmass : RWRS.markIid Q ν (RWRS.forgetMarks ⁻¹' B) = Q B := by
    rw [← Measure.map_apply measurable_forgetMarks hB, map_forgetMarks_markIid Q ν]
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, markIid_smul, markIid_restrict Q ν hB,
    hmass]

/-- Under the conditional law on the event where the conditional probability of
`A` is one, `A` is almost sure. -/
theorem cond_eq_one_of_inter (P : Measure (RWRS.Net 1)) [IsProbabilityMeasure P]
    {A S : Set (RWRS.Net 1)} (hA : MeasurableSet A) (hS : P (A ∩ S) = P S) (h0 : P S ≠ 0) :
    P[A|S] = 1 := by
  rw [ProbabilityTheory.cond_apply' hA, Set.inter_comm S A, hS,
    ENNReal.inv_mul_cancel h0 (measure_ne_top P S)]

/-- Under the conditional law off that event, `A` is null. -/
theorem cond_eq_zero_of_inter (P : Measure (RWRS.Net 1)) [IsProbabilityMeasure P]
    {A S : Set (RWRS.Net 1)} (hA : MeasurableSet A) (hS : P (A ∩ S) = 0) :
    P[A|S] = 0 := by
  rw [ProbabilityTheory.cond_apply' hA, Set.inter_comm S A, hS, mul_zero]

end RWRS.Support
