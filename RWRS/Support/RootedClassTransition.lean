import RWRS.Support.RootedClassSaturation

/-!
# Positive class transitions

Every neighbor of a connected network has positive probability under the
class rerooting kernel.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The class transition probability can be evaluated on any connected representative. -/
theorem classRerootKernel_apply_goodNet (N : GoodNet) {D : Set RootedBallClass}
    (hD : MeasurableSet D) :
    classRerootKernel (goodNetClass N) D =
      rerootAvg (goodNetExtend ((D.indicator (1 : RootedBallClass → ℝ≥0∞)) ∘ goodNetClass)) N.1 := by
  let f := D.indicator (1 : RootedBallClass → ℝ≥0∞)
  change classRerootMeasure (goodNetClass N) D = _
  rw [classRerootMeasure_apply _ hD]
  apply netInvariant_rerootAvg (netInvariant_goodNetExtend_class f)
  apply (goodNetClass_eq_iff_netIso _ _).1
  exact goodNetClass_representative _

/-- Any neighbor in a measurable class event has positive transition probability. -/
theorem classRerootKernel_apply_pos_of_neighbor (N : GoodNet) {D : Set RootedBallClass}
    (hD : MeasurableSet D) {y : ℕ} (hy : (netGraph N.1).Adj (netRoot N.1) y)
    (hmem : goodNetClass (goodNetReroot N y) ∈ D) :
    0 < classRerootKernel (goodNetClass N) D := by
  classical
  rw [classRerootKernel_apply_goodNet N hD]
  have hy' : y ∈ (netGraph N.1).neighborFinset (netRoot N.1) := by simpa using hy
  have hvalue : goodNetExtend ((D.indicator (1 : RootedBallClass → ℝ≥0∞)) ∘ goodNetClass)
      (netReroot N.1 y) = 1 := by
    rw [goodNetExtend_of_good _ _ (netGood_netReroot N.2 y)]
    exact Set.indicator_of_mem hmem _
  have hsum : 0 < ∑ z ∈ (netGraph N.1).neighborFinset (netRoot N.1),
      goodNetExtend ((D.indicator (1 : RootedBallClass → ℝ≥0∞)) ∘ goodNetClass)
        (netReroot N.1 z) := by
    have hle := Finset.single_le_sum
      (f := fun z => goodNetExtend ((D.indicator (1 : RootedBallClass → ℝ≥0∞)) ∘
        goodNetClass) (netReroot N.1 z)) (fun _ _ => bot_le) hy'
    rw [hvalue] at hle
    exact lt_of_lt_of_le zero_lt_one hle
  change 0 < (∑ z ∈ (netGraph N.1).neighborFinset (netRoot N.1),
      goodNetExtend ((D.indicator (1 : RootedBallClass → ℝ≥0∞)) ∘ goodNetClass)
        (netReroot N.1 z)) / ((netGraph N.1).degree (netRoot N.1) : ℝ≥0∞)
  exact ENNReal.div_pos hsum.ne' ENNReal.coe_ne_top

end RWRS.Support
