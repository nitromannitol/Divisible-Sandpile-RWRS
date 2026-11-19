import RWRS.Support.RootedClassLaw
import Mathlib.Probability.Kernel.Defs

/-!
# The rerooting kernel on rooted graph classes

The uniform neighbor law descends to a measurable probability kernel on the
space of realized rooted-ball classes.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Choose a connected network representing a realized rooted graph class. -/
noncomputable def goodNetClassRepresentative (c : RootedBallClass) : GoodNet :=
  Classical.choose c.property

/-- The chosen representative has the prescribed rooted graph class. -/
theorem goodNetClass_representative (c : RootedBallClass) :
    goodNetClass (goodNetClassRepresentative c) = c := by
  apply Subtype.ext
  exact Classical.choose_spec c.property

/-- Uniformly reroot a representative and take the resulting class law. -/
noncomputable def classRerootMeasure (c : RootedBallClass) : Measure RootedBallClass :=
  let N := goodNetClassRepresentative c
  ((netGraph N.1).degree (netRoot N.1) : ℝ≥0∞)⁻¹ •
    ∑ y ∈ (netGraph N.1).neighborFinset (netRoot N.1),
      Measure.dirac (goodNetClass ⟨netReroot N.1 y, netGood_netReroot N.2 y⟩)

/-- The uniform rerooting class law is a probability measure. -/
instance isProbabilityMeasure_classRerootMeasure (c : RootedBallClass) :
    IsProbabilityMeasure (classRerootMeasure c) := by
  classical
  let N := goodNetClassRepresentative c
  have hcard : ((netGraph N.1).neighborFinset (netRoot N.1)).card =
      (netGraph N.1).degree (netRoot N.1) := rfl
  have hpos : (((netGraph N.1).degree (netRoot N.1) : ℕ) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (degree_netRoot_pos N.2).ne'
  have htop : ((netGraph N.1).degree (netRoot N.1) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  constructor
  change (((netGraph N.1).degree (netRoot N.1) : ℝ≥0∞)⁻¹ •
    ∑ y ∈ (netGraph N.1).neighborFinset (netRoot N.1),
      Measure.dirac (goodNetClass ⟨netReroot N.1 y, netGood_netReroot N.2 y⟩)) Set.univ = 1
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul, hcard,
    ENNReal.inv_mul_cancel hpos htop]

/-- Evaluation of the class rerooting law is the neighbor average of the class indicator. -/
theorem classRerootMeasure_apply (c : RootedBallClass) {D : Set RootedBallClass}
    (hD : MeasurableSet D) :
    classRerootMeasure c D =
      rerootAvg (goodNetExtend ((D.indicator (1 : RootedBallClass → ℝ≥0∞)) ∘ goodNetClass))
        (goodNetClassRepresentative c).1 := by
  classical
  let N := goodNetClassRepresentative c
  have hsum : ∀ y ∈ (netGraph N.1).neighborFinset (netRoot N.1),
      D.indicator (1 : RootedBallClass → ℝ≥0∞) (goodNetClass ⟨netReroot N.1 y, netGood_netReroot N.2 y⟩) =
        goodNetExtend ((D.indicator (1 : RootedBallClass → ℝ≥0∞)) ∘ goodNetClass)
          (netReroot N.1 y) := by
    intro y _
    simpa only [Function.comp_apply] using
      (goodNetExtend_of_good ((D.indicator (1 : RootedBallClass → ℝ≥0∞)) ∘ goodNetClass)
        (netReroot N.1 y) (netGood_netReroot N.2 y)).symm
  change (((netGraph N.1).degree (netRoot N.1) : ℝ≥0∞)⁻¹ •
    ∑ y ∈ (netGraph N.1).neighborFinset (netRoot N.1),
      Measure.dirac (goodNetClass ⟨netReroot N.1 y, netGood_netReroot N.2 y⟩)) D = _
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp_rw [Measure.dirac_apply' _ hD]
  rw [Finset.sum_congr rfl hsum]
  simp only [smul_eq_mul, rerootAvg, div_eq_mul_inv, mul_comm]
  rfl

/-- Evaluation of the class rerooting law is measurable in the class. -/
theorem measurable_classRerootMeasure_apply {D : Set RootedBallClass} (hD : MeasurableSet D) :
    Measurable fun c => classRerootMeasure c D := by
  let f : RootedBallClass → ℝ≥0∞ := D.indicator (1 : RootedBallClass → ℝ≥0∞)
  have hf : Measurable f := measurable_const.indicator hD
  obtain ⟨g, hg, hgeq⟩ := exists_measurable_classRerootAvg f hf
  have heq : (fun c => classRerootMeasure c D) = g := by
    funext c
    rw [classRerootMeasure_apply c hD]
    have h := hgeq (goodNetClassRepresentative c)
    rw [goodNetClass_representative] at h
    exact h.symm
  rw [heq]
  exact hg

/-- The uniform rerooting transition kernel on rooted graph classes. -/
noncomputable def classRerootKernel : Kernel RootedBallClass RootedBallClass where
  toFun := classRerootMeasure
  measurable' := Measure.measurable_of_measurable_coe _ fun _ hD =>
    measurable_classRerootMeasure_apply hD

/-- The class rerooting kernel is Markov. -/
instance isMarkovKernel_classRerootKernel : IsMarkovKernel classRerootKernel :=
  ⟨fun c => by
    change IsProbabilityMeasure (classRerootMeasure c)
    infer_instance⟩

end RWRS.Support
