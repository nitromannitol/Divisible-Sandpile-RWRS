/-
Reading a scenery on an arbitrary vertex set through a finite index set.

The three cited inequalities of `lem:fuk-nagaev` are stated for a probability
space and an index set in the lowest universe, which is where a citation lives;
the vertex set of a graph is at an arbitrary universe, so they cannot be applied
to the scenery directly.  They can be applied to the scenery indexed by
`Fin n`, and this module carries the answer back: the field on `V` read along a
bijection `Fin n ≃ S` is the i.i.d. field indexed by `Fin n`, so every event of
the finite field has the same probability under either law.
-/
import RWRS.Support.IidMap
import Mathlib.Probability.ProductMeasure

open MeasureTheory

namespace RWRS.Support

variable {V : Type*} {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- **The field read along a bijection is the i.i.d. field on `Fin n`.** -/
theorem iidLaw_map_equiv (S : Set V) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (e : Fin n ≃ S) :
    (RWRS.iidLaw V ν).map (fun ξ : V → ℝ => fun j : Fin n => ξ ((e j : S) : V))
      = RWRS.iidLaw (Fin n) ν := by
  have h1 : (RWRS.iidLaw (Fin n) ν).map (MeasurableEquiv.piCongrLeft (fun _ : S => ℝ) e)
      = RWRS.iidLaw (S : Type _) ν := by
    simpa [RWRS.iidLaw] using
      (Measure.infinitePi_map_piCongrLeft (μ := fun _ : S => ν) e)
  have h3 : (RWRS.iidLaw (S : Type _) ν).map
        (MeasurableEquiv.piCongrLeft (fun _ : S => ℝ) e).symm = RWRS.iidLaw (Fin n) ν := by
    rw [← h1, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
    simp
  have hfac : (fun ξ : V → ℝ => fun j : Fin n => ξ ((e j : S) : V))
      = (MeasurableEquiv.piCongrLeft (fun _ : S => ℝ) e).symm ∘ (S.restrict) := by
    funext ξ
    funext j
    simp [MeasurableEquiv.piCongrLeft, Set.restrict]
  rw [hfac, ← h3, ← iidLaw_restrict S ν]
  exact (Measure.map_map (MeasurableEquiv.measurable _) (Set.measurable_restrict S)).symm

theorem measurable_readAlong (S : Set V) {n : ℕ} (e : Fin n ≃ S) :
    Measurable (fun ξ : V → ℝ => fun j : Fin n => ξ ((e j : S) : V)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- **The transfer of an event.**  An event of the field read along the
bijection has the same probability under the two laws. -/
theorem meas_readAlong (S : Set V) {n : ℕ} (e : Fin n ≃ S)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) :
    RWRS.iidLaw V ν {ξ : V → ℝ | (fun j : Fin n => ξ ((e j : S) : V)) ∈ E}
      = RWRS.iidLaw (Fin n) ν E := by
  have h := Measure.map_apply (μ := RWRS.iidLaw V ν)
    (measurable_readAlong (V := V) S e) hE
  rw [iidLaw_map_equiv S ν e] at h
  exact h.symm

/-- Reindexing a sum over a `Finset` along a bijection from `Fin n`. -/
theorem sum_finset_eq_sum_fin {S : Finset V} {n : ℕ} (e : Fin n ≃ (S : Set V))
    (g : V → ℝ) : ∑ v ∈ S, g v = ∑ j : Fin n, g ((e j : (S : Set V)) : V) := by
  classical
  rw [← Finset.sum_coe_sort S g]
  exact (Fintype.sum_equiv e _ _ fun j => rfl).symm

end RWRS.Support
