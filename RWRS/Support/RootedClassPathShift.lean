import RWRS.Support.RootedClassPathMap
import RWRS.Support.RootedClassPathStationaryMarginals

/-!
# Shifted rooted-class path laws

Dropping the first state of a class walk gives the class walk started from the
one-step image of the initial distribution.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder

/-- Adjoin a final state to a finite prefix. -/
def rootedClassPrefixAppend (n : ℕ)
    (p : (Finset.Iic n → RootedBallClass) × RootedBallClass) :
    Finset.Iic (n + 1) → RootedBallClass :=
  fun i => if h : i.1 ≤ n then p.1 ⟨i.1, Finset.mem_Iic.mpr h⟩ else p.2

/-- Adjoining a state to a finite prefix is measurable. -/
theorem measurable_rootedClassPrefixAppend (n : ℕ) :
    Measurable (rootedClassPrefixAppend n) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i.1 ≤ n
  · simpa only [rootedClassPrefixAppend, dif_pos h, Function.comp_def] using
      (measurable_pi_apply (⟨i.1, Finset.mem_Iic.mpr h⟩ : Finset.Iic n)).comp
        (measurable_fst : Measurable (Prod.fst :
          (Finset.Iic n → RootedBallClass) × RootedBallClass → _))
  · simpa only [rootedClassPrefixAppend, dif_neg h] using
      (measurable_snd : Measurable (Prod.snd :
        (Finset.Iic n → RootedBallClass) × RootedBallClass → _))

/-- A prefix and its next state reconstruct the next prefix. -/
theorem rootedClassPrefixAppend_restrict (n : ℕ) (x : ℕ → RootedBallClass) :
    rootedClassPrefixAppend n (frestrictLe n x, x (n + 1)) = frestrictLe (n + 1) x := by
  funext i
  by_cases h : i.1 ≤ n
  · simp only [rootedClassPrefixAppend, dif_pos h, frestrictLe_apply]
  · have hi : i.1 = n + 1 := by
      have := Finset.mem_Iic.mp i.2
      omega
    change (if h : i.1 ≤ n then x (⟨i.1, Finset.mem_Iic.mpr h⟩ : Finset.Iic n).1
      else x (n + 1)) = x i.1
    rw [dif_neg h, hi]

/-- Equal prefix laws and equal transition laws give equal next prefix laws. -/
theorem map_frestrictLe_succ_eq_of_transition
    (μ η : Measure (ℕ → RootedBallClass)) (n : ℕ)
    (hprefix : μ.map (frestrictLe n) = η.map (frestrictLe n))
    (hμ : μ.map (frestrictLe n) ⊗ₘ rootedClassPathStep n =
      μ.map (fun x => (frestrictLe n x, x (n + 1))))
    (hη : η.map (frestrictLe n) ⊗ₘ rootedClassPathStep n =
      η.map (fun x => (frestrictLe n x, x (n + 1)))) :
    μ.map (frestrictLe (n + 1)) = η.map (frestrictLe (n + 1)) := by
  have hpair : μ.map (fun x => (frestrictLe n x, x (n + 1))) =
      η.map (fun x => (frestrictLe n x, x (n + 1))) := by
    rw [← hμ, ← hη, hprefix]
  have h := congrArg (fun ρ => ρ.map (rootedClassPrefixAppend n)) hpair
  rw [Measure.map_map (measurable_rootedClassPrefixAppend n)
      ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))),
    Measure.map_map (measurable_rootedClassPrefixAppend n)
      ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1)))] at h
  simpa only [Function.comp_def, rootedClassPrefixAppend_restrict] using h

/-- Two path laws with the same initial state law and transition rule coincide. -/
theorem rootedClassPathLaw_unique
    (μ η : Measure (ℕ → RootedBallClass)) [IsProbabilityMeasure μ] [IsProbabilityMeasure η]
    (hzero : μ.map (fun x => x 0) = η.map (fun x => x 0))
    (hμ : ∀ n, μ.map (frestrictLe n) ⊗ₘ rootedClassPathStep n =
      μ.map (fun x => (frestrictLe n x, x (n + 1))))
    (hη : ∀ n, η.map (frestrictLe n) ⊗ₘ rootedClassPathStep n =
      η.map (fun x => (frestrictLe n x, x (n + 1)))) : μ = η := by
  have hprefix : ∀ n, μ.map (frestrictLe n) = η.map (frestrictLe n) := by
    intro n
    induction n with
    | zero =>
        let e := MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => RootedBallClass)
        have hf : (frestrictLe 0 : (ℕ → RootedBallClass) → _) =
            e.symm ∘ (fun x => x 0) := by
          funext x i
          have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
          simp [frestrictLe_apply, e, hi]
        rw [hf, ← Measure.map_map e.symm.measurable (measurable_pi_apply 0),
          ← Measure.map_map e.symm.measurable (measurable_pi_apply 0), hzero]
    | succ n ih => exact map_frestrictLe_succ_eq_of_transition μ η n ih (hμ n) (hη n)
  refine ext_of_generate_finite (measurableCylinders (fun _ : ℕ => RootedBallClass))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro s hs
    obtain ⟨n, S, hS, rfl⟩ : ∃ n S, MeasurableSet S ∧
        s = cylinder (Finset.Iic n) S := by
      simpa [measurableCylinders_nat] using hs
    change μ (frestrictLe n ⁻¹' S) = η (frestrictLe n ⁻¹' S)
    rw [← Measure.map_apply (measurable_frestrictLe n) hS,
      ← Measure.map_apply (measurable_frestrictLe n) hS, hprefix n]
  · rw [measure_univ, measure_univ]

/-- The shifted rooted-class path starts with the one-step image of its initial law. -/
theorem rootedClassPathLaw_map_shift (ν : Measure RootedBallClass) [IsProbabilityMeasure ν] :
    (rootedClassPathLaw ν).map rootedClassPathShift =
      rootedClassPathLaw (classRerootKernel ∘ₘ ν) := by
  haveI : IsProbabilityMeasure (rootedClassPathLaw ν) := isProbabilityMeasure_rootedClassPathLaw ν
  haveI : IsProbabilityMeasure ((rootedClassPathLaw ν).map rootedClassPathShift) :=
    Measure.isProbabilityMeasure_map measurable_rootedClassPathShift.aemeasurable
  haveI : IsProbabilityMeasure (classRerootKernel ∘ₘ ν) := by infer_instance
  haveI : IsProbabilityMeasure (rootedClassPathLaw (classRerootKernel ∘ₘ ν)) :=
    isProbabilityMeasure_rootedClassPathLaw _
  apply rootedClassPathLaw_unique
  · rw [Measure.map_map (measurable_pi_apply 0) measurable_rootedClassPathShift,
      rootedClassPathLaw_map_zero]
    change (rootedClassPathLaw ν).map (fun x => x (0 + 1)) = _
    rw [rootedClassPathLaw_map_succ, rootedClassPathLaw_map_zero]
  · exact rootedClassPathLaw_shift_prefix ν
  · exact rootedClassPathLaw_prefix (classRerootKernel ∘ₘ ν)

/-- A stationary class law makes path shift measure preserving. -/
theorem measurePreserving_rootedClassPathShift (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (hstat : classRerootKernel ∘ₘ ν = ν) :
    MeasurePreserving rootedClassPathShift (rootedClassPathLaw ν) (rootedClassPathLaw ν) := by
  refine ⟨measurable_rootedClassPathShift, ?_⟩
  rw [rootedClassPathLaw_map_shift, hstat]

/-- The class walk of a stationary connected network has a shift-preserving path law. -/
theorem measurePreserving_rootedClassPathShift_goodNetClassLaw (Q : Measure (Net 0))
    [IsProbabilityMeasure Q] (hgood : ∀ᵐ N ∂Q, NetGood N) (hstat : IsStationaryNet Q) :
    MeasurePreserving rootedClassPathShift (rootedClassPathLaw (goodNetClassLaw Q))
      (rootedClassPathLaw (goodNetClassLaw Q)) := by
  haveI := isProbabilityMeasure_goodNetClassLaw Q hgood
  exact measurePreserving_rootedClassPathShift _
    (classRerootKernel_comp_goodNetClassLaw Q hgood hstat)

end RWRS.Support
