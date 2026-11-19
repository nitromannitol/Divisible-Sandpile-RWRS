import RWRS.Support.RootedClassPathConditional
import RWRS.Support.RootedClassPathInvariantValues
import RWRS.Support.RootedClassHarmonicInvariant
import Mathlib.Probability.Martingale.Convergence

/-!
# Invariant information of a stationary class walk

A bounded shift-invariant path observable is almost surely an invariant
function of the initial rooted class.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Preorder Filtration Filter
open scoped Topology

/-- A shift-invariant path observable is unchanged by dropping any finite prefix. -/
theorem rootedClassPathDrop_invariant {L : (ℕ → RootedBallClass) → ℝ}
    (hshift : ∀ x, L (rootedClassPathShift x) = L x) (n : ℕ) (x : ℕ → RootedBallClass) :
    L (rootedClassPathDrop n x) = L x := by
  induction n with
  | zero =>
      congr 1
      funext k
      simp only [rootedClassPathDrop, Nat.zero_add]
  | succ n ih =>
      have hdrop : rootedClassPathDrop (n + 1) x = rootedClassPathShift (rootedClassPathDrop n x) := by
        funext k
        simp only [rootedClassPathDrop, rootedClassPathShift]
        congr 1
        omega
      rw [hdrop, hshift, ih]

/-- A shift-invariant observable has continuation mean equal to its last-state path mean. -/
theorem integral_rootedClassTraj_eq_pathMean (n : ℕ)
    (u : Finset.Iic n → RootedBallClass) {L : (ℕ → RootedBallClass) → ℝ}
    (hL : Measurable L) (hshift : ∀ x, L (rootedClassPathShift x) = L x) :
    (∫ x, L x ∂Kernel.traj rootedClassPathStep n u) =
      rootedClassPathMean L (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
  calc
    (∫ x, L x ∂Kernel.traj rootedClassPathStep n u) =
        ∫ x, L (rootedClassPathDrop n x) ∂Kernel.traj rootedClassPathStep n u := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (rootedClassPathDrop_invariant hshift n x).symm
    _ = ∫ x, L x ∂(Kernel.traj rootedClassPathStep n u).map (rootedClassPathDrop n) := by
      symm
      exact integral_map (measurable_rootedClassPathDrop n).aemeasurable hL.aestronglyMeasurable
    _ = rootedClassPathMean L (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) := by
      rw [rootedClassTraj_map_drop]
      rfl

/-- Finite-prefix information generates the entire class path σ-algebra. -/
theorem iSup_rootedClassPath_piLE :
    (⨆ n : ℕ, piLE (X := fun _ => RootedBallClass) n) =
      (inferInstance : MeasurableSpace (ℕ → RootedBallClass)) := by
  apply le_antisymm
  · exact iSup_le fun n => piLE.le n
  · change (⨆ i : ℕ, (inferInstance : MeasurableSpace RootedBallClass).comap
      (fun x : ℕ → RootedBallClass => x i)) ≤ _
    apply iSup_le
    intro i
    apply le_trans _ (le_iSup (fun n : ℕ => piLE (X := fun _ => RootedBallClass) n) i)
    apply Measurable.comap_le
    rw [piLE_eq_comap_frestrictLe]
    exact (measurable_pi_apply (⟨i, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic i)).comp
      (comap_measurable (frestrictLe i))

/-- Every coordinate of a stationary class walk has its initial distribution. -/
theorem rootedClassPathLaw_map_of_stationary (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (hstat : classRerootKernel ∘ₘ ν = ν) (n : ℕ) :
    (rootedClassPathLaw ν).map (fun x => x n) = ν := by
  induction n with
  | zero => exact rootedClassPathLaw_map_zero ν
  | succ n ih => rw [rootedClassPathLaw_map_succ, ih, hstat]

/-- Shift-invariant path information is an invariant observable of the initial class. -/
theorem exists_invariant_class_of_shift_invariant_path (ν : Measure RootedBallClass)
    [IsProbabilityMeasure ν] (hstat : classRerootKernel ∘ₘ ν = ν)
    {L : (ℕ → RootedBallClass) → ℝ} (hL : Measurable L)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, |L x| ≤ C)
    (hshift : ∀ x, L (rootedClassPathShift x) = L x) :
    ∃ g : RootedBallClass → ℝ, Measurable[rootedClassInvariantSigma] g ∧
      ∀ᵐ x ∂rootedClassPathLaw ν, L x = g (x 0) := by
  let P := rootedClassPathLaw ν
  let H := rootedClassPathMean L
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_rootedClassPathLaw ν
  have hi : Integrable L P := Integrable.of_bound hL.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x)
  obtain ⟨g, hg, heq⟩ := exists_invariant_version_pathMean ν hstat hL hC hbound hshift
  have hcoords : ∀ᵐ x ∂P, ∀ n, H (x n) = g (x n) := by
    apply ae_all_iff.mpr
    intro n
    have hm : (fun x : ℕ → RootedBallClass => x n) ⁻¹'
        {c | H c = g c} = {x | H (x n) = g (x n)} := rfl
    have hmeas : MeasurableSet {c | H c = g c} :=
      measurableSet_eq_fun (measurable_rootedClassPathMean hL)
        (hg.mono rootedClassInvariantSigma_le le_rfl)
    have hmap : ∀ᵐ c ∂P.map (fun x => x n), H c = g c := by
      rw [rootedClassPathLaw_map_of_stationary ν hstat n]
      exact heq
    exact (ae_map_iff (measurable_pi_apply n).aemeasurable hmeas).1 hmap
  have hgpath := ae_rootedClassPathLaw_invariantValue ν hg
  have hce : ∀ᵐ x ∂P, ∀ n, (P[L | piLE n]) x = H (x n) := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [condExp_rootedClassPathLaw_traj ν n hL hbound] with x hx
    rw [hx, integral_rootedClassTraj_eq_pathMean n (frestrictLe n x) hL hshift]
    rfl
  have hLmeas : StronglyMeasurable[⨆ n : ℕ, piLE (X := fun _ => RootedBallClass) n] L := by
    rw [iSup_rootedClassPath_piLE]
    exact hL.stronglyMeasurable
  have hlim := hi.tendsto_ae_condExp (ℱ := piLE) hLmeas
  refine ⟨g, hg, ?_⟩
  filter_upwards [hcoords, hgpath, hce, hlim] with x hx hpath hcond hlimx
  have hconst : ∀ n, (P[L | piLE n]) x = g (x 0) :=
    fun n => (hcond n).trans ((hx n).trans (hpath n))
  have ht : Tendsto (fun n => (P[L | piLE n]) x) atTop (𝓝 (g (x 0))) := by
    simpa only [hconst] using tendsto_const_nhds
  exact (tendsto_nhds_unique hlimx ht)

end RWRS.Support
