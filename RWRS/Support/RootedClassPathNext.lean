import RWRS.Support.RootedClassPathMarginal
import RWRS.Support.RootedClassKernelStationary

/-!
# Consecutive rooted-class path marginals

The next-coordinate law is obtained by applying the rerooting kernel to the
current-coordinate law.
-/

open MeasureTheory ProbabilityTheory Preorder

namespace RWRS.Support

/-- Consecutive coordinate laws are related by the class rerooting kernel. -/
theorem rootedClassPathLaw_map_succ (ν : Measure RWRS.Support.RootedBallClass)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (RWRS.Support.rootedClassPathLaw ν).map (fun x => x (n + 1)) =
      RWRS.Support.classRerootKernel ∘ₘ
        (RWRS.Support.rootedClassPathLaw ν).map (fun x => x n) := by
  let P := RWRS.Support.rootedClassPathLaw ν
  haveI : IsProbabilityMeasure P := RWRS.Support.isProbabilityMeasure_rootedClassPathLaw ν
  haveI : IsProbabilityMeasure (P.map (frestrictLe n)) :=
    Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
  have h := congrArg Measure.snd (RWRS.Support.rootedClassPathLaw_prefix ν n)
  change ((P.map (frestrictLe n)) ⊗ₘ RWRS.Support.rootedClassPathStep n).snd =
    (P.map (fun x => (frestrictLe n x, x (n + 1)))).snd at h
  rw [Measure.snd_compProd] at h
  have hrhs : (P.map (fun x => (frestrictLe n x, x (n + 1)))).snd =
      P.map (fun x => x (n + 1)) := by
    let F : (ℕ → RWRS.Support.RootedBallClass) →
        ((Finset.Iic n → RWRS.Support.RootedBallClass) × RWRS.Support.RootedBallClass) :=
      fun x => (frestrictLe n x, x (n + 1))
    change (P.map F).map Prod.snd = _
    have hF : Measurable F :=
      (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))
    rw [Measure.map_map measurable_snd hF]
    rfl
  rw [hrhs] at h
  have hleft : RWRS.Support.rootedClassPathStep n ∘ₘ (P.map (frestrictLe n)) =
      RWRS.Support.classRerootKernel ∘ₘ P.map (fun x => x n) := by
    ext D hD
    rw [Measure.bind_apply hD (Kernel.aemeasurable _),
      Measure.bind_apply hD (Kernel.aemeasurable _)]
    rw [lintegral_map (Kernel.measurable_coe _ hD) (measurable_frestrictLe n),
      lintegral_map (Kernel.measurable_coe _ hD) (measurable_pi_apply n)]
    rfl
  exact h.symm.trans hleft

end RWRS.Support
