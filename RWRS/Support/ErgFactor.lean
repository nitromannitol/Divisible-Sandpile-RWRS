/-
The Bochner form of the independence of the mark at the root from the rooted
graph.

The marked law is the image of a product, so a function of the mark at the root
times a function of the rooted graph integrates as the product of the two
integrals.  This is what the paper uses to read the conserved mass as
`E[σ] E[1/deg(ρ)]` and to get `E|σ| < ∞` from `E[|σ(ρ)|/deg(ρ)] < ∞`
(`rwrs.tex:357`).  Integrability on the product comes from the non-negative form
of the same identity.
-/
import RWRS.Support.ErgMass

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal


theorem measurable_netConfig_root :
    Measurable fun M : RWRS.Net 1 => RWRS.netConfig M (RWRS.netRoot M) := by
  have hpair : Measurable fun q : RWRS.Net 1 × ℕ => RWRS.netConfig q.1 q.2 :=
    measurable_from_prod_countable_left fun r =>
      (measurable_pi_apply (0 : Fin 1)).comp
        ((measurable_pi_apply r).comp (measurable_snd.comp measurable_snd))
  exact hpair.comp (measurable_id.prodMk measurable_netRoot)

theorem integrable_markIid_mark_mul (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {f : ℝ → ℝ} (hf : Measurable f)
    {w : RWRS.Net 0 → ℝ} (hw : Measurable w) (hfi : Integrable f ν) (hwi : Integrable w Q) :
    Integrable (fun M : RWRS.Net 1 =>
      f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M)) (RWRS.markIid Q ν) := by
  have hmeas : Measurable fun M : RWRS.Net 1 =>
      f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M) :=
    (hf.comp measurable_netConfig_root).mul (hw.comp measurable_forgetMarks)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hsplit : ∀ M : RWRS.Net 1,
      ‖f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M)‖ₑ
        = ‖f (RWRS.netConfig M (RWRS.netRoot M))‖ₑ * ‖w (RWRS.forgetMarks M)‖ₑ := by
    intro M; exact enorm_mul _ _
  rw [HasFiniteIntegral]
  simp only [hsplit]
  rw [lintegral_markIid_mark_mul Q ν (f := fun z => ‖f z‖ₑ) hf.enorm
    (w := fun N => ‖w N‖ₑ) hw.enorm]
  exact ENNReal.mul_lt_top hfi.2 hwi.2


/-- The Bochner form: the mark at the root is independent of the rooted graph. -/
theorem integral_markIid_mark_mul (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {f : ℝ → ℝ} (hf : Measurable f)
    {w : RWRS.Net 0 → ℝ} (hw : Measurable w) (hfi : Integrable f ν) (hwi : Integrable w Q) :
    (∫ M, f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M) ∂(RWRS.markIid Q ν))
      = (∫ z, f z ∂ν) * ∫ N, w N ∂Q := by
  haveI := instIsProbabilityMeasureIidLaw (V := ℕ) ν
  have hmeas : Measurable fun M : RWRS.Net 1 =>
      f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M) :=
    (hf.comp measurable_netConfig_root).mul (hw.comp measurable_forgetMarks)
  have hgi := integrable_markIid_mark_mul Q ν hf hw hfi hwi
  have hpt : ∀ p : RWRS.Net 0 × (ℕ → ℝ),
      f (RWRS.netConfig (markMap p) (RWRS.netRoot (markMap p))) * w (RWRS.forgetMarks (markMap p))
        = f (p.2 (RWRS.netRoot p.1)) * w p.1 := by
    intro p
    rw [forgetMarks_markMap]
    rfl
  have hmap : (∫ M, f (RWRS.netConfig M (RWRS.netRoot M)) * w (RWRS.forgetMarks M)
        ∂(RWRS.markIid Q ν))
      = ∫ p : RWRS.Net 0 × (ℕ → ℝ), f (p.2 (RWRS.netRoot p.1)) * w p.1
          ∂(Q.prod (RWRS.iidLaw ℕ ν)) := by
    rw [markIid_eq_map, integral_map measurable_markMap.aemeasurable hmeas.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hFint : Integrable (fun p : RWRS.Net 0 × (ℕ → ℝ) => f (p.2 (RWRS.netRoot p.1)) * w p.1)
      (Q.prod (RWRS.iidLaw ℕ ν)) := by
    rw [markIid_eq_map] at hgi
    have h2 := (integrable_map_measure hmeas.aestronglyMeasurable
      measurable_markMap.aemeasurable).mp hgi
    exact h2.congr (Filter.Eventually.of_forall hpt)
  rw [hmap, integral_prod _ hFint]
  have hinner : ∀ N : RWRS.Net 0,
      (∫ ξ : ℕ → ℝ, f (ξ (RWRS.netRoot N)) * w N ∂(RWRS.iidLaw ℕ ν)) = (∫ z, f z ∂ν) * w N := by
    intro N
    rw [integral_mul_const]
    congr 1
    conv_rhs => rw [← map_eval_iidLaw (V := ℕ) ν (RWRS.netRoot N)]
    exact (integral_map (measurable_pi_apply _).aemeasurable hf.aestronglyMeasurable).symm
  simp only [hinner]
  exact integral_const_mul _ _

end RWRS.Support
