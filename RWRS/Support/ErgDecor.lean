/-
The decorrelation of two splice averages at distant roots.

Two splice averages of radius `r` whose balls are disjoint read disjoint sets of
marks, so under the i.i.d. field they are independent and the mark average of
their product is the product of their mark averages.  That is the conditional
independence of `rwrs.tex:319`.  The walk average of the product is then handled
by the exchange of the mark average with the iterated reroot average, which is a
finite sum divided by a constant at every step.
-/
import RWRS.Support.ErgSplice

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal Classical

/-- The splice average reads the marks only inside the ball. -/
theorem ballAvg_congr (ν : Measure ℝ) (r : ℕ) (h : RWRS.Net 1 → ℝ≥0∞) (M : RWRS.Net 0)
    {ξ ξ' : ℕ → ℝ} (hagree : ∀ i ∈ netBallX M r, ξ i = ξ' i) :
    ballAvg ν r h M ξ = ballAvg ν r h M ξ' := by
  refine lintegral_congr fun η => ?_
  have : netComb M r ξ η = netComb M r ξ' η := by
    funext i
    by_cases hi : i ∈ netBallX M r
    · rw [netComb_of_mem hi, netComb_of_mem hi, hagree i hi]
    · rw [netComb_of_notMem hi, netComb_of_notMem hi]
  rw [this]

theorem measurable_ballAvg_fixed (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ)
    {h : RWRS.Net 1 → ℝ≥0∞} (hm : Measurable h) (M : RWRS.Net 0) :
    Measurable (ballAvg ν r h M) :=
  (measurable_ballAvg ν r hm).comp ((measurable_const (a := M)).prodMk measurable_id)

theorem rerootIter_congr_reroot {m : ℕ} {Ψ Ψ' : RWRS.Net m → ℝ≥0∞} :
    ∀ (n : ℕ) (N : RWRS.Net m), (∀ v : ℕ, Ψ (RWRS.netReroot N v) = Ψ' (RWRS.netReroot N v)) →
      (rerootAvg^[n] Ψ) N = (rerootAvg^[n] Ψ') N := by
  intro n
  induction n with
  | zero =>
      intro N hN
      have hb := hN (RWRS.netRoot N)
      rw [show RWRS.netReroot N (RWRS.netRoot N) = N from rfl] at hb
      simpa using hb
  | succ n ih =>
      intro N hN
      have hstep : ∀ g : RWRS.Net m → ℝ≥0∞, rerootAvg^[n + 1] g = rerootAvg (rerootAvg^[n] g) := by
        intro g; rw [Function.iterate_succ']; rfl
      rw [hstep Ψ, hstep Ψ', rerootAvg, rerootAvg]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      exact ih (RWRS.netReroot N y) (fun v => hN v)

theorem lintegral_rerootAvg_exchange {m : ℕ} {P : Measure (ℕ → ℝ)} [SFinite P]
    (Ψ : RWRS.Net m → (ℕ → ℝ) → ℝ≥0∞) (hΨ : ∀ M, Measurable (Ψ M)) (N : RWRS.Net m) :
    ∫⁻ ξ, rerootAvg (fun M => Ψ M ξ) N ∂P = rerootAvg (fun M => ∫⁻ ξ, Ψ M ξ ∂P) N := by
  simp only [rerootAvg, div_eq_mul_inv]
  rw [lintegral_mul_const'' _ (Finset.measurable_sum
    ((RWRS.netGraph N).neighborFinset (RWRS.netRoot N))
    (fun y _ => hΨ (RWRS.netReroot N y))).aemeasurable]
  congr 1
  exact lintegral_finsetSum _ (fun y _ => hΨ (RWRS.netReroot N y))

theorem lintegral_ballAvg_mul (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ)
    {h : RWRS.Net 1 → ℝ≥0∞} (hm : Measurable h) (N : RWRS.Net 0) (v : ℕ)
    (hdisj : Disjoint (netBallX N r) (netBallX (RWRS.netReroot N v) r)) :
    ∫⁻ ξ, ballAvg ν r h N ξ * ballAvg ν r h (RWRS.netReroot N v) ξ ∂(RWRS.iidLaw ℕ ν)
      = (∫⁻ ξ, ballAvg ν r h N ξ ∂(RWRS.iidLaw ℕ ν))
        * ∫⁻ ξ, ballAvg ν r h (RWRS.netReroot N v) ξ ∂(RWRS.iidLaw ℕ ν) := by
  haveI : IsProbabilityMeasure (RWRS.iidLaw ℕ ν) := instIsProbabilityMeasureIidLaw ν
  have hg : Measurable (ballAvg ν r h N) := measurable_ballAvg_fixed ν r hm N
  have hk : Measurable (ballAvg ν r h (RWRS.netReroot N v)) :=
    measurable_ballAvg_fixed ν r hm (RWRS.netReroot N v)
  have hF : Measurable fun ζ : ℕ → ℝ =>
      ballAvg ν r h N ζ * ballAvg ν r h (RWRS.netReroot N v) ζ := hg.mul hk
  have hcomp : ∫⁻ p : (ℕ → ℝ) × (ℕ → ℝ),
      (ballAvg ν r h N (netComb N r p.1 p.2)
        * ballAvg ν r h (RWRS.netReroot N v) (netComb N r p.1 p.2))
      ∂((RWRS.iidLaw ℕ ν).prod (RWRS.iidLaw ℕ ν))
      = ∫⁻ ζ, ballAvg ν r h N ζ * ballAvg ν r h (RWRS.netReroot N v) ζ ∂(RWRS.iidLaw ℕ ν) :=
    (measurePreserving_netComb ν N r).lintegral_comp hF
  have hpt : ∀ p : (ℕ → ℝ) × (ℕ → ℝ),
      ballAvg ν r h N (netComb N r p.1 p.2)
        * ballAvg ν r h (RWRS.netReroot N v) (netComb N r p.1 p.2)
      = ballAvg ν r h N p.1 * ballAvg ν r h (RWRS.netReroot N v) p.2 := by
    rintro ⟨ξ, η⟩
    rw [ballAvg_netComb ν r h N ξ η]
    congr 1
    refine ballAvg_congr ν r h (RWRS.netReroot N v) ?_
    intro i hi
    exact netComb_of_notMem (fun hc => (Set.disjoint_left.1 hdisj) hc hi) ξ η
  have hae : AEMeasurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
      ballAvg ν r h N p.1 * ballAvg ν r h (RWRS.netReroot N v) p.2)
      ((RWRS.iidLaw ℕ ν).prod (RWRS.iidLaw ℕ ν)) :=
    ((hg.comp measurable_fst).mul (hk.comp measurable_snd)).aemeasurable
  rw [← hcomp, lintegral_congr hpt, lintegral_prod _ hae]
  rw [lintegral_congr fun ξ => lintegral_const_mul'' (ballAvg ν r h N ξ) hk.aemeasurable]
  rw [lintegral_mul_const'' _ hg.aemeasurable]

end RWRS.Support
