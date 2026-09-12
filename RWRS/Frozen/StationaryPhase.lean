/-
Theorem 2.4 of `rwrs.tex`, frozen.  `rwrs.tex:268-276` (label
`thm:stationary-phase`):

  "Let $(G,\rho)$ be a stationary random rooted graph that is almost surely
   infinite, and let $(\sigma(v))_{v\in V}$ be i.i.d. random variables sampled
   independently of $(G,\rho)$, with $\E[\sigma]=\mu$ and
   $\E[|\sigma(\rho)|/\deg(\rho)]<\infty$.
   (i) If $\mu>1$, then $\P(\sigma\text{ stabilizes})=0$.
   (ii) If $\mu<1$, then $\P(\sigma\text{ stabilizes})=1$."

The mean is the extended expectation of `ssec:notation`, and the integrability
hypothesis is that of `thm:stationary-toppling`.

No σ-algebra occurs in the statement.  The proof conditions on the
rerooting-invariant events of the underlying rooted graph,
`graphInvariantSigma 1`: it needs the conditioning event to be graph-measurable,
so that the marks keep their common law under the conditional law
(`rwrs.tex:347`), and rerooting-invariant, so that the conditional law of the
rooted graph is again stationary.  The heat kernel decay is carried because the
proof reaches `lem:01-stationary`, and through it the marking lemma, on the
components of the ergodic decomposition.
-/
import RWRS.External.ErgodicDecomposition
import RWRS.External.HeatKernelVanishing
import RWRS.Frozen.ZeroOneStationary
import RWRS.Support.ErgSubFinal
import RWRS.Support.ErgCondNet

open MeasureTheory ProbabilityTheory

-- The proof reaches both conclusions through the integrability hypothesis, which
-- already forces the mark law to have a finite first moment, so the weaker
-- assumption that the extended mean exists is not referred to.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.stationaryPhase
    (hHKV : ∀ N : RWRS.Net 0, RWRS.NetGood N →
      RWRS.External.HeatKernelVanishing (RWRS.netGraph N))
    (hED : RWRS.External.ErgodicDecomposition)
    (Q : Measure (RWRS.Net 0)) (hQ : IsProbabilityMeasure Q)
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hdet : RWRS.HasExtMean ν)
    (hint : Integrable (fun N => |RWRS.netWeightedMass N|) (RWRS.markIid Q ν)) :
    (1 < RWRS.extMean ν →
      RWRS.markIid Q ν
        {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} = 0) ∧
    (RWRS.extMean ν < 1 →
      RWRS.markIid Q ν
        {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} = 1)
-- FROZEN-STATEMENT-END
:= by
  haveI := hQ
  haveI := hν
  set A := {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} with hAdef
  have hAmeas : MeasurableSet A := RWRS.Support.measurableSet_stabilizesNet
  haveI hP : IsProbabilityMeasure (RWRS.markIid Q ν) :=
    RWRS.Support.isProbabilityMeasure_markIid Q ν
  have h01 := RWRS.Frozen.zeroOneStationary hHKV hED Q hQ hgood hstat ν hν
  obtain ⟨B, hB, hPA, hinter, hcompl⟩ :=
    RWRS.Support.exists_graph_event_of_zeroOne Q ν hAmeas h01
  have hν1 : Integrable (fun z : ℝ => z) ν :=
    RWRS.Support.integrable_id_of_integrable_netWeightedMass Q hgood ν hint
  have hmean : RWRS.extMean ν = ((∫ z, z ∂ν : ℝ) : EReal) :=
    RWRS.Support.extMean_eq_integral_of_integrable ν hν1
  have hBmeas : MeasurableSet B := hB.1
  have hsmeas : MeasurableSet ((RWRS.forgetMarks ⁻¹' B : Set (RWRS.Net 1))) :=
    RWRS.Support.measurable_forgetMarks (m := 1) hBmeas
  have hPs : RWRS.markIid Q ν (RWRS.forgetMarks ⁻¹' B) = Q B := by
    rw [← Measure.map_apply RWRS.Support.measurable_forgetMarks hBmeas,
      RWRS.Support.map_forgetMarks_markIid Q ν]
  constructor
  · -- the supercritical half
    intro hgt
    by_contra hne
    have hQB : Q B ≠ 0 := by rw [← hPA]; exact hne
    haveI : IsProbabilityMeasure (Q[|B]) := cond_isProbabilityMeasure hQB
    have hgoodc : ∀ᵐ N ∂(Q[|B]), RWRS.NetGood N := RWRS.Support.ae_netGood_cond hgood B
    have hstatc : RWRS.IsStationaryNet (Q[|B]) :=
      RWRS.Support.isStationaryNet_cond hstat hBmeas hB.2.1 hB.2.2
    have hmark : RWRS.markIid (Q[|B]) ν = (RWRS.markIid Q ν)[|RWRS.forgetMarks ⁻¹' B] :=
      RWRS.Support.markIid_cond Q ν hBmeas
    have hs0 : RWRS.markIid Q ν (RWRS.forgetMarks ⁻¹' B) ≠ 0 := by rw [hPs]; exact hQB
    have hintc : Integrable (fun N => |RWRS.netWeightedMass N|) (RWRS.markIid (Q[|B]) ν) := by
      rw [hmark, ProbabilityTheory.cond]
      exact (hint.restrict).smul_measure (ENNReal.inv_ne_top.mpr hs0)
    have hone : RWRS.markIid (Q[|B]) ν A = 1 := by
      rw [hmark]
      exact RWRS.Support.cond_eq_one_of_inter (RWRS.markIid Q ν) hAmeas hinter hs0
    have hstabc : ∀ᵐ N ∂(RWRS.markIid (Q[|B]) ν),
        RWRS.Stabilizes (RWRS.netGraph N) (RWRS.netConfig N) := by
      haveI : IsProbabilityMeasure (RWRS.markIid (Q[|B]) ν) :=
        RWRS.Support.isProbabilityMeasure_markIid (Q[|B]) ν
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hAmeas).mpr hone
    have hle := RWRS.Support.integral_id_le_one_of_ae_stabilizes (Q[|B]) hgoodc hstatc ν
      hintc hstabc
    rw [hmean] at hgt
    have : (1 : ℝ) < ∫ z, z ∂ν := by exact_mod_cast hgt
    exact absurd this (not_lt.mpr hle)
  · -- the subcritical half
    intro hlt
    by_contra hne
    have hsne : RWRS.markIid Q ν (RWRS.forgetMarks ⁻¹' B) ≠ 1 := by rw [hPs, ← hPA]; exact hne
    have hcne : RWRS.markIid Q ν (RWRS.forgetMarks ⁻¹' B)ᶜ ≠ 0 := fun h =>
      hsne ((prob_compl_eq_zero_iff hsmeas).mp h)
    have hpre : ((RWRS.forgetMarks ⁻¹' B : Set (RWRS.Net 1)))ᶜ
        = (RWRS.forgetMarks ⁻¹' Bᶜ : Set (RWRS.Net 1)) := by
      rw [Set.preimage_compl]
    have hQBc : Q Bᶜ ≠ 0 := by
      intro h
      apply hcne
      rw [hpre, ← Measure.map_apply RWRS.Support.measurable_forgetMarks hBmeas.compl,
        RWRS.Support.map_forgetMarks_markIid Q ν]
      exact h
    have hBc : (RWRS.invariantSigma 0).MeasurableSet' Bᶜ :=
      (RWRS.invariantSigma 0).measurableSet_compl B hB
    haveI : IsProbabilityMeasure (Q[|Bᶜ]) := cond_isProbabilityMeasure hQBc
    have hgoodc : ∀ᵐ N ∂(Q[|Bᶜ]), RWRS.NetGood N := RWRS.Support.ae_netGood_cond hgood Bᶜ
    have hstatc : RWRS.IsStationaryNet (Q[|Bᶜ]) :=
      RWRS.Support.isStationaryNet_cond hstat hBmeas.compl hBc.2.1 hBc.2.2
    have hmark : RWRS.markIid (Q[|Bᶜ]) ν = (RWRS.markIid Q ν)[|RWRS.forgetMarks ⁻¹' Bᶜ] :=
      RWRS.Support.markIid_cond Q ν hBmeas.compl
    have hs0 : RWRS.markIid Q ν (RWRS.forgetMarks ⁻¹' Bᶜ) ≠ 0 := by rw [← hpre]; exact hcne
    have hintc : Integrable (fun N => |RWRS.netWeightedMass N|) (RWRS.markIid (Q[|Bᶜ]) ν) := by
      rw [hmark, ProbabilityTheory.cond]
      exact (hint.restrict).smul_measure (ENNReal.inv_ne_top.mpr hs0)
    have hzero : RWRS.markIid (Q[|Bᶜ]) ν A = 0 := by
      rw [hmark]
      refine RWRS.Support.cond_eq_zero_of_inter (RWRS.markIid Q ν) hAmeas ?_
      rw [← hpre]
      exact hcompl
    have hnsc : ∀ᵐ N ∂(RWRS.markIid (Q[|Bᶜ]) ν),
        ¬ RWRS.Stabilizes (RWRS.netGraph N) (RWRS.netConfig N) := by
      rw [ae_iff]
      simpa using hzero
    have hge := RWRS.Support.one_le_integral_id_of_ae_not_stabilizes (Q[|Bᶜ]) hgoodc hstatc ν
      hintc hnsc
    rw [hmean] at hlt
    have : (∫ z, z ∂ν) < (1 : ℝ) := by exact_mod_cast hlt
    exact absurd this (not_lt.mpr hge)

