/-
Lemma 2.7 of `rwrs.tex`, frozen.  `rwrs.tex:329-334` (label
`lem:01-stationary`):

  "Let $(G,\rho)$ be a stationary random rooted graph that is almost surely
   infinite, and let $(\sigma(v))_{v\in V}$ be i.i.d. random variables sampled
   independently of $(G,\rho)$.  Then
   $\P(\sigma\text{ stabilizes}\mid\mathcal I_G)\in\{0,1\}$ a.s."

`I_G` is the σ-algebra of `rwrs.tex:244`: the rerooting-invariant events of the
underlying rooted graph. On a marked network it is read through `forgetMarks`,
as `graphInvariantSigma 1`. The inclusion `I_G ⊆ σ(G,ρ)` keeps the marks i.i.d.
under the conditional law (`rwrs.tex:337-340`).

The conditional probability is the conditional expectation of the indicator of
the stabilization event, and the assertion is that it takes only the values `0`
and `1`, almost surely.

The proof is the paper's.  The ergodic decomposition gives the conditional law
`K` of the rooted graph given `I_G`; almost every component is supported on
connected rooted graphs, stationary and ergodic, so
`lem:ergodic-marked-stationary` makes its i.i.d. marking ergodic; the
stabilization event is rerooting invariant, so it has probability `0` or `1`
under each marked component; and the conditional expectation of its indicator
is exactly the component probability, because the conditioning reads only the
rooted graph and the marks are sampled independently of it.
-/
import RWRS.External.ErgodicDecomposition
import RWRS.Frozen.ErgodicMarked
import RWRS.Support.ErgCondLaw
import RWRS.Support.ErgStab
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.zeroOneStationary
    (hHKV : ∀ N : RWRS.Net 0, RWRS.NetGood N →
      RWRS.External.HeatKernelVanishing (RWRS.netGraph N))
    (hED : RWRS.External.ErgodicDecomposition)
    (Q : Measure (RWRS.Net 0)) (hQ : IsProbabilityMeasure Q)
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) :
    ∀ᵐ N ∂(RWRS.markIid Q ν),
      (RWRS.markIid Q ν)[Set.indicator
          {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)}
          (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1] N = 0 ∨
      (RWRS.markIid Q ν)[Set.indicator
          {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)}
          (fun _ => (1 : ℝ)) | RWRS.graphInvariantSigma 1] N = 1
-- FROZEN-STATEMENT-END
:= by
  haveI := hQ
  haveI := hν
  set A := {M : RWRS.Net 1 | RWRS.Stabilizes (RWRS.netGraph M) (RWRS.netConfig M)} with hAdef
  have hAmeas : MeasurableSet A := RWRS.Support.measurableSet_stabilizesNet
  have hAsig : (RWRS.invariantSigma 1).MeasurableSet' A :=
    ⟨hAmeas, RWRS.Support.netInvariantSet_stabilizes, RWRS.Support.rerootInvariant_stabilizes⟩
  obtain ⟨K, hKprob, hKmeas, hKid, hKae⟩ := hED Q hQ hgood hstat
  have hcond := RWRS.Support.condExp_indicator_markIid Q ν K hKprob hKmeas hKid hAmeas
  have hcomp : ∀ᵐ N ∂Q, RWRS.markIid (K N) ν A = 0 ∨ RWRS.markIid (K N) ν A = 1 := by
    filter_upwards [hKae] with N hN
    exact (RWRS.Frozen.ergodicMarked hHKV (K N) (hKprob N) hN.1 hN.2.1 hN.2.2 ν hν).2 A hAsig
  have hqmp : Measure.QuasiMeasurePreserving RWRS.forgetMarks (RWRS.markIid Q ν) Q :=
    ⟨RWRS.Support.measurable_forgetMarks, by
      rw [RWRS.Support.map_forgetMarks_markIid Q ν]⟩
  filter_upwards [hcond, hqmp.ae hcomp] with M h1 h2
  rcases h2 with h2 | h2
  · exact Or.inl (by rw [← h1, h2, ENNReal.toReal_zero])
  · exact Or.inr (by rw [← h1, h2, ENNReal.toReal_one])
