/-
Lemma 2.6 of `rwrs.tex`, frozen.  `rwrs.tex:310-313` (label
`lem:ergodic-marked-stationary`):

  "Let $(G,\rho)$ be a stationary and ergodic random rooted graph that is
   almost surely infinite.  Given $(G,\rho)$, let $(\sigma(v))_{v\in V}$ be
   i.i.d. random variables with common law $\nu$, sampled independently of
   $(G,\rho)$.  Then $(G,\rho,\sigma)$ is a stationary and ergodic random
   rooted network."

Networks have vertex set `ℕ`. The hypothesis `hgood` asserts almost sure
connectedness, so the underlying graphs are almost surely infinite and connected,
as in the paper's standing setting.

The heat kernel decay quoted at `rwrs.tex:319-322` is supplied on connected
networks by `RWRS.External.heatKernelVanishing_of_netGood`. The almost sure
connectedness hypothesis of `Q` supplies `NetGood` at every use site.
-/
import RWRS.Support.ErgFinal
import RWRS.Frozen.IidStationary

open MeasureTheory
open scoped ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.ergodicMarked
    (hHKV : ∀ N : RWRS.Net 0, RWRS.NetGood N →
      RWRS.External.HeatKernelVanishing (RWRS.netGraph N))
    (Q : Measure (RWRS.Net 0)) (hQ : IsProbabilityMeasure Q)
    (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet Q)
    (herg : RWRS.IsErgodicNet Q) (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) :
    RWRS.IsStationaryNet (RWRS.markIid Q ν) ∧ RWRS.IsErgodicNet (RWRS.markIid Q ν)
-- FROZEN-STATEMENT-END
:= by
  haveI := hQ
  haveI := hν
  refine ⟨RWRS.Frozen.iidStationary Q hQ ν hν hstat, ?_⟩
  intro A hAsig
  obtain ⟨hA, hiso, hre⟩ := hAsig
  obtain ⟨c, hc0, hc1, hae, hval⟩ := RWRS.Support.exists_markProb_ae_eq Q ν herg hA hiso hre
  set C : ℝ≥0∞ := ENNReal.ofReal c with hC
  have hC1 : C ≤ 1 := by
    rw [hC, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hc1
  have hCae : ∀ᵐ N ∂Q, RWRS.Support.markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N = C := by
    filter_upwards [hae] with N hN
    have hne : RWRS.Support.markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (RWRS.Support.markAvg_indicator_le_one ν A N)
    rw [hC, ← hN, RWRS.Support.markProb, ENNReal.ofReal_toReal hne]
  have hsq : C = C * C :=
    RWRS.Support.markAvg_mul_self hHKV Q hgood hstat ν hA hiso hre hC1 hCae
  rw [hval]
  by_cases h0 : C = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    have hne : C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hC1
    have hmul : C * 1 = C * C := by rw [mul_one]; exact hsq
    exact ((ENNReal.mul_right_inj h0 hne).mp hmul).symm
