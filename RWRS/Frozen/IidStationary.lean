/-
Proposition 2.3 of `rwrs.tex`, frozen.  `rwrs.tex:257-259` (label
`prop:iid-stationary`):

  "Let $(G,\rho)$ be a stationary random rooted graph, and given $G$, let
   $(\sigma(v))_{v\in V}$ be i.i.d. with a fixed common law $\nu$, sampled
   independently of $(G,\rho)$.  Then $(G,\rho,\sigma)$ is a stationary random
   rooted network."

A random rooted graph is a law on `Net 0`, the networks with no marks, and
decorating it with an independent i.i.d. field of common law `ν` is `markIid`.
-/
import RWRS.Support.Marking

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.iidStationary (Q : Measure (RWRS.Net 0)) (hQ : IsProbabilityMeasure Q)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hstat : RWRS.IsStationaryNet Q) :
    RWRS.IsStationaryNet (RWRS.markIid Q ν)
-- FROZEN-STATEMENT-END
:= by
  haveI := hQ
  haveI := hν
  rw [RWRS.Support.isStationaryNet_iff]
  intro h hm hinv
  have hs := (RWRS.Support.isStationaryNet_iff Q).mp hstat (RWRS.Support.markAvg ν h)
    (RWRS.Support.measurable_markAvg ν hm) (RWRS.Support.markAvg_invariant ν hm hinv)
  rw [RWRS.Support.lintegral_markIid Q ν hm, hs,
    RWRS.Support.lintegral_markIid Q ν (RWRS.Support.measurable_rerootAvg hm)]
  exact lintegral_congr fun N => (RWRS.Support.markAvg_rerootAvg ν hm N).symm
