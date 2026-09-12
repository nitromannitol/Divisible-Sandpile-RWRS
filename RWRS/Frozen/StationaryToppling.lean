/-
Theorem 2.5 of `rwrs.tex`, frozen.  `rwrs.tex:278-286` (label
`thm:stationary-toppling`):

  "Let $(G,\rho,\sigma)$ be a stationary random rooted network with
   $\E[|\sigma(\rho)|/\deg(\rho)]<\infty$.  Under parallel toppling, for each
   $k\geq0$:
   (a) The random rooted network $(G,\rho,\sigma_k,u_k)$ is stationary.
   (b) The degree-weighted mass is conserved:
   $\E[\sigma_k(\rho)/\deg(\rho)]=\E[\sigma(\rho)/\deg(\rho)]$."

The network `(G,ρ,σ_k,u_k)` is `netTopple N k`, whose two marks are the
configuration and the odometer after `k` rounds; part (a) is the stationarity of
its law, the image of `P` under that map.  Integrability of the degree-weighted
mass is the hypothesis, and part (b) asserts in particular that the toppled mass
is integrable, since the two integrals are equal and the second is finite.
-/
import RWRS.Support.Toppling

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.stationaryToppling (P : Measure (RWRS.Net 1)) (hP : IsProbabilityMeasure P)
    (hgood : ∀ᵐ N ∂P, RWRS.NetGood N) (hstat : RWRS.IsStationaryNet P)
    (hint : Integrable (fun N => |RWRS.netWeightedMass N|) P) (k : ℕ) :
    RWRS.IsStationaryNet (P.map (fun N => RWRS.netTopple N k)) ∧
      Integrable (fun N => RWRS.netWeightedMassAt N k) P ∧
      ∫ N, RWRS.netWeightedMassAt N k ∂P = ∫ N, RWRS.netWeightedMass N ∂P
-- FROZEN-STATEMENT-END
:= by
  haveI := hP
  refine ⟨RWRS.Support.isStationaryNet_map_netTopple P hstat k, ?_, ?_⟩
  · exact (RWRS.Support.massConservation P hgood hstat hint k).1
  · exact (RWRS.Support.massConservation P hgood hstat hint k).2
