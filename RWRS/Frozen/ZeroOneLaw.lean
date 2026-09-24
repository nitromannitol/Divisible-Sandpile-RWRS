/-
Proposition 4.1 of `rwrs.tex`, frozen.  `rwrs.tex:491-495` (label
`prop:01-law`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph and let
   $(\sigma(v))_{v\in V}$ be i.i.d.\ random variables.  Then
   $\P(\sigma \text{ stabilizes})\in\{0,1\}$ and
   $\P(\sup_n\E_o[S_n\mid\xi]=\infty)\in\{0,1\}$."

The i.i.d. field is the product measure `iidLaw V ν` on configurations, and
the two events are the sets of configurations named.  `sup_n E_o[S_n | ξ]` is
read in `[0,∞]`, so `= ∞` is a value and not the junk of an unbounded real
supremum; the scenery is the excess mass `ξ = σ - 1`, which is i.i.d. exactly
when `σ` is.
-/
import RWRS.Support.Swap
import LatticeProb.Prob.HewittSavage

open MeasureTheory

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.zeroOneLaw (hVF : RWRS.External.VoltageFunction G)
    [Infinite V] [MeasurableSpace V] (hG : G.Connected)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (o : V) :
    (RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 0 ∨
        RWRS.iidLaw V ν {σ : V → ℝ | RWRS.Stabilizes G σ} = 1) ∧
    (RWRS.iidLaw V ν {σ : V → ℝ | RWRS.supMeanPayoff G (RWRS.excess σ) o = ⊤} = 0 ∨
        RWRS.iidLaw V ν {σ : V → ℝ | RWRS.supMeanPayoff G (RWRS.excess σ) o = ⊤} = 1)
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI := hν
  constructor
  · exact LatticeProb.measure_zero_or_one_of_exchangeable ν
      (RWRS.Support.measurableSet_stabilizes hG)
      (fun π hπ => by
        ext σ
        simp only [Set.mem_preimage]
        exact RWRS.Support.stabilizes_perm_iff hVF hG σ π hπ)
  · exact LatticeProb.measure_zero_or_one_of_exchangeable ν
      (RWRS.Support.measurableSet_supMeanPayoff_top hG o)
      (fun π hπ => by
        ext σ
        simp only [Set.mem_preimage]
        exact RWRS.Support.supMeanPayoff_perm_iff hVF hG σ π hπ o)
