/-
Proposition 5.8 of `rwrs.tex`, frozen.  `rwrs.tex:777-782` (label
`prop:doubly-transient-really-general`):

  "Let $G=(V,E)$ be an infinite, locally finite, connected graph.  Assume the
   simple random walk on $G$ is transient, that $\sum_{v\in V}g(o,v)^2<\infty$
   for every $o\in V$, and that $G$ admits a uniform local trap condition.  Let
   $(\xi(v))_{v\in V}$ be i.i.d. and independent of the walk with $\E[\xi]=0$,
   $\var(\xi)>0$, and $\E[\xi^2]<\infty$.  Then
   $\sup_\tau\E_o[S_\tau\mid\xi]=\infty$ almost surely for every $o\in V$, where
   the supremum is over bounded stopping times."

Transience is `g(o,o) < ∞` at every vertex, double transience is
`RWRS.DoublyTransient`, and the trap condition is `def:trap-family`.
-/
import RWRS.Setting
import RWRS.Support.DTStepOne

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.doublyTransient [Infinite V] (hG : G.Connected)
    (htrans : ∀ o : V, RWRS.green G o o ≠ ⊤) (hdt : RWRS.DoublyTransient G)
    (htrap : RWRS.UniformLocalTrap G)
    (ν : Measure ℝ) (hν : IsProbabilityMeasure ν) (hmean : RWRS.extMean ν = 0)
    (hvar : 0 < RWRS.evar ν) (hsq : RWRS.evar ν < ⊤) :
    ∀ o : V, ∀ᵐ ξ ∂(RWRS.iidLaw V ν), RWRS.supStopValue G ξ o = ⊤
-- FROZEN-STATEMENT-END
:= by
  classical
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  haveI : Countable V := RWRS.Support.countable_of_connected hG
  haveI := hν
  intro o
  exact RWRS.Support.ae_supStopValue_top_of_lintegral_top hG hν hmean hsq o (hdt o)
    (RWRS.Support.lintegral_supStopValue_eq_top hG hdt htrap ν hmean hvar hsq o)
