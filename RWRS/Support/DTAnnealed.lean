import RWRS.Support.DTCappedRule
import RWRS.Support.DTPotential

/-!
# The annealed payoff identity for the capped rule

Averaged over the scenery, the walk expectation of the payoff collected by
the capped rule plus the trap potential vanishes: per scenery the payoff
identity gives the trap potential at the root, whose scenery average is
zero by centredness.
-/

namespace RWRS.Support

open MeasureTheory

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

set_option linter.unusedSectionVars false in
/-- **The annealed payoff identity for the capped rule.** -/
theorem integral_payoffCapped_add_trapPotential_eq_zero [Infinite V] (hG : G.Connected)
    (r : ℕ) (C : V → Finset V) (ℓ : ℕ) (K : Finset V) {N : ℕ} (hN : 0 < N)
    (ε : ℝ) (o : V) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (h0 : RWRS.extMean ν = 0) :
    ∫ ξ, RWRS.walkExp G N o (fun X =>
        RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
          + trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))) ∂(iidLaw V ν)
      = 0 := by
  calc ∫ ξ, RWRS.walkExp G N o (fun X =>
      RWRS.payoff G ξ (trapRuleCapped G r C ℓ K N ε ξ X) X
        + trapPotential G K ξ (X (trapRuleCapped G r C ℓ K N ε ξ X))) ∂(iidLaw V ν)
    = ∫ ξ, trapPotential G K ξ o ∂(iidLaw V ν) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
        walkExp_payoff_add_trapPotential hG K hesc ξ N o
          (trapRuleCapped G r C ℓ K N ε ξ) (isStopping_trapRuleCapped r C ℓ K hN ε ξ)
          (fun X => trapRuleCapped_le r C ℓ K N ε ξ X)
          (fun X' _ k hk => mem_of_lt_trapRuleCapped r C ℓ K N ε ξ X' hk))
  _ = 0 := integral_trapPotential (inferInstance) h0 K o

