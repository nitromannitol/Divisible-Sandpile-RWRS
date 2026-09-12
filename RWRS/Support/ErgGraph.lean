/-
The rooted graph underlying a rooted network, and the σ-algebra of its
rerooting-invariant events read on the network.

The paper conditions on two different σ-algebras.  Ergodicity of a rooted
NETWORK is triviality of `invariantSigma m`, whose events may read the marks
(`rwrs.tex:252`).  The conditioning of `lem:01-stationary` and of the proof of
`thm:stationary-phase` is on the `I_G` of `rwrs.tex:244`, an σ-algebra of events
of the rooted GRAPH: the paper uses `I_G ⊆ σ(G,ρ)` to keep the marks i.i.d.
under the conditional law (`rwrs.tex:337`) and graph measurability of the
conditioning event to keep the mark law unchanged (`rwrs.tex:347`).  That is
`graphInvariantSigma m`, the pullback of `invariantSigma 0` along
`forgetMarks`.  This file has its basic API: forgetting the marks is measurable
and commutes with rerooting and with isomorphism, the pullback is a sub-σ-algebra
of `invariantSigma m`, and the law of the rooted graph underlying an i.i.d.
marked network is the law of the rooted graph.
-/
import RWRS.Support.Marking

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- Forgetting the marks is measurable. -/
theorem measurable_forgetMarks {m : ℕ} :
    Measurable (RWRS.forgetMarks : RWRS.Net m → RWRS.Net 0) :=
  measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk measurable_const)

/-- Forgetting the marks keeps the graph. -/
theorem netGraph_forgetMarks {m : ℕ} (N : RWRS.Net m) :
    RWRS.netGraph (RWRS.forgetMarks N) = RWRS.netGraph N := rfl

/-- Forgetting the marks keeps the root. -/
theorem netRoot_forgetMarks {m : ℕ} (N : RWRS.Net m) :
    RWRS.netRoot (RWRS.forgetMarks N) = RWRS.netRoot N := rfl

/-- Forgetting the marks commutes with rerooting. -/
theorem forgetMarks_netReroot {m : ℕ} (N : RWRS.Net m) (y : ℕ) :
    RWRS.forgetMarks (RWRS.netReroot N y) = RWRS.netReroot (RWRS.forgetMarks N) y := rfl

/-- An isomorphism of rooted networks is an isomorphism of the rooted graphs
underlying them. -/
theorem netIso_forgetMarks {m : ℕ} {N N' : RWRS.Net m} (h : RWRS.NetIso N N') :
    RWRS.NetIso (RWRS.forgetMarks N) (RWRS.forgetMarks N') := by
  obtain ⟨φ, hadj, hroot, -⟩ := h
  exact ⟨φ, hadj, hroot, fun i => rfl⟩

/-- Every rerooting-invariant event is measurable. -/
theorem invariantSigma_le {m : ℕ} :
    RWRS.invariantSigma m ≤ (inferInstance : MeasurableSpace (RWRS.Net m)) :=
  fun _ hA => hA.1

/-- Decorating a rooted graph and then forgetting the marks returns the rooted
graph. -/
theorem forgetMarks_markMap (p : RWRS.Net 0 × (ℕ → ℝ)) :
    RWRS.forgetMarks (markMap p) = p.1 := by
  obtain ⟨⟨a, r, s⟩, ξ⟩ := p
  show ((a, r, fun (_ : ℕ) (j : Fin 0) => Fin.elim0 j) : RWRS.Net 0) = (a, r, s)
  exact congrArg (fun t => ((a, r, t) : RWRS.Net 0)) (funext fun _ => funext fun j => j.elim0)

end RWRS.Support
