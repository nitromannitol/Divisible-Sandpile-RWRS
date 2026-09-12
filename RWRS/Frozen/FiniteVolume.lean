/-
Proposition 3.3 of `rwrs.tex`, frozen.  `rwrs.tex:429-444` (label
`prop:finite-vol`):

  "Let $K\subseteq V$ be finite, connected, and proper, with $o\in K$.  Then
   $v_K(x)<\infty$ for every $x\in V$.  Let $D_K\coloneqq\{x\in K:v_K(x)>0\}$
   and let $D_K(o)$ denote the connected component of~$o$ in~$D_K$ (with
   $D_K(o)\coloneqq\varnothing$ if $o\notin D_K$).  If $o\notin D_K$, then
   $v_K(o)=0$.  If $o\in D_K$, then $v_K(o)=\E_o[S_{\tau_{D_K(o)}}]$.
   In particular,
   $v_K(o)=\max\{0,\sup_{C\subseteq K, C\text{ connected}, o\in C}
     \sum_{v\in C}g_C(v)(\sigma(v)-1)\}$."

`v_K(x)<\infty` is read as the statement that the set of values of the
stopping rules bounded by `τ_K` is bounded above; that is exactly what makes
the supremum `v_K(x)` a real number rather than the junk value of an
unbounded `sSup`.  The last identity is stated as `IsLUB` for the same reason,
and the `max` with `0` is the element `0` adjoined to the family, which is the
value of the rule `C = {o}` degenerating to immediate stopping.  The sets `K`
and `C` are `Finset`s, which is the paper's finiteness; `hKproper` is
`V ∖ K ≠ ∅`.  `hG` and `[Infinite V]` are the standing assumptions of
`ssec:notation`.  `[MeasurableSingletonClass V]` records that the vertex set
carries its discrete measurable structure; the vertex set of a locally finite
connected graph is countable, and the paper's walk on path space is the law of a
sequence of vertices, which is a measure only for that structure.
-/
import RWRS.Support.FiniteVol

open MeasureTheory

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- The connectedness of `K` is not referred to: the argument uses only that `K`
-- is finite and proper, the walk leaving it almost surely from every site.
set_option linter.unusedVariables false in
-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.finiteVolume [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (hG : G.Connected)
    (σ : V → ℝ) (o : V) (K : Finset V) (hKconn : (G.induce (K : Set V)).Connected)
    (hKproper : ((K : Set V))ᶜ.Nonempty) (hoK : o ∈ K) :
    (∀ x : V, BddAbove (RWRS.stopValuesExit G (RWRS.excess σ) (K : Set V) x)) ∧
    (o ∉ RWRS.activeSet G (RWRS.excess σ) (K : Set V) →
      RWRS.valueExit G (RWRS.excess σ) (K : Set V) o = 0) ∧
    (o ∈ RWRS.activeSet G (RWRS.excess σ) (K : Set V) →
      Integrable (fun X => RWRS.payoffAtExit G (RWRS.excess σ)
          (RWRS.compIn G (RWRS.activeSet G (RWRS.excess σ) (K : Set V)) o) X)
          (RWRS.walkLaw G o) ∧
      RWRS.valueExit G (RWRS.excess σ) (K : Set V) o =
        ∫ X, RWRS.payoffAtExit G (RWRS.excess σ)
          (RWRS.compIn G (RWRS.activeSet G (RWRS.excess σ) (K : Set V)) o) X
          ∂(RWRS.walkLaw G o)) ∧
    IsLUB (insert (0 : ℝ)
        {a : ℝ | ∃ C : Finset V, C ⊆ K ∧ (G.induce (C : Set V)).Connected ∧ o ∈ C ∧
          a = ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * (σ v - 1)})
      (RWRS.valueExit G (RWRS.excess σ) (K : Set V) o)
-- FROZEN-STATEMENT-END
:= by
  classical
  haveI : Countable V := RWRS.Support.countable_of_connected hG
  have hdeg : ∀ v : V, 0 < G.degree v := by
    intro v
    rw [SimpleGraph.degree_pos_iff_exists_adj]
    obtain ⟨u, hu⟩ := exists_ne v
    obtain ⟨p⟩ := hG.preconnected v u
    rcases p with _ | ⟨hadj, q⟩
    · exact absurd rfl hu
    · exact ⟨_, hadj⟩
  have hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V) := by
    intro x
    obtain ⟨q, hq⟩ := hKproper
    obtain ⟨p⟩ := hG.preconnected x q
    exact ⟨q, p, hq⟩
  refine ⟨fun x => RWRS.Support.bddAbove_stopValuesExit hdeg _ K hesc x, ?_, ?_, ?_⟩
  · exact RWRS.Support.valueExit_eq_zero_of_not_mem_activeSet hdeg _ K hesc hoK
  · exact fun ho => RWRS.Support.valueExit_eq_integral_activeComp hG hdeg _ K hesc ho
  · exact RWRS.Support.isLUB_valueExit hG hdeg _ K hesc hoK
