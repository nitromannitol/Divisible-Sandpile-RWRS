/-
Decorating a stationary random rooted graph with an i.i.d. field of marks.

The decoration is the map `markMap`, which copies the neighbour lists and the
root of a rooted graph and reads the marks off a field on the vertex set.  It
commutes with rerooting, so the identity of `def:stationary-graph` for the
decorated law is the same identity for the law of the graph, tested against the
mark average `markAvg`.  That average is invariant under isomorphism even
though the individual functions are not: an isomorphism moves the marks by a
permutation of the vertex set, and the i.i.d. law is invariant under such a
permutation.
-/
import RWRS.Network
import LatticeProb.Prob.ZeroOne

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

instance instIsProbabilityMeasureIidLaw {V : Type*} (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidLaw V ν) := by
  unfold iidLaw; infer_instance

/-- The rooted network obtained from a rooted graph and a field of marks. -/
def markMap (p : Net 0 × (ℕ → ℝ)) : Net 1 := (p.1.1, p.1.2.1, fun i (_ : Fin 1) => p.2 i)

theorem measurable_markMap : Measurable markMap := by
  refine Measurable.prodMk (measurable_fst.comp measurable_fst) (Measurable.prodMk
    ((measurable_fst.comp measurable_snd).comp measurable_fst) ?_)
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun _ => ?_
  exact (measurable_pi_apply i).comp measurable_snd

theorem markIid_eq_map (Q : Measure (Net 0)) (ν : Measure ℝ) :
    markIid Q ν = (Q.prod (iidLaw ℕ ν)).map markMap := rfl

theorem netGraph_markMap (p : Net 0 × (ℕ → ℝ)) : netGraph (markMap p) = netGraph p.1 := rfl

theorem netRoot_markMap (p : Net 0 × (ℕ → ℝ)) : netRoot (markMap p) = netRoot p.1 := rfl

theorem netReroot_markMap (N : Net 0) (ξ : ℕ → ℝ) (y : ℕ) :
    netReroot (markMap (N, ξ)) y = markMap (netReroot N y, ξ) := rfl

/-- The average of a function of the decorated network over the marks. -/
noncomputable def markAvg (ν : Measure ℝ) (h : Net 1 → ℝ≥0∞) (N : Net 0) : ℝ≥0∞ :=
  ∫⁻ ξ, h (markMap (N, ξ)) ∂(iidLaw ℕ ν)

theorem measurable_markAvg (ν : Measure ℝ) [IsProbabilityMeasure ν] {h : Net 1 → ℝ≥0∞}
    (hm : Measurable h) : Measurable (markAvg ν h) := by
  have : Measurable (Function.uncurry fun (N : Net 0) (ξ : ℕ → ℝ) => h (markMap (N, ξ))) := by
    exact hm.comp measurable_markMap
  exact this.lintegral_prod_right'

/-- The decorated function of an isomorphic pair differs by the permutation of
the marks, and the i.i.d. law does not see that permutation. -/
theorem markAvg_invariant (ν : Measure ℝ) [IsProbabilityMeasure ν] {h : Net 1 → ℝ≥0∞}
    (hm : Measurable h) (hinv : NetInvariant h) : NetInvariant (markAvg ν h) := by
  rintro N N' ⟨φ, hadj, hroot, -⟩
  have hiso : ∀ ξ : ℕ → ℝ,
      h (markMap (N, LatticeProb.coordShift φ ξ)) = h (markMap (N', ξ)) := by
    intro ξ
    refine hinv _ _ ⟨φ, ?_, hroot, ?_⟩
    · intro i j
      exact hadj i j
    · intro i
      rfl
  have hmp : MeasurePreserving (LatticeProb.coordShift (X := ℝ) (⇑φ))
      (iidLaw ℕ ν) (iidLaw ℕ ν) :=
    LatticeProb.measurePreserving_coordShift (fun _ : ℕ => ν) φ.injective fun _ => rfl
  calc markAvg ν h N
      = ∫⁻ ξ, h (markMap (N, ξ)) ∂(iidLaw ℕ ν) := rfl
    _ = ∫⁻ ξ, h (markMap (N, LatticeProb.coordShift (⇑φ) ξ)) ∂(iidLaw ℕ ν) :=
        (hmp.lintegral_comp (hm.comp measurable_markMap |>.comp
          ((measurable_const (a := N)).prodMk measurable_id))).symm
    _ = ∫⁻ ξ, h (markMap (N', ξ)) ∂(iidLaw ℕ ν) := by
        exact lintegral_congr fun ξ => hiso ξ
    _ = markAvg ν h N' := rfl

theorem lintegral_markIid (Q : Measure (Net 0)) [IsProbabilityMeasure Q] (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {h : Net 1 → ℝ≥0∞} (hm : Measurable h) :
    ∫⁻ M, h M ∂(markIid Q ν) = ∫⁻ N, markAvg ν h N ∂Q := by
  rw [markIid_eq_map, lintegral_map hm measurable_markMap]
  rw [lintegral_prod (fun p : Net 0 × (ℕ → ℝ) => h (markMap p))
    (hm.comp measurable_markMap).aemeasurable]
  rfl


/-! ### The rerooting average -/

/-- The right side of the identity of `def:stationary-graph`, as a function of
the network. -/
noncomputable def rerootAvg {m : ℕ} (h : Net m → ℝ≥0∞) (N : Net m) : ℝ≥0∞ :=
  (∑ y ∈ (netGraph N).neighborFinset (netRoot N), h (netReroot N y))
    / ((netGraph N).degree (netRoot N) : ℝ≥0∞)

theorem measurable_netReroot {m : ℕ} (y : ℕ) : Measurable fun N : Net m => netReroot N y :=
  measurable_fst.prodMk (measurable_const.prodMk (measurable_snd.comp measurable_snd))

theorem measurable_netRoot {m : ℕ} : Measurable fun N : Net m => netRoot N :=
  measurable_fst.comp measurable_snd

theorem measurableSet_adj {m : ℕ} (r j : ℕ) :
    MeasurableSet {N : Net m | (netGraph N).Adj r j} := by
  have h1 : MeasurableSet {N : Net m | j ∈ N.1 r} :=
    ((measurable_pi_apply r).comp measurable_fst)
      (MeasurableSet.of_discrete (s := {L : List ℕ | j ∈ L}))
  have h2 : MeasurableSet {N : Net m | r ∈ N.1 j} :=
    ((measurable_pi_apply j).comp measurable_fst)
      (MeasurableSet.of_discrete (s := {L : List ℕ | r ∈ L}))
  by_cases hrj : r = j
  · have : {N : Net m | (netGraph N).Adj r j} = ∅ := by
      ext N; simp [netGraph, hrj]
    rw [this]; exact MeasurableSet.empty
  · have : {N : Net m | (netGraph N).Adj r j} = {N : Net m | j ∈ N.1 r} ∩ {N | r ∈ N.1 j} := by
      ext N
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hrj, h.1, h.2⟩⟩
    rw [this]; exact h1.inter h2

open scoped Classical in
theorem sum_neighborFinset_eq_tsum {m : ℕ} (h : Net m → ℝ≥0∞) (N : Net m) (r : ℕ) :
    (∑ y ∈ (netGraph N).neighborFinset r, h (netReroot N y))
      = ∑' j : ℕ, if (netGraph N).Adj r j then h (netReroot N j) else 0 := by
  rw [tsum_eq_sum (s := (netGraph N).neighborFinset r) fun j hj => ?_]
  · exact (Finset.sum_congr rfl fun y hy => by
      rw [if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)]).symm
  · rw [if_neg fun hc => hj ((SimpleGraph.mem_neighborFinset _ _ _).mpr hc)]

open scoped Classical in
theorem degree_eq_tsum {m : ℕ} (N : Net m) (r : ℕ) :
    ((netGraph N).degree r : ℝ≥0∞)
      = ∑' j : ℕ, if (netGraph N).Adj r j then (1 : ℝ≥0∞) else 0 := by
  rw [tsum_eq_sum (s := (netGraph N).neighborFinset r) fun j hj => ?_]
  · rw [Finset.sum_congr rfl fun y hy => if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy),
      Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
  · rw [if_neg fun hc => hj ((SimpleGraph.mem_neighborFinset _ _ _).mpr hc)]

/-- The rerooting average as a function of the network and of the root. -/
noncomputable def rerootPair {m : ℕ} (h : Net m → ℝ≥0∞) (q : Net m × ℕ) : ℝ≥0∞ :=
  (∑ y ∈ (netGraph q.1).neighborFinset q.2, h (netReroot q.1 y))
    / ((netGraph q.1).degree q.2 : ℝ≥0∞)

set_option maxHeartbeats 1000000 in
theorem measurable_rerootAvg {m : ℕ} {h : Net m → ℝ≥0∞} (hm : Measurable h) :
    Measurable (rerootAvg h) := by
  classical
  have hnum : ∀ r : ℕ, Measurable fun N : Net m =>
      ∑ y ∈ (netGraph N).neighborFinset r, h (netReroot N y) := by
    intro r
    have : (fun N : Net m => ∑ y ∈ (netGraph N).neighborFinset r, h (netReroot N y))
        = fun N => ∑' j : ℕ, if (netGraph N).Adj r j then h (netReroot N j) else 0 :=
      funext fun N => sum_neighborFinset_eq_tsum h N r
    rw [this]
    refine Measurable.tsum fun j => ?_
    exact Measurable.ite (measurableSet_adj r j) (hm.comp (measurable_netReroot j))
      measurable_const
  have hden : ∀ r : ℕ, Measurable fun N : Net m => ((netGraph N).degree r : ℝ≥0∞) := by
    intro r
    have : (fun N : Net m => ((netGraph N).degree r : ℝ≥0∞))
        = fun N => ∑' j : ℕ, if (netGraph N).Adj r j then (1 : ℝ≥0∞) else 0 :=
      funext fun N => degree_eq_tsum N r
    rw [this]
    refine Measurable.tsum fun j => ?_
    exact Measurable.ite (measurableSet_adj r j) measurable_const measurable_const
  have hpair : Measurable (rerootPair h) :=
    measurable_from_prod_countable_left fun r => (hnum r).div (hden r)
  have hsplit : rerootAvg h = rerootPair h ∘ fun N : Net m => (N, netRoot N) := rfl
  rw [hsplit]
  exact hpair.comp (measurable_id.prodMk measurable_netRoot)

theorem isStationaryNet_iff {m : ℕ} (P : Measure (Net m)) :
    IsStationaryNet P ↔ ∀ h : Net m → ℝ≥0∞, Measurable h → NetInvariant h →
      ∫⁻ N, h N ∂P = ∫⁻ N, rerootAvg h N ∂P := Iff.rfl

/-- The mark average of the rerooting average is the rerooting average of the
mark average. -/
theorem markAvg_rerootAvg (ν : Measure ℝ) [IsProbabilityMeasure ν] {h : Net 1 → ℝ≥0∞}
    (hm : Measurable h) (N : Net 0) :
    markAvg ν (rerootAvg h) N = rerootAvg (markAvg ν h) N := by
  classical
  have hstep : ∀ ξ : ℕ → ℝ, rerootAvg h (markMap (N, ξ))
      = (∑ y ∈ (netGraph N).neighborFinset (netRoot N), h (markMap (netReroot N y, ξ)))
          / ((netGraph N).degree (netRoot N) : ℝ≥0∞) := by
    intro ξ
    rw [rerootAvg]
    rfl
  have hmeas : ∀ y : ℕ, Measurable fun ξ : ℕ → ℝ => h (markMap (netReroot N y, ξ)) := fun y =>
    (hm.comp measurable_markMap).comp
      ((measurable_const (a := netReroot N y)).prodMk measurable_id)
  rw [markAvg]
  simp only [hstep, div_eq_mul_inv]
  have hsum : AEMeasurable (fun ξ : ℕ → ℝ =>
      ∑ y ∈ (netGraph N).neighborFinset (netRoot N), h (markMap (netReroot N y, ξ)))
      (iidLaw ℕ ν) := (Finset.measurable_sum _ fun y _ => hmeas y).aemeasurable
  rw [lintegral_mul_const'' _ hsum, lintegral_finsetSum _ fun y _ => hmeas y, rerootAvg,
    div_eq_mul_inv]
  rfl

end RWRS.Support
