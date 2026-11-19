import RWRS.Support.ErgBall

/-!
# Finite rooted ball codes

A finite adjacency matrix and a distinguished vertex describe a rooted finite
graph. The event that such a graph describes a rooted network ball is measurable.
-/

namespace RWRS.Support

open MeasureTheory

/-- A finite graph presented by its adjacency matrix and a distinguished vertex. -/
abbrev RootedFiniteGraph := Σ n : ℕ, Fin n × (Fin n → Fin n → Bool)

/-- A rooted network ball has the finite rooted graph described by `c`. -/
def NetBallMatches {m : ℕ} (N : Net m) (r : ℕ) (c : RootedFiniteGraph) : Prop :=
  ∃ e : Fin c.1 → ℕ, Function.Injective e ∧
    netRoot N = e c.2.1 ∧
    (∀ v : ℕ, v ∈ netBallSet N r ↔ ∃ i, e i = v) ∧
    (∀ i j, (netGraph N).Adj (e i) (e j) ↔ c.2.2 i j = true)

/-- The event that a rooted ball has a specified finite code is measurable. -/
theorem measurableSet_netBallMatches {m : ℕ} (r : ℕ) (c : RootedFiniteGraph) :
    MeasurableSet {N : Net m | NetBallMatches N r c} := by
  classical
  have heq : {N : Net m | NetBallMatches N r c} =
      ⋃ e : Fin c.1 → ℕ, {N : Net m | Function.Injective e ∧
        netRoot N = e c.2.1 ∧
        (∀ v : ℕ, v ∈ netBallSet N r ↔ ∃ i, e i = v) ∧
        (∀ i j, (netGraph N).Adj (e i) (e j) ↔ c.2.2 i j = true)} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, NetBallMatches]
  rw [heq]
  refine MeasurableSet.iUnion fun e => ?_
  by_cases hinj : Function.Injective e
  · have hr : MeasurableSet {N : Net m | netRoot N = e c.2.1} := by
      exact measurable_netRoot (measurableSet_singleton _)
    have hv : MeasurableSet {N : Net m |
        ∀ v : ℕ, v ∈ netBallSet N r ↔ ∃ i, e i = v} := by
      simp only [Set.setOf_forall]
      refine MeasurableSet.iInter fun v => ?_
      by_cases h : ∃ i, e i = v
      · simpa only [h, iff_true] using (measurableSet_mem_netBallSet (m := m) v r)
      · simpa [h, Set.compl_setOf] using (measurableSet_mem_netBallSet (m := m) v r).compl
    have ha : MeasurableSet {N : Net m |
        ∀ i j, (netGraph N).Adj (e i) (e j) ↔ c.2.2 i j = true} := by
      simp only [Set.setOf_forall]
      refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
      by_cases h : c.2.2 i j = true
      · simpa only [h, iff_true] using (measurableSet_adj (m := m) (e i) (e j))
      · simpa [h, Set.compl_setOf] using (measurableSet_adj (m := m) (e i) (e j)).compl
    simpa only [hinj, true_and, Set.setOf_and] using hr.inter (hv.inter ha)
  · simp only [hinj, false_and, Set.setOf_false]
    exact MeasurableSet.empty

/-- Every rooted network ball admits a finite rooted graph code. -/
theorem exists_netBallMatches {m : ℕ} (N : Net m) (r : ℕ) :
    ∃ c : RootedFiniteGraph, NetBallMatches N r c := by
  classical
  letI : Fintype (netBallSet N r) := (finite_netBallSet N r).fintype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (netBallSet N r)
  let f : Fin n → ℕ := fun i => (e.symm i : ℕ)
  have hroot : netRoot N ∈ netBallSet N r :=
    netBallSet_mono N (Nat.zero_le r) (show netRoot N ∈ netBallSet N 0 from rfl)
  let root : netBallSet N r := ⟨netRoot N, hroot⟩
  refine ⟨⟨n, e root, fun i j => decide ((netGraph N).Adj (f i) (f j))⟩, f, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  · exact (congrArg Subtype.val (e.symm_apply_apply root)).symm
  · intro v
    constructor
    · intro hv
      exact ⟨e ⟨v, hv⟩, congrArg Subtype.val (e.symm_apply_apply ⟨v, hv⟩)⟩
    · rintro ⟨i, rfl⟩
      exact (e.symm i).property
  · intro i j
    simp only [decide_eq_true_eq]

end RWRS.Support
