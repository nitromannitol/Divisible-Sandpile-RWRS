/-
The balls of a rooted network, built one neighbour shell at a time.

The proof of `lem:ergodic-marked-stationary` approximates an invariant event by
a function of the marked ball of radius `r` around the root, so the ball must be
a measurable function of the network.  Reading it off the graph distance makes
that awkward; building it by adding one shell of neighbours at a time makes it
an explicit countable union of adjacency events, hence measurable by induction
on the radius.  The two facts the proof needs are that the shells exhaust a
connected graph and that two shells of radius `r` around vertices at distance
more than `2r` are disjoint.
-/
import RWRS.Support.Marking
import RWRS.Support.BallWalk

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

/-- The ball of radius `r` around the root, built shell by shell. -/
def netBallSet {m : ℕ} (N : RWRS.Net m) : ℕ → Set ℕ
  | 0 => {RWRS.netRoot N}
  | r + 1 => netBallSet N r ∪ {i | ∃ w ∈ netBallSet N r, (RWRS.netGraph N).Adj w i}

/-- Membership in the radius-`0` ball is equality with the root, unfolding the
base case of `netBallSet`. -/
theorem mem_netBallSet_zero {m : ℕ} (N : RWRS.Net m) (i : ℕ) :
    i ∈ netBallSet N 0 ↔ i = RWRS.netRoot N := Iff.rfl

/-- Membership in the radius-`(r + 1)` ball unfolds to membership in the
radius-`r` ball together with the new neighbour shell. -/
theorem mem_netBallSet_succ {m : ℕ} (N : RWRS.Net m) (r i : ℕ) :
    i ∈ netBallSet N (r + 1)
      ↔ i ∈ netBallSet N r ∨ ∃ w, w ∈ netBallSet N r ∧ (RWRS.netGraph N).Adj w i := Iff.rfl

/-- `netBallSet` after rerooting at `v` is definitionally the ball of the
network with only its root component replaced by `v`. -/
theorem netBallSet_reroot {m : ℕ} (N : RWRS.Net m) (v r : ℕ) :
    netBallSet (RWRS.netReroot N v) r = netBallSet ((N.1, v, N.2.2) : RWRS.Net m) r := rfl

/-- The balls `netBallSet N r` are monotone in `r`, by induction on the
larger radius. -/
theorem netBallSet_mono {m : ℕ} (N : RWRS.Net m) {r s : ℕ} (h : r ≤ s) :
    netBallSet N r ⊆ netBallSet N s := by
  induction s with
  | zero => simp [Nat.le_zero.1 h]
  | succ s ih =>
      rcases Nat.lt_or_ge r (s + 1) with hlt | hge
      · exact fun x hx => Or.inl (ih (Nat.lt_succ_iff.1 hlt) hx)
      · have : r = s + 1 := le_antisymm h hge
        subst this; exact subset_rfl

/-- `netBallSet N r` is contained in the graph-distance closed ball of the
same radius, by induction on `r` using the triangle inequality for `edist`
at each new shell. -/
theorem netBallSet_subset_closedBall {m : ℕ} (N : RWRS.Net m) (r : ℕ) :
    netBallSet N r ⊆ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) r := by
  induction r with
  | zero =>
      intro i hi
      have hir : i = RWRS.netRoot N := hi
      subst hir
      simp only [RWRS.closedBall, Set.mem_setOf_eq, Nat.cast_zero, SimpleGraph.edist_self,
        le_refl]
  | succ r ih =>
      intro i hi
      rcases hi with h | ⟨w, hw, hadj⟩
      · have h2 : (RWRS.netGraph N).edist i (RWRS.netRoot N) ≤ (r : ℕ∞) := ih h
        simp only [RWRS.closedBall, Set.mem_setOf_eq]
        refine le_trans h2 ?_
        exact_mod_cast Nat.le_succ r
      · have hwr : (RWRS.netGraph N).edist w (RWRS.netRoot N) ≤ (r : ℕ∞) := ih hw
        have h1 : (RWRS.netGraph N).edist i w = 1 :=
          SimpleGraph.edist_eq_one_iff_adj.2 hadj.symm
        have htri := SimpleGraph.edist_triangle (G := RWRS.netGraph N) (u := i) (v := w)
          (w := RWRS.netRoot N)
        simp only [RWRS.closedBall, Set.mem_setOf_eq]
        rw [h1] at htri
        refine le_trans htri ?_
        calc (1 : ℕ∞) + (RWRS.netGraph N).edist w (RWRS.netRoot N) ≤ 1 + (r : ℕ∞) := by gcongr
          _ = ((r + 1 : ℕ) : ℕ∞) := by push_cast; ring

/-- Membership of a fixed vertex `i` in `netBallSet N r` is a measurable
condition on `N`, by induction on `r` using measurability of the root map
and of adjacency. -/
theorem measurableSet_mem_netBallSet {m : ℕ} (i r : ℕ) :
    MeasurableSet {N : RWRS.Net m | i ∈ netBallSet N r} := by
  induction r generalizing i with
  | zero =>
      have hset : {N : RWRS.Net m | i ∈ netBallSet N 0}
          = (fun N : RWRS.Net m => RWRS.netRoot N) ⁻¹' {i} := by
        ext N
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun hN => hN.symm, fun hN => hN.symm⟩
      rw [hset]
      exact measurable_netRoot (measurableSet_singleton i)
  | succ r ih =>
      have hset : {N : RWRS.Net m | i ∈ netBallSet N (r + 1)}
          = {N : RWRS.Net m | i ∈ netBallSet N r}
            ∪ ⋃ w : ℕ, ({N : RWRS.Net m | w ∈ netBallSet N r}
                ∩ {N : RWRS.Net m | (RWRS.netGraph N).Adj w i}) := by
        ext N
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
        exact ⟨fun hN => hN.imp id (fun ⟨w, hw, hadj⟩ => ⟨w, hw, hadj⟩),
          fun hN => hN.imp id (fun ⟨w, hw, hadj⟩ => ⟨w, hw, hadj⟩)⟩
      rw [hset]
      refine (ih i).union (MeasurableSet.iUnion fun w => (ih w).inter ?_)
      exact measurableSet_adj w i

/-- Every vertex `i` joined to the root by a walk `p` lies in the ball
`netBallSet N p.length`, by induction on the walk. -/
theorem mem_netBallSet_of_walk {m : ℕ} (N : RWRS.Net m) :
    ∀ {i j : ℕ} (p : (RWRS.netGraph N).Walk i j), j = RWRS.netRoot N →
      i ∈ netBallSet N p.length := by
  intro i j p
  induction p with
  | nil => intro h; subst h; exact rfl
  | @cons a b c hadj q ih =>
      intro h
      exact Or.inr ⟨b, ih h, hadj.symm⟩

/-- On a good (connected) network every vertex `i` eventually lies in some
`netBallSet N r`, being joined to the root by a walk. -/
theorem exists_mem_netBallSet {m : ℕ} {N : RWRS.Net m} (hN : RWRS.NetGood N) (i : ℕ) :
    ∃ r : ℕ, i ∈ netBallSet N r := by
  obtain ⟨p⟩ := hN.preconnected i (RWRS.netRoot N)
  exact ⟨p.length, mem_netBallSet_of_walk N p rfl⟩

/-- Rerooting a network at `v` makes `v` the new root. -/
theorem netRoot_reroot {m : ℕ} (N : RWRS.Net m) (v : ℕ) :
    RWRS.netRoot (RWRS.netReroot N v) = v := rfl

/-- Rerooting a network leaves its underlying graph unchanged. -/
theorem netGraph_reroot {m : ℕ} (N : RWRS.Net m) (v : ℕ) :
    RWRS.netGraph (RWRS.netReroot N v) = RWRS.netGraph N := rfl

/-- If the radius-`r` balls around the root and around a rerooted vertex `v`
are not disjoint, `v` lies in the closed ball of radius `2r` about the root,
by the triangle inequality through a common point of the two balls. -/
theorem mem_closedBall_of_not_disjoint {m : ℕ} (N : RWRS.Net m) (v r : ℕ)
    (h : ¬ Disjoint (netBallSet N r) (netBallSet (RWRS.netReroot N v) r)) :
    v ∈ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) (2 * r) := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨i, hi1, hi2⟩ := h
  have h1 : (RWRS.netGraph N).edist i (RWRS.netRoot N) ≤ (r : ℕ∞) :=
    netBallSet_subset_closedBall N r hi1
  have h2 : (RWRS.netGraph N).edist i v ≤ (r : ℕ∞) := by
    have := netBallSet_subset_closedBall (RWRS.netReroot N v) r hi2
    simpa [RWRS.closedBall, netGraph_reroot, netRoot_reroot] using this
  have htri := SimpleGraph.edist_triangle (G := RWRS.netGraph N) (u := v) (v := i)
    (w := RWRS.netRoot N)
  have h2' : (RWRS.netGraph N).edist v i ≤ (r : ℕ∞) := by
    rwa [SimpleGraph.edist_comm] at h2
  simp only [RWRS.closedBall, Set.mem_setOf_eq]
  refine le_trans htri ?_
  calc (RWRS.netGraph N).edist v i + (RWRS.netGraph N).edist i (RWRS.netRoot N)
      ≤ (r : ℕ∞) + (r : ℕ∞) := by gcongr
    _ = ((2 * r : ℕ) : ℕ∞) := by push_cast; ring

/-- **`netBallSet` agrees with the graph-distance closed ball.**  One inclusion
is `netBallSet_subset_closedBall`; the other realizes the distance by a
shortest walk and applies `mem_netBallSet_of_walk`. -/
theorem netBallSet_eq_closedBall {m : ℕ} (N : RWRS.Net m) (r : ℕ) :
    netBallSet N r = RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) r := by
  refine Set.Subset.antisymm (netBallSet_subset_closedBall N r) ?_
  intro i hi
  have hle : (RWRS.netGraph N).edist i (RWRS.netRoot N) ≤ (r : ℕ∞) := hi
  have hne : (RWRS.netGraph N).edist i (RWRS.netRoot N) ≠ ⊤ := by
    intro hc
    rw [hc] at hle
    exact absurd hle (by simp)
  obtain ⟨p, hp⟩ := (SimpleGraph.reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
  have hlen : (p.length : ℕ∞) ≤ (r : ℕ∞) := by rw [hp]; exact hle
  have hlen' : p.length ≤ r := by exact_mod_cast hlen
  exact netBallSet_mono N hlen' (mem_netBallSet_of_walk N p rfl)

/-- Each `netBallSet N r` is finite, via its identification with the closed
ball and `finite_closedBall`. -/
theorem finite_netBallSet {m : ℕ} (N : RWRS.Net m) (r : ℕ) : (netBallSet N r).Finite := by
  rw [netBallSet_eq_closedBall]
  exact finite_closedBall (RWRS.netRoot N) r


/-! ### The ball completed by the vertices the root cannot reach -/

/-- The ball of radius `r` around the root, completed at every positive radius
by the vertices no path from the root reaches.  On a connected network there are
no such vertices and this is the ball itself; on every network the completed
balls exhaust the vertex set, which is what makes the events they carry generate
the product σ-algebra.  Adding the unreachable vertices all at once keeps the
construction invariant under isomorphism. -/
def netBallX {m : ℕ} (N : RWRS.Net m) (r : ℕ) : Set ℕ :=
  netBallSet N r ∪ {i | r ≠ 0 ∧ ∀ s : ℕ, i ∉ netBallSet N s}

/-- The plain ball `netBallSet N r` is contained in its completion
`netBallX N r`. -/
theorem netBallSet_subset_netBallX {m : ℕ} (N : RWRS.Net m) (r : ℕ) :
    netBallSet N r ⊆ netBallX N r := Set.subset_union_left

/-- `netBallX` is monotone in `r`, combining monotonicity of `netBallSet` with
the fact that the completion condition `r ≠ 0` persists as `r` grows. -/
theorem netBallX_mono {m : ℕ} (N : RWRS.Net m) {r s : ℕ} (h : r ≤ s) :
    netBallX N r ⊆ netBallX N s := by
  rintro i (hi | ⟨hr, hi⟩)
  · exact Or.inl (netBallSet_mono N h hi)
  · exact Or.inr ⟨by omega, hi⟩

/-- Every vertex lies in some `netBallX N r`: either it already lies in some
`netBallSet`, or otherwise it qualifies for the radius-`1` completion. -/
theorem exists_mem_netBallX {m : ℕ} (N : RWRS.Net m) (i : ℕ) : ∃ r : ℕ, i ∈ netBallX N r := by
  by_cases h : ∃ s : ℕ, i ∈ netBallSet N s
  · obtain ⟨s, hs⟩ := h
    exact ⟨s, Or.inl hs⟩
  · push Not at h
    exact ⟨1, Or.inr ⟨one_ne_zero, h⟩⟩

/-- Membership of a fixed vertex `i` in `netBallX N r` is a measurable
condition on `N`, combining measurability of `netBallSet` membership with
measurability of the completion condition as a countable intersection. -/
theorem measurableSet_mem_netBallX {m : ℕ} (i r : ℕ) :
    MeasurableSet {N : RWRS.Net m | i ∈ netBallX N r} := by
  have hset : {N : RWRS.Net m | i ∈ netBallX N r}
      = {N : RWRS.Net m | i ∈ netBallSet N r}
        ∪ (⋂ s : ℕ, {N : RWRS.Net m | i ∈ netBallSet N s}ᶜ) ∩ {_N : RWRS.Net m | r ≠ 0} := by
    ext N
    by_cases hr : r = 0
    · simp [netBallX, hr]
    · simp [netBallX, hr, Set.mem_iInter]
  rw [hset]
  refine (measurableSet_mem_netBallSet i r).union ?_
  by_cases hr : r = 0
  · simp [hr]
  · have : {_N : RWRS.Net m | r ≠ 0} = (Set.univ : Set (RWRS.Net m)) := by
      ext N; simp [hr]
    rw [this, Set.inter_univ]
    exact MeasurableSet.iInter fun s => (measurableSet_mem_netBallSet i s).compl

/-- On a good (connected) network `netBallX` reduces to the plain ball
`netBallSet`, since `exists_mem_netBallSet` rules out any unreached vertex. -/
theorem netBallX_eq_of_good {m : ℕ} {N : RWRS.Net m} (hN : RWRS.NetGood N) (r : ℕ) :
    netBallX N r = netBallSet N r := by
  refine Set.union_eq_self_of_subset_right ?_
  rintro i ⟨-, hi⟩
  obtain ⟨s, hs⟩ := exists_mem_netBallSet hN i
  exact absurd hs (hi s)

/-- The non-disjointness criterion `mem_closedBall_of_not_disjoint`, restated
for the completed balls `netBallX` on good networks, where `netBallX_eq_of_good`
identifies them with `netBallSet`. -/
theorem mem_closedBall_of_not_disjoint_netBallX {m : ℕ} {N : RWRS.Net m} (hN : RWRS.NetGood N)
    (v r : ℕ) (h : ¬ Disjoint (netBallX N r) (netBallX (RWRS.netReroot N v) r)) :
    v ∈ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) (2 * r) := by
  refine mem_closedBall_of_not_disjoint N v r ?_
  rwa [netBallX_eq_of_good hN r, netBallX_eq_of_good (show RWRS.NetGood (RWRS.netReroot N v) from hN) r] at h

end RWRS.Support
