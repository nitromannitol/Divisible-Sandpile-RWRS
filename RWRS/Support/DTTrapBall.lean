/-
The uniform local trap condition on a bounded-degree graph.

The paper's remark after `def:trap-family` (`rwrs.tex:866`): on a graph of degree
at most `d`, the ball `B(y,R)` with `R = ceil(L d)` is a trap set for the level
`L`.  It contains its centre, it has at most `(d+1)^R` vertices, the subgraph it
induces is connected, and the walk started at the centre spends at least `R + 1`
steps in it, each of inverse-degree weight at least `1/d`.
-/
import RWRS.Support.Transience
import RWRS.Support.BallWalk
import RWRS.Support.SharpBall

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

omit [G.LocallyFinite] in
/-- **A vertex at distance `n + 1` has a neighbour at distance `n`.** -/
theorem exists_adj_edist_le (y : V) (n : ℕ) {v : V} (h1 : G.edist v y ≤ (n : ℕ∞) + 1)
    (h2 : ¬ G.edist v y ≤ (n : ℕ∞)) : ∃ z, G.Adj v z ∧ G.edist z y ≤ (n : ℕ∞) := by
  have hne : G.edist v y ≠ ⊤ := by
    intro htop
    rw [htop] at h1
    exact absurd h1 (by simp)
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  have hvy : v ≠ y := by
    intro hvy
    subst hvy
    exact h2 (by simp)
  obtain ⟨z, hadj, p', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hvy p
  refine ⟨z, hadj, ?_⟩
  refine le_trans (SimpleGraph.edist_le p') ?_
  have hlen : ((p'.length + 1 : ℕ) : ℕ∞) = G.edist v y := by
    simpa using hp
  have hle : ((p'.length + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) + 1 := by
    rw [hlen]; exact h1
  have hstep : ((p'.length : ℕ∞) + 1) ≤ (n : ℕ∞) + 1 := by
    simpa [Nat.cast_add] using hle
  exact WithTop.add_le_add_iff_right (by exact ENat.one_ne_top) |>.1 hstep

omit [G.LocallyFinite] in
/-- **The ball of radius `n + 1` is the ball of radius `n` together with its
neighbours.** -/
theorem closedBall_succ_subset (y : V) (n : ℕ) :
    RWRS.closedBall G y (n + 1)
      ⊆ RWRS.closedBall G y n ∪ ⋃ v ∈ RWRS.closedBall G y n, G.neighborSet v := by
  intro w hw
  by_cases hn : G.edist w y ≤ (n : ℕ∞)
  · exact Or.inl hn
  · have h1 : G.edist w y ≤ (n : ℕ∞) + 1 := by
      have : G.edist w y ≤ ((n + 1 : ℕ) : ℕ∞) := hw
      simpa [Nat.cast_add] using this
    obtain ⟨z, hadj, hz⟩ := exists_adj_edist_le y n h1 hn
    exact Or.inr (Set.mem_biUnion (show z ∈ RWRS.closedBall G y n from hz) hadj.symm)

/-- **The heat kernel is supported in the ball of the same radius.** -/
theorem heat_eq_zero_of_notMem_closedBall :
    ∀ (k : ℕ) (x v : V), v ∉ RWRS.closedBall G x k → RWRS.heat G k x v = 0 := by
  intro k
  induction k with
  | zero =>
      intro x v hv
      have hxv : x ≠ v := by
        intro h
        exact hv (by simp [RWRS.closedBall, ← h])
      simp only [RWRS.heat, if_neg hxv]
  | succ k ih =>
      intro x v hv
      have hz : ∀ z ∈ G.neighborFinset x, RWRS.heat G k z v = 0 := by
        intro z hzmem
        have hadj : G.Adj x z := (SimpleGraph.mem_neighborFinset _ _ _).1 hzmem
        refine ih z v fun hmem => hv ?_
        exact closedBall_mono_of_adj hadj k hmem
      show RWRS.walkOp G (fun z => RWRS.heat G k z v) x = 0
      rw [RWRS.walkOp, Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_div]

/-- **The heat kernel has total mass one on any finite set containing the ball
of its radius.** -/
theorem sum_heat_eq_one (hdeg : ∀ v : V, 0 < G.degree v) :
    ∀ (k : ℕ) (x : V) (S : Finset V), RWRS.closedBall G x k ⊆ (S : Set V) →
      ∑ v ∈ S, RWRS.heat G k x v = 1 := by
  intro k
  induction k with
  | zero =>
      intro x S hS
      have hxS : x ∈ S := by
        have : x ∈ RWRS.closedBall G x 0 := by simp [RWRS.closedBall]
        exact_mod_cast hS this
      simp only [RWRS.heat]
      rw [Finset.sum_eq_single x (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd hxS h),
        if_pos rfl]
  | succ k ih =>
      intro x S hS
      have h1 : ∀ w : V, RWRS.heat G (k + 1) x w
          = (∑ y ∈ G.neighborFinset x, RWRS.heat G k y w) / G.degree x := fun _ => rfl
      have hrw : ∑ v ∈ S, RWRS.heat G (k + 1) x v
          = (∑ y ∈ G.neighborFinset x, ∑ v ∈ S, RWRS.heat G k y v) / G.degree x := by
        rw [Finset.sum_congr rfl (fun v _ => h1 v), ← Finset.sum_div, Finset.sum_comm]
      rw [hrw]
      have hinner : ∀ y ∈ G.neighborFinset x, ∑ v ∈ S, RWRS.heat G k y v = 1 := by
        intro y hy
        have hadj : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).1 hy
        exact ih y S fun v hv => hS (closedBall_mono_of_adj hadj k hv)
      rw [Finset.sum_congr rfl hinner, Finset.sum_const,
        SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]
      have hdx : (G.degree x : ℝ) ≠ 0 := by
        have := hdeg x
        positivity
      exact div_self hdx

/-- **The heat kernel is a probability on the whole graph.** -/
theorem tsum_ofReal_heat_eq_one (hdeg : ∀ v : V, 0 < G.degree v) (k : ℕ) (x : V) :
    (∑' v : V, ENNReal.ofReal (RWRS.heat G k x v)) = 1 := by
  classical
  set S : Finset V := (finite_closedBall (G := G) x k).toFinset with hS
  have hsub : RWRS.closedBall G x k ⊆ (S : Set V) := by
    intro v hv
    simpa [hS] using hv
  have hzero : ∀ v ∉ S, ENNReal.ofReal (RWRS.heat G k x v) = 0 := by
    intro v hv
    have h0 : RWRS.heat G k x v = 0 :=
      heat_eq_zero_of_notMem_closedBall k x v (by
        intro hmem
        exact hv (by simpa [hS] using hmem))
    simp [h0]
  rw [tsum_eq_sum hzero, ← ENNReal.ofReal_sum_of_nonneg (fun v _ => heat_nonneg k x v),
    sum_heat_eq_one hdeg k x S hsub, ENNReal.ofReal_one]

/-- **The trap strength of a ball**: the walk started at the centre of a ball of
radius `R` spends at least `R + 1` steps inside it, each of inverse-degree weight
at least `1/d`. -/
theorem thetaExit_closedBall_ge (d : ℕ) (hdeg : ∀ v : V, 0 < G.degree v)
    (hd : RWRS.BoundedDegree G d) (y : V) (R : ℕ) :
    ((R + 1 : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞)
      ≤ RWRS.thetaExit G (RWRS.closedBall G y R) y := by
  classical
  set C : Set V := RWRS.closedBall G y R with hC
  have hkh : ∀ k : ℕ, k ≤ R → ∀ v : V,
      RWRS.killedHeat G C k y v = RWRS.heat G k y v := by
    intro k hk v
    refine killedHeat_eq_heat_of_ball C k y (fun w hw => ?_) v
    have h1 : G.edist w y ≤ (k : ℕ∞) := hw
    exact le_trans h1 (by exact_mod_cast hk)
  have hmass : ((R + 1 : ℕ) : ℝ≥0∞)
      ≤ ∑' v : V, ∑' k : ℕ, ENNReal.ofReal (RWRS.killedHeat G C k y v) := by
    rw [ENNReal.tsum_comm]
    refine le_trans (le_of_eq ?_)
      (ENNReal.sum_le_tsum (Finset.range (R + 1))
        (f := fun k : ℕ => ∑' v : V, ENNReal.ofReal (RWRS.killedHeat G C k y v)))
    have hone : ∀ k ∈ Finset.range (R + 1),
        (∑' v : V, ENNReal.ofReal (RWRS.killedHeat G C k y v)) = 1 := by
      intro k hk
      have hkR : k ≤ R := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      rw [tsum_congr (fun v => by rw [hkh k hkR v])]
      exact tsum_ofReal_heat_eq_one hdeg k y
    rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hterm : ∀ v : V,
      (∑' k : ℕ, ENNReal.ofReal (RWRS.killedHeat G C k y v)) / (d : ℝ≥0∞)
        ≤ RWRS.killedGreen G C y v := by
    intro v
    exact ENNReal.div_le_div_left (by exact_mod_cast hd v) _
  calc ((R + 1 : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞)
      ≤ (∑' v : V, ∑' k : ℕ, ENNReal.ofReal (RWRS.killedHeat G C k y v)) / (d : ℝ≥0∞) :=
        ENNReal.div_le_div_right hmass _
    _ = ∑' v : V, (∑' k : ℕ, ENNReal.ofReal (RWRS.killedHeat G C k y v)) / (d : ℝ≥0∞) := by
        simp only [ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
    _ ≤ ∑' v : V, RWRS.killedGreen G C y v := ENNReal.tsum_le_tsum hterm
    _ = RWRS.thetaExit G C y := rfl

/-- **A ball of radius `R` in a graph of degree at most `d` has at most
`(d+1)^R` vertices.** -/
theorem card_ballFinset_le (d : ℕ) (hd : RWRS.BoundedDegree G d) (y : V) :
    ∀ R : ℕ, (ballFinset G y R).card ≤ (d + 1) ^ R := by
  classical
  intro R
  induction R with
  | zero =>
      have hset : ballFinset G y 0 = {y} := by
        ext v
        rw [mem_ballFinset, Finset.mem_singleton]
        constructor
        · intro hv
          have h0 : G.edist v y ≤ (0 : ℕ∞) := hv
          have : G.edist v y = 0 := le_antisymm h0 bot_le
          exact (SimpleGraph.edist_eq_zero_iff).1 this
        · intro hv
          subst hv
          show G.edist v v ≤ ((0 : ℕ) : ℕ∞)
          simp
      rw [hset]
      simp
  | succ R ih =>
      have hsub : ballFinset G y (R + 1)
          ⊆ ballFinset G y R ∪ (ballFinset G y R).biUnion (fun v => G.neighborFinset v) := by
        intro w hw
        rcases closedBall_succ_subset y R (mem_ballFinset.1 hw) with h | h
        · exact Finset.mem_union_left _ (mem_ballFinset.2 h)
        · obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 h
          refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨v, mem_ballFinset.2 hv, ?_⟩)
          exact (SimpleGraph.mem_neighborFinset _ _ _).2 hwv
      have hcard1 : (ballFinset G y (R + 1)).card
          ≤ (ballFinset G y R).card
            + ((ballFinset G y R).biUnion (fun v => G.neighborFinset v)).card :=
        le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have hcard2 : ((ballFinset G y R).biUnion (fun v => G.neighborFinset v)).card
          ≤ (ballFinset G y R).card * d := by
        refine le_trans (Finset.card_biUnion_le) ?_
        calc ∑ v ∈ ballFinset G y R, (G.neighborFinset v).card
            ≤ ∑ _v ∈ ballFinset G y R, d := by
              refine Finset.sum_le_sum fun v _ => ?_
              rw [SimpleGraph.card_neighborFinset_eq_degree]
              exact hd v
          _ = (ballFinset G y R).card * d := by rw [Finset.sum_const, smul_eq_mul]
      calc (ballFinset G y (R + 1)).card
          ≤ (ballFinset G y R).card + (ballFinset G y R).card * d := by omega
        _ = (ballFinset G y R).card * (d + 1) := by ring
        _ ≤ (d + 1) ^ R * (d + 1) := Nat.mul_le_mul_right _ ih
        _ = (d + 1) ^ (R + 1) := by ring

omit [G.LocallyFinite] in
/-- **A ball induces a connected subgraph**: every vertex of the ball reaches the
centre along a geodesic, which stays in the ball. -/
theorem connected_induce_closedBall (y : V) (R : ℕ) :
    (G.induce (RWRS.closedBall G y R)).Connected := by
  have hy : y ∈ RWRS.closedBall G y R := by
    show G.edist y y ≤ ((R : ℕ) : ℕ∞)
    simp
  have key : ∀ n : ℕ, n ≤ R → ∀ (v : V) (hv : v ∈ RWRS.closedBall G y R),
      G.edist v y ≤ (n : ℕ∞) →
      (G.induce (RWRS.closedBall G y R)).Reachable ⟨v, hv⟩ ⟨y, hy⟩ := by
    intro n
    induction n with
    | zero =>
        intro _ v hv h0
        have hz : G.edist v y = 0 := le_antisymm (by simpa using h0) bot_le
        have hvy : v = y := (SimpleGraph.edist_eq_zero_iff).1 hz
        subst hvy
        exact SimpleGraph.Reachable.refl _
    | succ n ih =>
        intro hnR v hv h
        by_cases hn : G.edist v y ≤ (n : ℕ∞)
        · exact ih (by omega) v hv hn
        · have h1 : G.edist v y ≤ (n : ℕ∞) + 1 := by
            simpa [Nat.cast_add] using h
          obtain ⟨z, hadj, hz⟩ := exists_adj_edist_le y n h1 hn
          have hzb : z ∈ RWRS.closedBall G y R :=
            le_trans hz (by exact_mod_cast (by omega : n ≤ R))
          have hstep : (G.induce (RWRS.closedBall G y R)).Adj ⟨v, hv⟩ ⟨z, hzb⟩ := hadj
          exact (SimpleGraph.Adj.reachable hstep).trans (ih (by omega) z hzb hz)
  have hpre : (G.induce (RWRS.closedBall G y R)).Preconnected := by
    intro a b
    have ha := key R le_rfl a.1 a.2 a.2
    have hb := key R le_rfl b.1 b.2 b.2
    exact ha.trans hb.symm
  haveI : Nonempty ↥(RWRS.closedBall G y R) := ⟨⟨y, hy⟩⟩
  exact ⟨hpre⟩

theorem coe_ballFinset (y : V) (R : ℕ) :
    ((ballFinset G y R : Finset V) : Set V) = RWRS.closedBall G y R := by
  ext v
  simp [ballFinset]

/-- **A bounded-degree graph admits a uniform local trap condition**
(`rwrs.tex:866`): the ball of radius `R = ceil(L d)` about a vertex is a trap set
for the level `L`. -/
theorem uniformLocalTrap_of_boundedDegree (d : ℕ) (hd0 : 0 < d)
    (hd : RWRS.BoundedDegree G d) (hdeg : ∀ v : V, 0 < G.degree v) :
    RWRS.UniformLocalTrap G := by
  intro L hL
  obtain ⟨R, hR⟩ := exists_nat_ge (L * d)
  refine ⟨R, (d + 1) ^ R, fun y => ⟨ballFinset G y R, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine mem_ballFinset.2 ?_
    show G.edist y y ≤ ((R : ℕ) : ℕ∞)
    simp
  · rw [coe_ballFinset]
  · exact card_ballFinset_le d hd y R
  · rw [coe_ballFinset]
    exact connected_induce_closedBall y R
  · rw [coe_ballFinset]
    refine le_trans ?_ (thetaExit_closedBall_ge d hdeg hd y R)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hLle : L ≤ ((R : ℝ) + 1) / d := by
      rw [le_div_iff₀ hdR]
      linarith
    calc ENNReal.ofReal L ≤ ENNReal.ofReal (((R : ℝ) + 1) / d) := ENNReal.ofReal_le_ofReal hLle
      _ = ((R + 1 : ℕ) : ℝ≥0∞) / (d : ℝ≥0∞) := by
          rw [ENNReal.ofReal_div_of_pos hdR]
          congr 1
          · rw [show ((R : ℝ) + 1) = ((R + 1 : ℕ) : ℝ) by push_cast; ring,
              ENNReal.ofReal_natCast]
          · rw [ENNReal.ofReal_natCast]

end RWRS.Support
