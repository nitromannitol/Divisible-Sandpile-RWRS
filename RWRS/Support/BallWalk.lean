/-
The two geometric facts the upper half of `thm:nested-vol` needs: the balls of a
locally finite graph are finite, and a walk average of length `n` sees only the
trajectories that stay in the ball of radius `k` at time `k`.
-/
import RWRS.Support.FiniteVol

namespace RWRS.Support

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **The balls of a locally finite graph are finite.** -/
theorem finite_closedBall (o : V) : ∀ r : ℕ, (RWRS.closedBall G o r).Finite := by
  intro r
  induction r with
  | zero =>
      refine (Set.finite_singleton o).subset ?_
      intro v hv
      have hv' : G.edist v o ≤ (0 : ℕ∞) := by
        simpa [RWRS.closedBall] using hv
      have : G.edist v o = 0 := le_antisymm hv' bot_le
      simpa using SimpleGraph.edist_eq_zero_iff.1 this
  | succ r ih =>
      have hcover : RWRS.closedBall G o (r + 1)
          ⊆ RWRS.closedBall G o r ∪ ⋃ w ∈ RWRS.closedBall G o r, G.neighborSet w := by
        intro v hv
        by_cases hr : v ∈ RWRS.closedBall G o r
        · exact Or.inl hr
        · right
          have hle : G.edist v o ≤ ((r + 1 : ℕ) : ℕ∞) := hv
          have hgt : ((r : ℕ) : ℕ∞) < G.edist v o := by
            have : ¬ (G.edist v o ≤ (r : ℕ∞)) := hr
            exact not_le.1 this
          have heq : G.edist v o = ((r + 1 : ℕ) : ℕ∞) := by
            refine le_antisymm hle ?_
            have : ((r : ℕ) : ℕ∞) + 1 ≤ G.edist v o := Order.add_one_le_of_lt hgt
            rwa [show ((r + 1 : ℕ) : ℕ∞) = ((r : ℕ) : ℕ∞) + 1 by push_cast; ring]
          obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_eq_coe heq
          cases p with
          | nil => simp at hp
          | @cons _ w _ hadj q =>
              have hq : q.length = r := by
                simp only [SimpleGraph.Walk.length_cons] at hp
                omega
              have hwr : w ∈ RWRS.closedBall G o r := by
                have := q.edist_le
                rw [hq] at this
                exact this
              exact Set.mem_biUnion hwr hadj.symm
      refine Set.Finite.subset (Set.Finite.union ih ?_) hcover
      refine Set.Finite.biUnion ih fun w _ => ?_
      exact (G.neighborFinset w).finite_toSet.subset (by simp)

/-- **A walk average sees only the trajectories that grow by one step at a
time.**  Two functionals that agree on those trajectories have the same walk
average. -/
theorem walkExp_congr_ball : ∀ (n : ℕ) (x : V) (F F' : (ℕ → V) → ℝ),
    (∀ X : ℕ → V, (∀ k ≤ n, G.edist x (X k) ≤ (k : ℕ∞)) → F X = F' X) →
      RWRS.walkExp G n x F = RWRS.walkExp G n x F' := by
  intro n
  induction n with
  | zero =>
      intro x F F' h
      show F (fun _ => x) = F' (fun _ => x)
      refine h _ fun k hk => ?_
      simp [SimpleGraph.edist_self]
  | succ n ih =>
      intro x F F' h
      show (∑ y ∈ G.neighborFinset x, RWRS.walkExp G n y (fun X => F (RWRS.cons x X)))
            / G.degree x
          = (∑ y ∈ G.neighborFinset x, RWRS.walkExp G n y (fun X => F' (RWRS.cons x X)))
            / G.degree x
      congr 1
      refine Finset.sum_congr rfl fun y hy => ?_
      have hadj : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).1 hy
      refine ih y _ _ fun X hX => ?_
      refine h (RWRS.cons x X) fun j hj => ?_
      cases j with
      | zero => simp [SimpleGraph.edist_self]
      | succ i =>
          have hxy : G.edist x y ≤ 1 := SimpleGraph.edist_le hadj.toWalk
          have htri : G.edist x (X i) ≤ G.edist x y + G.edist y (X i) :=
            SimpleGraph.edist_triangle
          have hi : G.edist y (X i) ≤ (i : ℕ∞) := hX i (by omega)
          have : G.edist x (X i) ≤ 1 + (i : ℕ∞) := le_trans htri (add_le_add hxy hi)
          have hcast : ((i + 1 : ℕ) : ℕ∞) = 1 + (i : ℕ∞) := by push_cast; ring
          show G.edist x (X i) ≤ ((i + 1 : ℕ) : ℕ∞)
          rw [hcast]
          exact this

/-! ### The upper half of the nested-volume representation -/

section Measured

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The smaller of two stopping times is a stopping time. -/
theorem isStopping_min {τ ρ : (ℕ → V) → ℕ} (hτ : RWRS.IsStopping τ) (hρ : RWRS.IsStopping ρ) :
    RWRS.IsStopping (fun X => min (τ X) (ρ X)) := by
  intro k X Y hXY hk
  simp only at hk ⊢
  have key : ∀ s : (ℕ → V) → ℕ, RWRS.IsStopping s → k ≤ s X → k ≤ s Y := by
    intro s hs hge
    by_contra hlt
    rw [not_le] at hlt
    have : s X = s Y := hs (s Y) Y X (fun j hj => (hXY j (le_trans hj hlt.le)).symm) rfl
    omega
  have key' : ∀ s : (ℕ → V) → ℕ, RWRS.IsStopping s → k ≤ s Y → k ≤ s X := by
    intro s hs hge
    by_contra hlt
    rw [not_le] at hlt
    have : s Y = s X := hs (s X) X Y (fun j hj => hXY j (le_trans hj hlt.le)) rfl
    omega
  rcases le_total (τ X) (ρ X) with h | h
  · have hτX : τ X = k := by omega
    have hρX : k ≤ ρ X := by omega
    have hτY : τ Y = k := hτ k X Y hXY hτX
    have hρY : k ≤ ρ Y := key ρ hρ hρX
    omega
  · have hρX : ρ X = k := by omega
    have hτX : k ≤ τ X := by omega
    have hρY : ρ Y = k := hρ k X Y hXY hρX
    have hτY : k ≤ τ Y := key τ hτ hτX
    omega

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The payoff at a bounded stopping time is settled by the positions up to the
bound. -/
theorem dependsUpTo_payoff_stopping {τ : (ℕ → V) → ℕ} (hτ : RWRS.IsStopping τ) {N : ℕ}
    (hτN : ∀ X, τ X ≤ N) (ξ : V → ℝ) :
    DependsUpTo N (fun X => RWRS.payoff G ξ (τ X) X) := by
  intro X Y hXY
  have hτeq : τ X = τ Y := dependsUpTo_of_isStopping hτ hτN X Y hXY
  simp only [RWRS.payoff]
  rw [hτeq]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : k ≤ N := by
    have h1 := Finset.mem_range.1 hk
    have h2 := hτN Y
    omega
  rw [hXY k hkN]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The truncated exit time is at most the exit time. -/
theorem exitTrunc_le_exitTime (C : Set V) (N : ℕ) (X : ℕ → V) :
    ((exitTrunc C N X : ℕ) : ℕ∞) ≤ LatticeProb.Graph.exitTime C X := by
  by_cases h : X ∈ stayIn C N
  · rw [exitTrunc, if_pos h]
    rw [stayIn_eq_lt_exitTime] at h
    exact le_of_lt h
  · rw [exitTrunc_of_notMem h]
    have hfin : LatticeProb.Graph.exitTime C X ≠ ⊤ := fun hc =>
      h ((LatticeProb.Graph.exitTime_eq_top_iff C X).mp hc N)
    rw [ENat.coe_toNat hfin]

/-- The odometer at a finite horizon is the value of a rule bounded by the exit
time of the ball of that radius. -/
theorem exists_finset_odometer_le_valueExit [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (σ : V → ℝ) (o : V) (n : ℕ) :
    ∃ B : Finset V, o ∈ B ∧ (∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (B : Set V)) ∧
      RWRS.odometer G σ n o ≤ RWRS.valueExit G (RWRS.excess σ) (B : Set V) o := by
  classical
  set ξ : V → ℝ := RWRS.excess σ with hξ
  set B : Finset V := (finite_closedBall (G := G) o n).toFinset with hBdef
  have hBmem : ∀ v : V, v ∈ B ↔ G.edist v o ≤ (n : ℕ∞) := by
    intro v
    rw [hBdef, Set.Finite.mem_toFinset]
    rfl
  have hoB : o ∈ B := by rw [hBmem]; simp
  have hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (B : Set V) := by
    intro x
    obtain ⟨q, hq⟩ : ∃ q : V, q ∉ B := by
      by_contra hcon
      have hsub : (Set.univ : Set V) ⊆ (B : Set V) := by
        intro z _
        by_contra hz
        exact hcon ⟨z, hz⟩
      exact (Set.infinite_univ (α := V)) (Set.Finite.subset B.finite_toSet hsub)
    obtain ⟨p⟩ := hG.preconnected x q
    exact ⟨q, p, by simpa using hq⟩
  obtain ⟨τ, hτ, hτn, hodo⟩ := (odometer_isLUB hG σ n o).2
  set τ' : (ℕ → V) → ℕ := fun X => min (τ X) (exitTrunc (B : Set V) n X) with hτ'def
  have hτ'stop : RWRS.IsStopping τ' :=
    isStopping_min hτ (isStopping_exitTrunc (B : Set V) n)
  have hτ'n : ∀ X, τ' X ≤ n := fun X => le_trans (min_le_left _ _) (hτn X)
  have hτ'le : ∀ X, (τ' X : ℕ∞) ≤ LatticeProb.Graph.exitTime (B : Set V) X := by
    intro X
    refine le_trans ?_ (exitTrunc_le_exitTime (B : Set V) n X)
    exact_mod_cast min_le_right (τ X) (exitTrunc (B : Set V) n X)
  have hcongr : RWRS.walkExp G n o (fun X => RWRS.payoff G ξ (τ X) X)
      = RWRS.walkExp G n o (fun X => RWRS.payoff G ξ (τ' X) X) := by
    refine walkExp_congr_ball n o _ _ fun X hX => ?_
    have hstay : X ∈ stayIn (B : Set V) n := by
      intro j hj
      have h1 : G.edist o (X j) ≤ (j : ℕ∞) := hX j hj
      have h2 : G.edist (X j) o ≤ (n : ℕ∞) := by
        rw [SimpleGraph.edist_comm]
        exact le_trans h1 (by exact_mod_cast hj)
      have : X j ∈ B := (hBmem (X j)).2 h2
      exact_mod_cast this
    have htr : exitTrunc (B : Set V) n X = n := by rw [exitTrunc, if_pos hstay]
    have : τ' X = τ X := by
      simp only [hτ'def, htr]
      exact min_eq_left (hτn X)
    rw [this]
  have hdep : DependsUpTo n (fun X => RWRS.payoff G ξ (τ' X) X) :=
    dependsUpTo_payoff_stopping hτ'stop hτ'n ξ
  have hbound : ∀ X : ℕ → V,
      |RWRS.payoff G ξ (τ' X) X| ≤ (n : ℝ) * stepBound G ξ B := by
    intro X
    have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := B) (n := τ' X) (X := X)
      (fun k hk => mem_of_lt_exitTrunc B n X (lt_of_lt_of_le hk (min_le_right _ _)))
    have h2 : ((τ' X : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hτ'n X
    have h3 : (0 : ℝ) ≤ stepBound G ξ B := stepBound_nonneg ξ B
    nlinarith
  have hint : RWRS.walkExp G n o (fun X => RWRS.payoff G ξ (τ' X) X)
      = ∫ X, RWRS.payoff G ξ (τ' X) X ∂(RWRS.walkLaw G o) := by
    rw [walkExp_eq_lib n o, walkLaw_eq_lib o]
    exact LatticeProb.Graph.walkExp_eq_integral hdeg n o _
      (measurable_of_dependsUpTo hdep) ((n : ℝ) * stepBound G ξ B)
      (fun X => by rw [Real.norm_eq_abs]; exact hbound X) hdep
  have hval : RWRS.odometer G σ n o ≤ RWRS.valueExit G ξ (B : Set V) o := by
    rw [hodo, hcongr, hint]
    exact le_csSup (bddAbove_stopValuesExit hdeg ξ B hesc o) ⟨τ', hτ'stop, hτ'le, rfl⟩
  exact ⟨B, hoB, hesc, hval⟩

/-- **The upper half of `thm:nested-vol`.**  The odometer at a finite horizon is
the value of a rule bounded by the exit time of the ball of that radius, and
`prop:finite-vol` reads that value off the connected subsets of the ball. -/
theorem ofReal_odometer_le_iSup [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (σ : V → ℝ) (o : V) (n : ℕ) :
    ENNReal.ofReal (RWRS.odometer G σ n o)
      ≤ ⨆ (C : Finset V) (_ : (G.induce (C : Set V)).Connected) (_ : o ∈ C),
          ENNReal.ofReal (∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * (σ v - 1)) := by
  classical
  obtain ⟨B, hoB, hesc, hval⟩ := exists_finset_odometer_le_valueExit hG hdeg σ o n
  rcases valueExit_mem_insert_zero hG hdeg (RWRS.excess σ) B hesc hoB with
    h | ⟨C, hCB, hCconn, hoC, hCsum⟩
  · rw [h] at hval
    have hz : ENNReal.ofReal (RWRS.odometer G σ n o) = 0 := by
      rw [ENNReal.ofReal_eq_zero]
      exact hval
    rw [hz]
    exact bot_le
  · refine le_trans (ENNReal.ofReal_le_ofReal hval) ?_
    rw [hCsum]
    exact le_iSup_of_le C (le_iSup_of_le hCconn (le_iSup_of_le hoC le_rfl))

end Measured

/-- The upper half of `thm:nested-vol`, with no measurable structure assumed. -/
theorem ofReal_odometer_le_iSup' [Infinite V] (hG : G.Connected) (σ : V → ℝ) (o : V) (n : ℕ) :
    ENNReal.ofReal (RWRS.odometer G σ n o)
      ≤ ⨆ (C : Finset V) (_ : (G.induce (C : Set V)).Connected) (_ : o ∈ C),
          ENNReal.ofReal (∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * (σ v - 1)) := by
  classical
  letI : MeasurableSpace V := ⊤
  haveI : MeasurableSingletonClass V := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  haveI : Countable V := countable_of_connected hG
  haveI : DecidableEq V := Classical.decEq V
  have hdeg : ∀ v : V, 0 < G.degree v := by
    intro v
    rw [SimpleGraph.degree_pos_iff_exists_adj]
    obtain ⟨u, hu⟩ := exists_ne v
    obtain ⟨p⟩ := hG.preconnected v u
    rcases p with _ | ⟨hadj, q⟩
    · exact absurd rfl hu
    · exact ⟨_, hadj⟩
  exact ofReal_odometer_le_iSup hG hdeg σ o n

end RWRS.Support
