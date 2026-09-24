/-
The subcritical half of `thm:stationary-phase`: what non-stabilization forces.

If the odometer is infinite at a vertex it is infinite at every neighbour, so on
a connected graph it is infinite everywhere (`rwrs.tex:363`): were it finite at a
neighbour `w`, the mass at `w` after `n` rounds would be at least
`σ(w) + u_n(v) - deg(w) u_n(w)`, which grows without bound, so `w` would emit at
least one per round from some time on and its own odometer would diverge.  A
vertex with an infinite odometer reaches mass one, and the toppling update never
lets the mass drop below one again, which is `liminf_k σ_k(ρ) ≥ 1`
(`rwrs.tex:364`).
-/
import RWRS.Support.Odometer

namespace RWRS.Support


variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem one_le_config_of_le {σ : V → ℝ} {v : V} {j k : ℕ} (hjk : j ≤ k)
    (hj : 1 ≤ RWRS.config G σ j v) : 1 ≤ RWRS.config G σ k v := by
  induction k with
  | zero =>
    have hz : j = 0 := Nat.le_zero.mp hjk
    subst hz
    exact hj
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · have hk : 1 ≤ RWRS.config G σ k v := ih (Nat.lt_succ_iff.mp hlt)
      rw [config_succ, RWRS.topple, min_eq_right hk]
      have hsum : 0 ≤ ∑ w ∈ G.neighborFinset v, RWRS.emission G (RWRS.config G σ k) w :=
        Finset.sum_nonneg fun w _ => emission_nonneg _ w
      linarith
    · have hz : j = k + 1 := le_antisymm hjk hge
      subst hz
      exact hj

theorem exists_one_le_config {σ : V → ℝ} {v : V}
    (hv : RWRS.odometerLimit G σ v = ⊤) : ∃ j : ℕ, 1 ≤ RWRS.config G σ j v := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ j : ℕ, RWRS.emission G (RWRS.config G σ j) v = 0 := by
    intro j
    rw [RWRS.emission, max_eq_right (by linarith [hcon j]), zero_div]
  have hodo : ∀ n : ℕ, RWRS.odometer G σ n v = 0 := by
    intro n
    exact Finset.sum_eq_zero fun j _ => hzero j
  have : RWRS.odometerLimit G σ v = 0 := by
    rw [RWRS.odometerLimit]
    simp only [hodo, ENNReal.ofReal_zero, ciSup_const]
  rw [this] at hv
  exact absurd hv (by simp)


theorem bddAbove_odometer_of_ne_top {σ : V → ℝ} {x : V}
    (hx : RWRS.odometerLimit G σ x ≠ ⊤) :
    ∃ C : ℝ, ∀ n : ℕ, RWRS.odometer G σ n x ≤ C := by
  refine ⟨(RWRS.odometerLimit G σ x).toReal, fun n => ?_⟩
  have h1 : ENNReal.ofReal (RWRS.odometer G σ n x) ≤ RWRS.odometerLimit G σ x :=
    le_iSup (fun m : ℕ => ENNReal.ofReal (RWRS.odometer G σ m x)) n
  have := ENNReal.toReal_mono hx h1
  rwa [ENNReal.toReal_ofReal (odometer_nonneg σ n x)] at this

theorem unbounded_odometer_of_eq_top {σ : V → ℝ} {x : V}
    (hx : RWRS.odometerLimit G σ x = ⊤) (T : ℝ) : ∃ n : ℕ, T ≤ RWRS.odometer G σ n x := by
  by_contra hcon
  push Not at hcon
  have hle : RWRS.odometerLimit G σ x ≤ ENNReal.ofReal T := by
    refine iSup_le fun n => ENNReal.ofReal_le_ofReal (le_of_lt (hcon n))
  rw [hx] at hle
  exact absurd (top_le_iff.mp hle) (by simp)

/-- An infinite odometer propagates to every neighbour. -/
theorem odometerLimit_eq_top_of_adj [Infinite V] (hG : G.Connected) (σ : V → ℝ) {v w : V}
    (hadj : G.Adj v w) (hv : RWRS.odometerLimit G σ v = ⊤) :
    RWRS.odometerLimit G σ w = ⊤ := by
  by_contra hw
  obtain ⟨C, hC⟩ := bddAbove_odometer_of_ne_top hw
  set d : ℝ := (G.degree w : ℝ) with hd
  have hd0 : (0 : ℝ) < d := by
    rw [hd]; exact_mod_cast degree_pos hG w
  -- the mass at `w` is at least the odometer at the neighbour `v`, up to the bound at `w`
  have hkey : ∀ n : ℕ,
      σ w + RWRS.odometer G σ n v - d * RWRS.odometer G σ n w ≤ RWRS.config G σ n w := by
    intro n
    have hsum : RWRS.odometer G σ n v
        ≤ ∑ y ∈ G.neighborFinset w, RWRS.odometer G σ n y :=
      Finset.single_le_sum (f := fun y => RWRS.odometer G σ n y)
        (fun y _ => odometer_nonneg σ n y)
        (SimpleGraph.mem_neighborFinset G w v |>.mpr hadj.symm)
    have hlap : RWRS.laplacian G (RWRS.odometer G σ n) w
        = (∑ y ∈ G.neighborFinset w, RWRS.odometer G σ n y) - d * RWRS.odometer G σ n w := by
      simp only [RWRS.laplacian, Finset.sum_sub_distrib, Finset.sum_const,
        SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, hd]
    rw [config_eq hG σ n w, hlap]
    linarith
  obtain ⟨n, hn⟩ := unbounded_odometer_of_eq_top hv (1 + d * C + d - σ w)
  -- from `n` on, the root emits at least one per round
  have hstep : ∀ m : ℕ, n ≤ m → RWRS.odometer G σ m w + 1 ≤ RWRS.odometer G σ (m + 1) w := by
    intro m hm
    have hmv : RWRS.odometer G σ n v ≤ RWRS.odometer G σ m v := odometer_le_of_le σ hm v
    have hbig : 1 + d ≤ RWRS.config G σ m w := by
      have := hkey m
      have hCm := hC m
      nlinarith
    have hem : (1 : ℝ) ≤ RWRS.emission G (RWRS.config G σ m) w := by
      rw [RWRS.emission, ← hd, le_div_iff₀ hd0, one_mul]
      exact le_max_of_le_left (by linarith)
    rw [odometer_succ]
    linarith
  have hgrow : ∀ k : ℕ, RWRS.odometer G σ n w + (k : ℝ) ≤ RWRS.odometer G σ (n + k) w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hstep (n + k) (Nat.le_add_right n k)
      have hcast : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [← Nat.add_assoc]
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt C
  have h1 := hgrow k
  have h2 := hC (n + k)
  have h3 := odometer_nonneg (G := G) σ n w
  linarith


/-- An infinite odometer propagates along a walk. -/
theorem odometerLimit_top_of_walk [Infinite V] (hG : G.Connected) (σ : V → ℝ) {v x : V}
    (p : G.Walk v x) : RWRS.odometerLimit G σ v = ⊤ → RWRS.odometerLimit G σ x = ⊤ := by
  induction p with
  | nil => exact id
  | cons h q ih => exact fun hv => ih (odometerLimit_eq_top_of_adj hG σ h hv)

/-- On a connected graph a configuration that does not stabilize has an infinite
odometer at every vertex.  This is the first sentence of the proof of part (ii)
(`rwrs.tex:363`). -/
theorem odometerLimit_eq_top_of_not_stabilizes [Infinite V] (hG : G.Connected) (σ : V → ℝ)
    (hns : ¬ RWRS.Stabilizes G σ) (x : V) : RWRS.odometerLimit G σ x = ⊤ := by
  obtain ⟨v, hv⟩ := not_forall.mp hns
  exact odometerLimit_top_of_walk hG σ (hG.preconnected v x).some (not_not.mp hv)

/-- On a connected graph a configuration that does not stabilize has mass at
least one at every vertex from some round on.  This is
`liminf_k σ_k(ρ) ≥ 1` of `rwrs.tex:364`. -/
theorem exists_one_le_config_of_not_stabilizes [Infinite V] (hG : G.Connected) (σ : V → ℝ)
    (hns : ¬ RWRS.Stabilizes G σ) (x : V) :
    ∃ j : ℕ, ∀ k : ℕ, j ≤ k → 1 ≤ RWRS.config G σ k x := by
  obtain ⟨j, hj⟩ := exists_one_le_config (odometerLimit_eq_top_of_not_stabilizes hG σ hns x)
  exact ⟨j, fun k hk => one_le_config_of_le hk hj⟩

end RWRS.Support
