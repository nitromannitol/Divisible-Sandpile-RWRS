/-
The potential of a scenery killed outside a finite set, and the optional
stopping identity it produces.

Step 1 of `prop:doubly-transient-really-general` runs the walk to a region where
the scenery is uniformly negative and reads the payoff off the martingale
`h(X_n) + S_n`, where `h(x) = ∑_v g(x,v)ξ(v)`.  That series is a random series
and converges only almost surely; at a finite horizon nothing is lost by killing
it outside the ball the walk cannot leave, and the killed potential

    h_D(x) = ∑_{v ∈ D} ξ(v) g_D(v,x)

is a finite sum with the same Laplacian `-ξ` inside `D`.  Optional stopping for
the finite-horizon walk average then gives `E_o[S_τ] = h_D(o) - E_o[h_D(X_τ)]`
for every stopping rule bounded by a horizon whose ball is inside `D`, with no
measure theory at all: both sides are finite averages.
-/
import RWRS.Support.BallWalk
import RWRS.Support.OptionalStopping
import RWRS.Support.Swap
import RWRS.Support.Continuation
import RWRS.Support.Critical
import RWRS.Support.Convexity

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {ν : Measure ℝ}

/-- `h_D(x) = ∑_{v ∈ D} ξ(v) g_D(v,x)`, the potential of the scenery `ξ` for the
walk killed on leaving `D`. -/
noncomputable def trapPotential (G : SimpleGraph V) [G.LocallyFinite] (D : Finset V)
    (ξ : V → ℝ) (x : V) : ℝ :=
  ∑ v ∈ D, ξ v * RWRS.killedGreenReal G (D : Set V) v x

/-- **The killed potential solves the Poisson equation inside `D`.** -/
theorem laplacian_trapPotential (D : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (D : Set V))
    (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) {x : V} (hx : x ∈ D) :
    RWRS.laplacian G (trapPotential G D ξ) x = -ξ x := by
  classical
  have hx' : x ∈ (D : Set V) := Finset.mem_coe.2 hx
  have hstep : ∀ v ∈ D, ξ v * RWRS.laplacian G (RWRS.killedGreenReal G (D : Set V) v) x
      = ξ v * -(if x = v then (1 : ℝ) else 0) := by
    intro v hv
    rw [laplacian_killedGreenReal_of_escape D hesc (fun w _ => hdeg w)
      (Finset.mem_coe.2 hv) hx']
  show RWRS.laplacian G (fun w => ∑ v ∈ D, ξ v * RWRS.killedGreenReal G (D : Set V) v w) x = -ξ x
  rw [laplacian_finsetSum, Finset.sum_congr rfl hstep]
  simp [Finset.sum_ite_eq, hx]

/-- **Optional stopping at a bounded rule.**  A rule bounded by `n` reads the
walk only inside the ball of radius `n`, so the payoff of `ξ` and the payoff of
`-Δ h_D` agree along every trajectory the average sees. -/
theorem walkExp_payoff_add_trapPotential [Infinite V] (hG : G.Connected) (D : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (D : Set V))
    (ξ : V → ℝ) (n : ℕ) (o : V)
    (τ : (ℕ → V) → ℕ) (hτ : RWRS.IsStopping τ) (hle : ∀ X, τ X ≤ n)
    (hin : ∀ X : ℕ → V, (∀ k ≤ n, G.edist o (X k) ≤ (k : ℕ∞)) →
      ∀ k, k < τ X → X k ∈ D) :
    RWRS.walkExp G n o (fun X => RWRS.payoff G ξ (τ X) X + trapPotential G D ξ (X (τ X)))
      = trapPotential G D ξ o := by
  have hopt := walkExp_optional hG (trapPotential G D ξ) n o τ hτ hle
  rw [← hopt]
  refine walkExp_congr_ball n o _ _ ?_
  intro X hX
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k < τ X := Finset.mem_range.mp hk
  have hkle : k ≤ n := le_trans hkn.le (hle X)
  have hxk : X k ∈ D := hin X hX k hkn
  simp only []
  rw [laplacian_trapPotential D hesc (fun v => degree_pos hG v) ξ hxk, neg_neg]

/-- The killed potential vanishes off `D`: the killed Green function has no mass
at a target outside the set. -/
theorem trapPotential_eq_zero_of_notMem (D : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (D : Set V)) (ξ : V → ℝ) {x : V}
    (hx : x ∉ D) : trapPotential G D ξ x = 0 := by
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [killedGreenReal_eq_zero_of_not_mem_of_escape D hesc (by exact_mod_cast hx) v, mul_zero]

/-! ### The potential has mean zero -/

theorem integral_trapPotential (hν : IsProbabilityMeasure ν) (h0 : RWRS.extMean ν = 0)
    (D : Finset V) (x : V) :
    ∫ ξ, trapPotential G D ξ x ∂(RWRS.iidLaw V ν) = 0 := by
  have hpt : ∀ ξ : V → ℝ, trapPotential G D ξ x
      = ∑ v ∈ D, RWRS.killedGreenReal G (D : Set V) v x * (fun z : ℝ => z) (ξ v) := fun ξ =>
    Finset.sum_congr rfl fun v _ => mul_comm _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact integral_weighted_zero D (fun v => RWRS.killedGreenReal G (D : Set V) v x)
    (integrable_id_of_extMean_zero h0) (integral_id_zero h0)

/-! ### Every bounded rule is below the value -/

theorem ofReal_walkExp_payoff_le_supStopValue [Infinite V] (ξ : V → ℝ) (n : ℕ) (o : V)
    (τ : (ℕ → V) → ℕ) (hτ : RWRS.IsStopping τ) (hle : ∀ X, τ X ≤ n) :
    ENNReal.ofReal (RWRS.walkExp G n o (fun X => RWRS.payoff G ξ (τ X) X))
      ≤ RWRS.supStopValue G ξ o := by
  have hmem : RWRS.walkExp G n o (fun X => RWRS.payoff G ξ (τ X) X)
      ∈ RWRS.stopValues G ξ n o := ⟨τ, hτ, hle, rfl⟩
  exact le_iSup_of_le n (le_iSup_of_le _ (le_iSup_of_le hmem le_rfl))

/-- **The finite-volume value is below the optimal stopping value.** -/
theorem ofReal_valueExit_le_supStopValue [Infinite V] [MeasurableSpace V]
    [MeasurableSingletonClass V] [Countable V] [DecidableEq V]
    (hG : G.Connected) (ξ : V → ℝ) (K : Finset V) (o : V) :
    ENNReal.ofReal (RWRS.valueExit G ξ (K : Set V) o) ≤ RWRS.supStopValue G ξ o := by
  have h := ofReal_valueExit_le_odometerLimit hG (fun v => degree_pos hG v)
    (fun u => ξ u + 1) K (esc_of_finset hG K) o
  rw [excess_add_one] at h
  exact h.trans (le_of_eq (supStopValue_eq_odometerLimit hG ξ o).symm)

/-! ### The killed Green function grows with the set -/

theorem killedHeat_mono {C D : Set V} (hCD : C ⊆ D) :
    ∀ (k : ℕ) (x y : V),
      LatticeProb.Graph.killedHeat G C k x y ≤ LatticeProb.Graph.killedHeat G D k x y := by
  intro k
  induction k with
  | zero =>
      intro x y
      by_cases hx : x ∈ C
      · rw [LatticeProb.Network.killedHeat_zero, LatticeProb.Network.killedHeat_zero,
          if_pos hx, if_pos (hCD hx)]
      · rw [LatticeProb.Network.killedHeat_zero, if_neg hx]
        exact LatticeProb.Network.killedHeat_nonneg D 0 x y
  | succ k ih =>
      intro x y
      by_cases hx : x ∈ C
      · rw [LatticeProb.Network.killedHeat_succ, LatticeProb.Network.killedHeat_succ,
          if_pos hx, if_pos (hCD hx)]
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum fun z _ => ih z y) (Nat.cast_nonneg _)
      · rw [LatticeProb.Network.killedHeat_succ, if_neg hx]
        exact LatticeProb.Network.killedHeat_nonneg D (k + 1) x y

theorem killedGreenReal_mono (C D : Finset V) (hCD : C ⊆ D)
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (hescD : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (D : Set V)) (x y : V) :
    RWRS.killedGreenReal G (C : Set V) x y ≤ RWRS.killedGreenReal G (D : Set V) x y := by
  have hCD' : (C : Set V) ⊆ (D : Set V) := by exact_mod_cast hCD
  rw [killedGreenReal_eq_tsum_of_escape C hescC x y,
    killedGreenReal_eq_tsum_of_escape D hescD x y]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact Summable.tsum_le_tsum (fun k => killedHeat_mono hCD' k x y)
    (summable_killedHeat_of_escape C hescC x y) (summable_killedHeat_of_escape D hescD x y)

/-! ### The trap's share of the potential -/

theorem killedGreen_eq_zero_of_notMem (C : Set V) {v : V} (hv : v ∉ C) (y : V) :
    RWRS.killedGreen G C y v = 0 := by
  have hz : ∀ k : ℕ, ENNReal.ofReal (LatticeProb.Graph.killedHeat G C k y v) = 0 := by
    intro k
    rw [LatticeProb.Network.killedHeat_of_target_not_mem hv k y]
    simp
  rw [killedGreen_eq_lib, LatticeProb.Graph.killedGreen, tsum_congr hz, tsum_zero]
  simp

theorem killedGreen_ne_top_of_escape (C : Finset V)
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (hdeg : ∀ w : V, 0 < G.degree w) (y v : V) :
    RWRS.killedGreen G (C : Set V) y v ≠ ⊤ := by
  rw [killedGreen_eq_lib, LatticeProb.Graph.killedGreen]
  have hd : G.degree v ≠ 0 := (hdeg v).ne'
  · have hnum : (∑' k : ℕ,
        ENNReal.ofReal (LatticeProb.Graph.killedHeat G (C : Set V) k y v)) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun k => LatticeProb.Network.killedHeat_nonneg (C : Set V) k y v)
        (summable_killedHeat_of_escape C hescC y v)]
      exact ENNReal.ofReal_ne_top
    exact ENNReal.div_ne_top hnum (by exact_mod_cast hd)

theorem thetaExit_eq_ofReal (C : Finset V)
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (hdeg : ∀ w : V, 0 < G.degree w) (y : V) :
    RWRS.thetaExit G (C : Set V) y
      = ENNReal.ofReal (∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) y v) := by
  have hvan : ∀ v : V, v ∉ C → RWRS.killedGreen G (C : Set V) y v = 0 := fun v hv =>
    killedGreen_eq_zero_of_notMem _ (by exact_mod_cast hv) y
  rw [RWRS.thetaExit, tsum_eq_sum hvan,
    ENNReal.ofReal_sum_of_nonneg fun v _ => killedGreenReal_nonneg_of_escape C hescC y v]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [RWRS.killedGreenReal, ENNReal.ofReal_toReal (killedGreen_ne_top_of_escape C hescC hdeg y v)]

theorem sum_killedGreenReal_ge_thetaExit (C : Finset V)
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (hdeg : ∀ w : V, 0 < G.degree w) (y : V) (L : ℝ)
    (hΘ : ENNReal.ofReal L ≤ RWRS.thetaExit G (C : Set V) y) :
    L ≤ ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) y v := by
  rw [thetaExit_eq_ofReal C hescC hdeg y] at hΘ
  have hnn : 0 ≤ ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) y v :=
    Finset.sum_nonneg fun v _ => killedGreenReal_nonneg_of_escape C hescC y v
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 hΘ

/-- **The trap's share of the potential is at most `-εL`.**  On a trap where the
scenery is at most `-ε`, the killed Green weights of the ambient set dominate
those of the trap, whose total is the inverse-degree exit time. -/
theorem sum_trap_le (C D : Finset V) (hCD : C ⊆ D)
    (hescC : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V))
    (hescD : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (D : Set V))
    (hdeg : ∀ w : V, 0 < G.degree w) (y : V) (ξ : V → ℝ) (ε L : ℝ) (hε : 0 ≤ ε)
    (hξ : ∀ v ∈ C, ξ v ≤ -ε)
    (hΘ : ENNReal.ofReal L ≤ RWRS.thetaExit G (C : Set V) y) :
    ∑ v ∈ C, ξ v * RWRS.killedGreenReal G (D : Set V) v y ≤ -(ε * L) := by
  have hstep : ∀ v ∈ C, ξ v * RWRS.killedGreenReal G (D : Set V) v y
      ≤ -ε * RWRS.killedGreenReal G (C : Set V) y v := by
    intro v hv
    have hDsym : RWRS.killedGreenReal G (D : Set V) v y
        = RWRS.killedGreenReal G (D : Set V) y v :=
      killedGreenReal_symm_of_escape D hescD v y
    have hmono : RWRS.killedGreenReal G (C : Set V) y v
        ≤ RWRS.killedGreenReal G (D : Set V) y v :=
      killedGreenReal_mono C D hCD hescC hescD y v
    have hnnD : 0 ≤ RWRS.killedGreenReal G (D : Set V) y v :=
      killedGreenReal_nonneg_of_escape D hescD y v
    rw [hDsym]
    nlinarith [hξ v hv, hmono, hnnD, hε]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [← Finset.mul_sum]
  have hsum : L ≤ ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) y v :=
    sum_killedGreenReal_ge_thetaExit C hescC hdeg y L hΘ
  nlinarith [hsum, hε]

/-! ### Splitting the potential along the trap blocks -/

open scoped Classical in
/-- **The potential splits along a block, a second block disjoint from it, and the
rest.** -/
theorem trapPotential_split (K C F : Finset V) (hdisj : Disjoint C F) (ξ : V → ℝ) (y : V) :
    trapPotential G K ξ y
      = (∑ v ∈ K ∩ C, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        + (∑ v ∈ K ∩ F, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        + ∑ v ∈ K \ (C ∪ F), ξ v * RWRS.killedGreenReal G (K : Set V) v y := by
  classical
  set f : V → ℝ := fun v => ξ v * RWRS.killedGreenReal G (K : Set V) v y with hf
  have h1 : ∑ v ∈ K ∩ (C ∪ F), f v + ∑ v ∈ K \ (C ∪ F), f v = ∑ v ∈ K, f v :=
    Finset.sum_inter_add_sum_sdiff K (C ∪ F) f
  have h2 : K ∩ (C ∪ F) = (K ∩ C) ∪ (K ∩ F) := Finset.inter_union_distrib_left K C F
  have h3 : Disjoint (K ∩ C) (K ∩ F) :=
    Finset.disjoint_left.2 fun a ha hb =>
      Finset.disjoint_left.1 hdisj (Finset.mem_inter.1 ha).2 (Finset.mem_inter.1 hb).2
  rw [trapPotential, ← h1, h2, Finset.sum_union h3]

open scoped Classical in
/-- The sites of a block outside `K` carry no weight, so the block's share of the
potential is a sum over the whole block. -/
theorem sum_inter_eq_sum_block (K C : Finset V)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) (ξ : V → ℝ) (y : V) :
    ∑ v ∈ K ∩ C, ξ v * RWRS.killedGreenReal G (K : Set V) v y
      = ∑ v ∈ C, ξ v * RWRS.killedGreenReal G (K : Set V) v y := by
  classical
  refine Finset.sum_subset Finset.inter_subset_right fun v hv hnv => ?_
  have hvK : v ∉ K := fun hc => hnv (Finset.mem_inter.2 ⟨hc, hv⟩)
  have hz : RWRS.killedGreenReal G (K : Set V) v y = 0 := by
    rw [killedGreenReal_symm_of_escape K hescK v y]
    exact killedGreenReal_eq_zero_of_not_mem_of_escape K hescK (by exact_mod_cast hvK) y
  rw [hz, mul_zero]

/-- **The trap block never contributes a positive amount.**  This is the bound the
assembly falls back on when the trap set is not contained in `K`. -/
theorem sum_trap_nonpos (C D : Finset V)
    (hescD : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (D : Set V))
    (y : V) (ξ : V → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hξ : ∀ v ∈ C, ξ v ≤ -ε) :
    ∑ v ∈ C, ξ v * RWRS.killedGreenReal G (D : Set V) v y ≤ 0 := by
  refine Finset.sum_nonpos fun v hv => ?_
  have hg : 0 ≤ RWRS.killedGreenReal G (D : Set V) v y :=
    killedGreenReal_nonneg_of_escape D hescD v y
  have hx : ξ v ≤ 0 := le_trans (hξ v hv) (by linarith)
  exact mul_nonpos_of_nonpos_of_nonneg hx hg

open scoped Classical in
/-- **The potential splits along the current block, the earlier blocks, and the
rest.** -/
theorem trapPotential_split_range (K : Finset V) (C : ℕ → Finset V) (i : ℕ)
    (hdisj : ∀ a ≤ i, ∀ b ≤ i, a ≠ b → Disjoint ((C a : Set V)) ((C b : Set V)))
    (ξ : V → ℝ) (y : V) :
    trapPotential G K ξ y
      = (∑ v ∈ K ∩ C i, ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        + (∑ j ∈ Finset.range i, ∑ v ∈ K ∩ C j,
            ξ v * RWRS.killedGreenReal G (K : Set V) v y)
        + (∑ v ∈ K \ (Finset.range (i + 1)).biUnion (fun j => K ∩ C j),
            ξ v * RWRS.killedGreenReal G (K : Set V) v y) := by
  have hpd : ((Finset.range i : Set ℕ)).PairwiseDisjoint (fun j => K ∩ C j) := by
    intro a ha b hb hab
    have ha' : a < i := Finset.mem_range.1 (Finset.mem_coe.1 ha)
    have hb' : b < i := Finset.mem_range.1 (Finset.mem_coe.1 hb)
    exact Finset.disjoint_of_subset_right (Finset.inter_subset_right)
      (Finset.disjoint_of_subset_left (Finset.inter_subset_right)
        (Finset.disjoint_coe.1 (hdisj a ha'.le b hb'.le hab)))
  have hdisjB : Disjoint (C i) ((Finset.range i).biUnion (fun j => K ∩ C j)) := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨j, hj, hjv⟩ := Finset.mem_biUnion.1 hv2
    have hj' : j < i := by simpa [Finset.mem_range] using hj
    have hdd := hdisj i (Nat.le_refl i) j hj'.le (Nat.ne_of_gt hj')
    exact Set.disjoint_left.1 hdd hv1 (Finset.mem_inter.1 hjv).2
  have hsplit := trapPotential_split (G := G) K (C i)
    ((Finset.range i).biUnion (fun j => K ∩ C j)) hdisjB ξ y
  have hmid : ∑ v ∈ K ∩ (Finset.range i).biUnion (fun j => K ∩ C j),
      ξ v * RWRS.killedGreenReal G (K : Set V) v y
      = ∑ j ∈ Finset.range i, ∑ v ∈ K ∩ C j,
          ξ v * RWRS.killedGreenReal G (K : Set V) v y := by
    have hsub : (Finset.range i).biUnion (fun j => K ∩ C j) ⊆ K :=
      (Finset.biUnion_subset).2 fun j _ => Finset.inter_subset_left
    have hKBi : K ∩ (Finset.range i).biUnion (fun j => K ∩ C j)
        = (Finset.range i).biUnion (fun j => K ∩ C j) := by aesop
    rw [hKBi]
    exact Finset.sum_biUnion (f := fun v => ξ v * RWRS.killedGreenReal G (K : Set V) v y) hpd
  have hrest : K \ (C i ∪ (Finset.range i).biUnion (fun j => K ∩ C j))
      = K \ (Finset.range (i + 1)).biUnion (fun j => K ∩ C j) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion,
      Finset.mem_inter, Finset.mem_range]
    refine Iff.intro ?_ ?_
    · intro hKu
      obtain ⟨hK, hu⟩ := hKu
      refine ⟨hK, ?_⟩
      intro hgoal
      obtain ⟨a, ha, hKa, hCa⟩ := hgoal
      by_cases hlt : a < i
      · exact hu (Or.inr ⟨a, hlt, hKa, hCa⟩)
      · have hai : a = i := by omega
        subst hai
        exact hu (Or.inl hCa)
    · intro hKu
      obtain ⟨hK, hneg⟩ := hKu
      refine ⟨hK, ?_⟩
      rintro (hv | ⟨a, ha, hKa, hCa⟩)
      · exact hneg ⟨i, Nat.lt_succ_self i, hK, hv⟩
      · exact hneg ⟨a, Nat.lt_succ_of_lt ha, hKa, hCa⟩
  simp only [hsplit, hmid, hrest]

end RWRS.Support
