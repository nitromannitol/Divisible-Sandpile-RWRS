/-
The finite-volume values increase to the odometer, and the continuation
inequality `eq:continuation` of `sec:doubly-transient`.

Every rule bounded by the exit time of a finite proper set is the increasing
limit of its truncations, which are bounded rules, so the finite-volume value is
below the odometer; and the ball of radius `n` already carries the odometer at
horizon `n`, so the finite-volume values increase to it.
-/
import RWRS.Support.BallWalk

namespace RWRS.Support

open MeasureTheory LatticeProb.Graph
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- A constant is a stopping time. -/
theorem isStopping_const (N : ℕ) : RWRS.IsStopping (fun _ : ℕ → V => N) :=
  fun _ _ _ _ h => h

/-- The exit time of a larger set is larger, so the value is monotone. -/
theorem valueExit_mono (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) {K K' : Finset V}
    (hKK' : K ⊆ K') (hesc' : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K' : Set V))
    (x : V) : RWRS.valueExit G ξ (K : Set V) x ≤ RWRS.valueExit G ξ (K' : Set V) x := by
  have hsub : (K : Set V) ⊆ (K' : Set V) := by exact_mod_cast hKK'
  have hle : ∀ X : ℕ → V, LatticeProb.Graph.exitTime (K : Set V) X
      ≤ LatticeProb.Graph.exitTime (K' : Set V) X := by
    intro X
    refine sInf_le_sInf ?_
    rintro t ⟨m, rfl, hm⟩
    exact ⟨m, rfl, fun hc => hm (hsub hc)⟩
  refine csSup_le ⟨0, zero_mem_stopValuesExit ξ _ x⟩ ?_
  rintro a ⟨τ, hτ, hτle, rfl⟩
  exact le_csSup (bddAbove_stopValuesExit hdeg ξ K' hesc' x)
    ⟨τ, hτ, fun X => le_trans (hτle X) (hle X), rfl⟩

/-- **The finite-volume value is below the odometer.**  A rule bounded by the
exit time of `K` is the limit of its truncations, and each truncation is a
bounded rule, whose value the odometer dominates. -/
theorem ofReal_valueExit_le_odometerLimit [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (σ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) (x : V) :
    ENNReal.ofReal (RWRS.valueExit G (RWRS.excess σ) (K : Set V) x)
      ≤ RWRS.odometerLimit G σ x := by
  classical
  set ξ : V → ℝ := RWRS.excess σ with hξ
  set μ : Measure (ℕ → V) := RWRS.walkLaw G x with hμ
  have hmem : ∀ a ∈ RWRS.stopValuesExit G ξ (K : Set V) x,
      ENNReal.ofReal a ≤ RWRS.odometerLimit G σ x := by
    rintro a ⟨τ, hτ, hτle, rfl⟩
    set τN : ℕ → (ℕ → V) → ℕ := fun N X => min (τ X) N with hτNdef
    have hτNstop : ∀ N, RWRS.IsStopping (τN N) := fun N =>
      isStopping_min hτ (isStopping_const N)
    have hτNle : ∀ N X, τN N X ≤ N := fun N X => min_le_right _ _
    have hτNexit : ∀ N X, (τN N X : ℕ∞) ≤ LatticeProb.Graph.exitTime (K : Set V) X := by
      intro N X
      refine le_trans ?_ (hτle X)
      exact_mod_cast min_le_left (τ X) N
    -- each truncation is a bounded rule
    have hbound : ∀ (N : ℕ) (X : ℕ → V),
        |RWRS.payoff G ξ (τN N X) X| ≤ (N : ℝ) * stepBound G ξ K := by
      intro N X
      have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := K) (n := τN N X) (X := X)
        (fun k hk => mem_of_lt_exitTime (C := (K : Set V))
          (lt_of_lt_of_le (by exact_mod_cast hk) (hτNexit N X)))
      have h2 : ((τN N X : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hτNle N X
      have h3 : (0 : ℝ) ≤ stepBound G ξ K := stepBound_nonneg ξ K
      nlinarith
    have hstop : ∀ N : ℕ,
        ENNReal.ofReal (∫ X, RWRS.payoff G ξ (τN N X) X ∂μ)
          ≤ RWRS.odometerLimit G σ x := by
      intro N
      have hdep : DependsUpTo N (fun X => RWRS.payoff G ξ (τN N X) X) :=
        dependsUpTo_payoff_stopping (hτNstop N) (hτNle N) ξ
      have hEq : RWRS.walkExp G N x (fun X => RWRS.payoff G ξ (τN N X) X)
          = ∫ X, RWRS.payoff G ξ (τN N X) X ∂μ := by
        rw [walkExp_eq_lib N x, hμ, walkLaw_eq_lib x]
        exact LatticeProb.Graph.walkExp_eq_integral hdeg N x _
          (measurable_of_dependsUpTo hdep) ((N : ℝ) * stepBound G ξ K)
          (fun X => by rw [Real.norm_eq_abs]; exact hbound N X) hdep
      have hin : (∫ X, RWRS.payoff G ξ (τN N X) X ∂μ) ∈ RWRS.stopValues G ξ N x :=
        ⟨τN N, hτNstop N, hτNle N, hEq.symm⟩
      have hle := (odometer_isLUB hG σ N x).1 _ hin
      exact le_trans (ENNReal.ofReal_le_ofReal hle)
        (le_iSup (fun n => ENNReal.ofReal (RWRS.odometer G σ n x)) N)
    -- and the truncations converge
    have hfin := LatticeProb.Graph.ae_exitTime_ne_top hdeg K hesc x
    rw [← walkLaw_eq_lib x] at hfin
    have hbdd : Integrable
        (fun X => stepBound G ξ K
          * (((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ) : ℝ)) μ := by
      have := LatticeProb.Graph.integrable_exitNat hdeg K hesc x
      rw [← walkLaw_eq_lib x] at this
      exact this.const_mul _
    have hconv : Filter.Tendsto
        (fun N : ℕ => ∫ X, RWRS.payoff G ξ (τN N X) X ∂μ) Filter.atTop
        (nhds (∫ X, RWRS.payoff G ξ (τ X) X ∂μ)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence _
        (fun N => (measurable_payoff_stopping (hτNstop N) ξ).aestronglyMeasurable) hbdd ?_ ?_
      · intro N
        filter_upwards [hfin] with X hX
        have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := K) (n := τN N X) (X := X)
          (fun k hk => mem_of_lt_exitTime (C := (K : Set V))
            (lt_of_lt_of_le (by exact_mod_cast hk) (hτNexit N X)))
        have h2 : ((τN N X : ℕ) : ℝ)
            ≤ (((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ) : ℝ) := by
          have : (τN N X : ℕ∞) ≤ ((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ∞) := by
            rw [ENat.coe_toNat hX]
            exact hτNexit N X
          exact_mod_cast this
        have h3 : (0 : ℝ) ≤ stepBound G ξ K := stepBound_nonneg ξ K
        rw [Real.norm_eq_abs]
        nlinarith
      · filter_upwards [hfin] with X hX
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        rw [Filter.EventuallyEq, Filter.eventually_atTop]
        refine ⟨τ X, fun N hN => ?_⟩
        simp only [hτNdef, min_eq_left hN]
    have hlim : Filter.Tendsto
        (fun N : ℕ => ENNReal.ofReal (∫ X, RWRS.payoff G ξ (τN N X) X ∂μ)) Filter.atTop
        (nhds (ENNReal.ofReal (∫ X, RWRS.payoff G ξ (τ X) X ∂μ))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hconv
    exact le_of_tendsto hlim (Filter.Eventually.of_forall hstop)
  -- pass from the elements to the supremum
  rcases eq_or_ne (RWRS.odometerLimit G σ x) ⊤ with hL | hL
  · rw [hL]; exact le_top
  · refine (ENNReal.ofReal_le_iff_le_toReal hL).2 ?_
    refine csSup_le ⟨0, zero_mem_stopValuesExit ξ _ x⟩ fun a ha => ?_
    exact (ENNReal.ofReal_le_iff_le_toReal hL).1 (hmem a ha)

omit [G.LocallyFinite] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- Every `Finset` of an infinite connected graph is escaped from. -/
theorem esc_of_finset [Infinite V] (hG : G.Connected) (K : Finset V) :
    ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V) := by
  intro x
  obtain ⟨q, hq⟩ : ∃ q : V, q ∉ K := by
    by_contra hcon
    have hsub : (Set.univ : Set V) ⊆ (K : Set V) := by
      intro z _
      by_contra hz
      exact hcon ⟨z, hz⟩
    exact (Set.infinite_univ (α := V)) (Set.Finite.subset K.finite_toSet hsub)
  obtain ⟨p⟩ := hG.preconnected x q
  exact ⟨q, p, by simpa using hq⟩

/-- **The finite-volume values increase to the odometer.** -/
theorem iSup_ofReal_valueExit [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (σ : V → ℝ) (x : V) :
    (⨆ K : Finset V, ENNReal.ofReal (RWRS.valueExit G (RWRS.excess σ) (K : Set V) x))
      = RWRS.odometerLimit G σ x := by
  refine le_antisymm (iSup_le fun K => ?_) ?_
  · exact ofReal_valueExit_le_odometerLimit hG hdeg σ K (esc_of_finset hG K) x
  · refine iSup_le fun n => ?_
    obtain ⟨B, -, -, hval⟩ := exists_finset_odometer_le_valueExit hG hdeg σ x n
    exact le_trans (ENNReal.ofReal_le_ofReal hval)
      (le_iSup (fun K : Finset V =>
        ENNReal.ofReal (RWRS.valueExit G (RWRS.excess σ) (K : Set V) x)) B)

/-! ### The continuation inequality at finite volume -/

/-- A bound for the finite-volume value, uniform in the site. -/
noncomputable def valueBound (G : SimpleGraph V) [G.LocallyFinite]
    (ξ : V → ℝ) (K : Finset V) : ℝ :=
  ∑ y ∈ K, RWRS.valueExit G ξ (K : Set V) y

theorem valueExit_le_valueBound (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) (y : V) :
    RWRS.valueExit G ξ (K : Set V) y ≤ valueBound G ξ K := by
  classical
  by_cases hy : y ∈ K
  · exact Finset.single_le_sum
      (f := fun z => RWRS.valueExit G ξ (K : Set V) z)
      (fun z _ => zero_le_valueExit hdeg ξ K hesc z) hy
  · rw [valueExit_eq_zero_of_notMem_set hdeg ξ K hesc hy]
    exact Finset.sum_nonneg fun z _ => zero_le_valueExit hdeg ξ K hesc z

theorem zero_le_valueBound (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) :
    0 ≤ valueBound G ξ K :=
  Finset.sum_nonneg fun z _ => zero_le_valueExit hdeg ξ K hesc z

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The truncated exit time of a trajectory that starts with a step inside the
set. -/
theorem exitTrunc_cons {D : Set V} {x : V} (hx : x ∈ D) (n : ℕ) (X : ℕ → V) :
    exitTrunc D (n + 1) (RWRS.cons x X) = exitTrunc D n X + 1 := by
  by_cases h : RWRS.cons x X ∈ stayIn D (n + 1)
  · have hX : X ∈ stayIn D n := by
      intro j hj
      exact h (j + 1) (by omega)
    rw [exitTrunc, if_pos h, exitTrunc, if_pos hX]
  · have hX : X ∉ stayIn D n := by
      intro hc
      refine h fun j hj => ?_
      cases j with
      | zero => exact hx
      | succ i => exact hc i (by omega)
    have hfin : LatticeProb.Graph.exitTime D X ≠ ⊤ := fun hc =>
      hX ((LatticeProb.Graph.exitTime_eq_top_iff D X).mp hc n)
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hfin
    rw [exitTrunc_of_notMem h, exitTrunc_of_notMem hX, exitTime_cons_of_mem hx, ← hr]
    rw [show ((r : ℕ∞) + 1) = ((r + 1 : ℕ) : ℕ∞) by push_cast; ring]
    simp

/-- **The continuation inequality at a finite horizon.**  Running to the exit
from `D`, or to the horizon, and then collecting the value of the position
reached, is worth no more than the value at the start. -/
theorem integral_continuation_trunc_le (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ)
    (K D : Finset V) (hDK : D ⊆ K)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) :
    ∀ (n : ℕ) (x : V),
      (∫ X, (RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X
          + RWRS.valueExit G ξ (K : Set V) (X (exitTrunc (D : Set V) n X)))
          ∂(LatticeProb.Graph.walkLaw G x))
        ≤ RWRS.valueExit G ξ (K : Set V) x := by
  classical
  set F : V → ℝ := fun y => RWRS.valueExit G ξ (K : Set V) y with hF
  have hFmeas : Measurable F := measurable_of_countable F
  have hFnonneg : ∀ y, 0 ≤ F y := fun y => zero_le_valueExit hdeg ξ K hesc y
  have hFle : ∀ y, F y ≤ valueBound G ξ K := valueExit_le_valueBound hdeg ξ K hesc
  have hVB : 0 ≤ valueBound G ξ K := zero_le_valueBound hdeg ξ K hesc
  have hSB : (0 : ℝ) ≤ stepBound G ξ D := stepBound_nonneg ξ D
  have hmeas : ∀ n : ℕ, Measurable fun X : ℕ → V =>
      RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X + F (X (exitTrunc (D : Set V) n X)) := by
    intro n
    exact (measurable_payoff_stopping (isStopping_exitTrunc (D : Set V) n) ξ).add
      (measurable_comp_apply_stopping (isStopping_exitTrunc (D : Set V) n)
        (exitTrunc_le (D : Set V) n) hFmeas)
  have hbnd : ∀ (n : ℕ) (X : ℕ → V),
      ‖RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X
        + F (X (exitTrunc (D : Set V) n X))‖ ≤ (n : ℝ) * stepBound G ξ D + valueBound G ξ K := by
    intro n X
    have h1 := abs_payoff_exitTrunc_le (G := G) ξ D n X
    have h2 := hFle (X (exitTrunc (D : Set V) n X))
    have h3 := hFnonneg (X (exitTrunc (D : Set V) n X))
    rw [Real.norm_eq_abs]
    calc |RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X + F (X (exitTrunc (D : Set V) n X))|
        ≤ |RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X|
            + |F (X (exitTrunc (D : Set V) n X))| := abs_add_le _ _
      _ ≤ (n : ℝ) * stepBound G ξ D + valueBound G ξ K := by
          rw [abs_of_nonneg h3]; exact add_le_add h1 h2
  have hint : ∀ (n : ℕ) (y : V), Integrable
      (fun X : ℕ → V => RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X
        + F (X (exitTrunc (D : Set V) n X))) (LatticeProb.Graph.walkLaw G y) := by
    intro n y
    refine Integrable.mono' (integrable_const ((n : ℝ) * stepBound G ξ D + valueBound G ξ K))
      (hmeas n).aestronglyMeasurable (Filter.Eventually.of_forall (hbnd n))
  intro n
  induction n with
  | zero =>
      intro x
      have hzero : ∀ X : ℕ → V, exitTrunc (D : Set V) 0 X = 0 := by
        intro X
        by_cases h : X ∈ stayIn (D : Set V) 0
        · rw [exitTrunc, if_pos h]
        · rw [exitTrunc_of_notMem h]
          have h0 : X 0 ∉ (D : Set V) := fun hc => h fun j hj => by
            rw [Nat.le_zero.mp hj]; exact hc
          rw [LatticeProb.Graph.exitTime_eq_natCast_of (D : Set V) (n := 0) h0 (by omega)]
          rfl
      have hae : ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G x),
          RWRS.payoff G ξ (exitTrunc (D : Set V) 0 X) X
            + F (X (exitTrunc (D : Set V) 0 X)) = F x := by
        filter_upwards [LatticeProb.Graph.ae_walkLaw_start (G := G) x] with X hX
        rw [hzero X, hX]
        show RWRS.payoff G ξ 0 X + F x = F x
        simp [RWRS.payoff]
      rw [integral_congr_ae hae, integral_const]
      simp only [probReal_univ, smul_eq_mul, one_mul]
      exact le_rfl
  | succ n ih =>
      intro x
      by_cases hx : x ∈ D
      · have hxD : x ∈ (D : Set V) := by exact_mod_cast hx
        have hxK : x ∈ K := hDK hx
        have hfs := integral_walkLaw_firstStep' (G := G) x (hdeg x) _ (hmeas (n + 1))
          (hint (n + 1) x)
        have hterm : ∀ y ∈ G.neighborFinset x,
            (∫ X, (RWRS.payoff G ξ (exitTrunc (D : Set V) (n + 1) (LatticeProb.Graph.cons x X))
                (LatticeProb.Graph.cons x X)
              + F ((LatticeProb.Graph.cons x X)
                  (exitTrunc (D : Set V) (n + 1) (LatticeProb.Graph.cons x X))))
                ∂(LatticeProb.Graph.walkLaw G y))
              ≤ ξ x / G.degree x + F y := by
          intro y _
          have hrw : ∀ X : ℕ → V,
              RWRS.payoff G ξ (exitTrunc (D : Set V) (n + 1) (LatticeProb.Graph.cons x X))
                  (LatticeProb.Graph.cons x X)
                + F ((LatticeProb.Graph.cons x X)
                    (exitTrunc (D : Set V) (n + 1) (LatticeProb.Graph.cons x X)))
                = ξ x / G.degree x
                  + (RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X
                      + F (X (exitTrunc (D : Set V) n X))) := by
            intro X
            rw [← cons_eq_lib, exitTrunc_cons hxD n X, payoff_cons]
            show ξ x / G.degree x + RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X
                + F (X (exitTrunc (D : Set V) n X))
              = ξ x / G.degree x
                  + (RWRS.payoff G ξ (exitTrunc (D : Set V) n X) X
                      + F (X (exitTrunc (D : Set V) n X)))
            ring
          simp only [hrw]
          rw [integral_add (integrable_const _) (hint n y)]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          have := ih y
          linarith
        have hsum := Finset.sum_le_sum hterm
        rw [Finset.sum_add_distrib, Finset.sum_const,
          SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul] at hsum
        have hdx : (0 : ℝ) < (G.degree x : ℝ) := by exact_mod_cast hdeg x
        rw [hfs]
        have hstep : (G.degree x : ℝ)⁻¹ * ((G.degree x : ℝ) * (ξ x / G.degree x)
            + ∑ y ∈ G.neighborFinset x, F y)
            = bellman G ξ (K : Set V) x := by
          rw [bellman]
          field_simp
          rfl
        calc (G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x,
              (∫ X, (RWRS.payoff G ξ (exitTrunc (D : Set V) (n + 1) (LatticeProb.Graph.cons x X))
                  (LatticeProb.Graph.cons x X)
                + F ((LatticeProb.Graph.cons x X)
                    (exitTrunc (D : Set V) (n + 1) (LatticeProb.Graph.cons x X))))
                  ∂(LatticeProb.Graph.walkLaw G y))
            ≤ (G.degree x : ℝ)⁻¹ * ((G.degree x : ℝ) * (ξ x / G.degree x)
                + ∑ y ∈ G.neighborFinset x, F y) :=
              mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = bellman G ξ (K : Set V) x := hstep
          _ ≤ F x := bellman_le_valueExit hdeg ξ K hesc hxK
      · have hae : ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G x),
            RWRS.payoff G ξ (exitTrunc (D : Set V) (n + 1) X) X
              + F (X (exitTrunc (D : Set V) (n + 1) X)) = F x := by
          filter_upwards [LatticeProb.Graph.ae_walkLaw_start (G := G) x] with X hX
          have h0 : X 0 ∉ (D : Set V) := by rw [hX]; exact_mod_cast hx
          have hns : X ∉ stayIn (D : Set V) (n + 1) := fun hc => h0 (hc 0 (by omega))
          have hz : exitTrunc (D : Set V) (n + 1) X = 0 := by
            rw [exitTrunc_of_notMem hns,
              LatticeProb.Graph.exitTime_eq_natCast_of (D : Set V) (n := 0) h0 (by omega)]
            rfl
          rw [hz, hX]
          show RWRS.payoff G ξ 0 X + F x = F x
          simp [RWRS.payoff]
        rw [integral_congr_ae hae, integral_const]
        simp only [probReal_univ, smul_eq_mul, one_mul]
        exact le_rfl

/-- **The continuation inequality at finite volume**, `eq:continuation` with the
odometer replaced by the value at a finite proper `K` containing `D`: running to
the exit from `D` and then collecting the value of the position reached is worth
no more than the value at the start. -/
theorem integral_continuation_le (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ)
    (K D : Finset V) (hDK : D ⊆ K)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hescD : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (D : Set V)) (x : V) :
    (∫ X, (RWRS.payoffAtExit G ξ (D : Set V) X
        + RWRS.valueExit G ξ (K : Set V)
            (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat))
        ∂(LatticeProb.Graph.walkLaw G x))
      ≤ RWRS.valueExit G ξ (K : Set V) x := by
  classical
  set F : V → ℝ := fun y => RWRS.valueExit G ξ (K : Set V) y with hF
  set μ : Measure (ℕ → V) := LatticeProb.Graph.walkLaw G x with hμ
  have hFmeas : Measurable F := measurable_of_countable F
  have hFnonneg : ∀ y, 0 ≤ F y := fun y => zero_le_valueExit hdeg ξ K hesc y
  have hFle : ∀ y, F y ≤ valueBound G ξ K := valueExit_le_valueBound hdeg ξ K hesc
  have hSB : (0 : ℝ) ≤ stepBound G ξ D := stepBound_nonneg ξ D
  have hfin := LatticeProb.Graph.ae_exitTime_ne_top hdeg D hescD x
  have hdom : Integrable
      (fun X => stepBound G ξ D
          * (((LatticeProb.Graph.exitTime (D : Set V) X).toNat : ℕ) : ℝ)
        + valueBound G ξ K) μ :=
    ((LatticeProb.Graph.integrable_exitNat hdeg D hescD x).const_mul _).add
      (integrable_const _)
  have hconv : Filter.Tendsto
      (fun N : ℕ => ∫ X, (RWRS.payoff G ξ (exitTrunc (D : Set V) N X) X
          + F (X (exitTrunc (D : Set V) N X))) ∂μ) Filter.atTop
      (nhds (∫ X, (RWRS.payoffAtExit G ξ (D : Set V) X
          + F (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat)) ∂μ)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence _
      (fun N => ((measurable_payoff_stopping (isStopping_exitTrunc (D : Set V) N) ξ).add
        (measurable_comp_apply_stopping (isStopping_exitTrunc (D : Set V) N)
          (exitTrunc_le (D : Set V) N) hFmeas)).aestronglyMeasurable) hdom ?_ ?_
    · intro N
      filter_upwards [hfin] with X hX
      have hle := exitTrunc_le_exitNat (C := D) (N := N) hX
      have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := D)
        (n := exitTrunc (D : Set V) N X) (X := X)
        (fun k hk => mem_of_lt_exitTrunc D N X hk)
      have h2 : ((exitTrunc (D : Set V) N X : ℕ) : ℝ)
          ≤ (((LatticeProb.Graph.exitTime (D : Set V) X).toNat : ℕ) : ℝ) := by
        exact_mod_cast hle
      have h3 := hFle (X (exitTrunc (D : Set V) N X))
      have h4 := hFnonneg (X (exitTrunc (D : Set V) N X))
      rw [Real.norm_eq_abs]
      calc |RWRS.payoff G ξ (exitTrunc (D : Set V) N X) X
              + F (X (exitTrunc (D : Set V) N X))|
          ≤ |RWRS.payoff G ξ (exitTrunc (D : Set V) N X) X|
              + |F (X (exitTrunc (D : Set V) N X))| := abs_add_le _ _
        _ ≤ stepBound G ξ D
              * (((LatticeProb.Graph.exitTime (D : Set V) X).toNat : ℕ) : ℝ)
            + valueBound G ξ K := by
              rw [abs_of_nonneg h4]
              refine add_le_add ?_ h3
              nlinarith
    · filter_upwards [hfin] with X hX
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      refine ⟨(LatticeProb.Graph.exitTime (D : Set V) X).toNat, fun N hN => ?_⟩
      rw [RWRS.payoffAtExit, exitTime_eq_lib,
        exitTrunc_of_notMem (notMem_stayIn_of_le hX hN)]
  exact le_of_tendsto hconv (Filter.Eventually.of_forall fun N =>
    integral_continuation_trunc_le hdeg ξ K D hDK hesc N x)

/-! ### The continuation inequality for the odometer -/

omit [DecidableEq V] in
/-- Reading a function of the vertex at the exit time is measurable. -/
theorem measurable_comp_exitNat {β : Type*} [MeasurableSpace β] (C : Set V) {g : V → β}
    (hg : Measurable g) :
    Measurable fun X : ℕ → V => g (X (LatticeProb.Graph.exitTime C X).toNat) := by
  have h1 : Measurable (fun X : ℕ → V => (LatticeProb.Graph.exitTime C X).toNat) :=
    LatticeProb.Graph.measurable_exitNat C
  have h2 : Measurable (fun p : (ℕ → V) × ℕ => g (p.1 p.2)) :=
    measurable_from_prod_countable_left fun n => hg.comp (measurable_pi_apply n)
  exact h2.comp (measurable_id.prodMk h1)

/-- **The continuation inequality `eq:continuation`.**  Running to the exit from
a finite set `D` and then collecting the odometer at the position reached is
worth no more than the odometer at the start.  Both sides live in `[0,∞]`, and
the expected payoff up to the exit, which may be negative, is carried on the
right. -/
theorem lintegral_odometerLimit_exit_le [Infinite V] (hG : G.Connected)
    (hdeg : ∀ v : V, 0 < G.degree v) (σ : V → ℝ) (D : Finset V) (x : V) :
    (∫⁻ X, RWRS.odometerLimit G σ (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat)
        ∂(LatticeProb.Graph.walkLaw G x))
      ≤ RWRS.odometerLimit G σ x
        + ENNReal.ofReal (-(∫ X, RWRS.payoffAtExit G (RWRS.excess σ) (D : Set V) X
            ∂(LatticeProb.Graph.walkLaw G x))) := by
  classical
  set ξ : V → ℝ := RWRS.excess σ with hξ
  set μ : Measure (ℕ → V) := LatticeProb.Graph.walkLaw G x with hμ
  set S : ℝ := ∫ X, RWRS.payoffAtExit G ξ (D : Set V) X ∂μ with hS
  have hescD : ∀ z : V, ∃ (q : V) (_ : G.Walk z q), q ∉ (D : Set V) := esc_of_finset hG D
  -- an increasing sequence of finite sets exhausting the graph
  obtain ⟨e, he⟩ := exists_surjective_nat V
  set g : V → ℕ := fun y => Classical.choose (he y) with hgdef
  have hge : ∀ y, e (g y) = y := fun y => Classical.choose_spec (he y)
  set Kseq : ℕ → Finset V := fun j => D ∪ (Finset.range j).image e with hKseq
  have hDK : ∀ j, D ⊆ Kseq j := fun j => Finset.subset_union_left
  have hmono : Monotone Kseq := by
    intro i j hij
    refine Finset.union_subset_union_right ?_
    refine Finset.image_subset_image fun a ha => ?_
    exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 ha) hij)
  have hcof : ∀ K : Finset V, ∃ j, K ⊆ Kseq j := by
    intro K
    refine ⟨K.sup g + 1, fun y hy => ?_⟩
    refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨g y, Finset.mem_range.2 ?_, hge y⟩)
    have := Finset.le_sup (f := g) hy
    omega
  have hescK : ∀ j, ∀ z : V, ∃ (q : V) (_ : G.Walk z q), q ∉ ((Kseq j : Finset V) : Set V) :=
    fun j => esc_of_finset hG (Kseq j)
  -- the values along the sequence increase to the odometer at every vertex
  have hsup : ∀ y : V,
      (⨆ j : ℕ, ENNReal.ofReal (RWRS.valueExit G ξ ((Kseq j : Finset V) : Set V) y))
        = RWRS.odometerLimit G σ y := by
    intro y
    refine le_antisymm (iSup_le fun j => ?_) ?_
    · exact ofReal_valueExit_le_odometerLimit hG hdeg σ (Kseq j) (hescK j) y
    · rw [← iSup_ofReal_valueExit hG hdeg σ y]
      refine iSup_le fun K => ?_
      obtain ⟨j, hj⟩ := hcof K
      exact le_trans (ENNReal.ofReal_le_ofReal
        (valueExit_mono hdeg ξ hj (hescK j) y))
        (le_iSup (fun j : ℕ =>
          ENNReal.ofReal (RWRS.valueExit G ξ ((Kseq j : Finset V) : Set V) y)) j)
  -- monotone convergence along the sequence
  have hmeasj : ∀ j : ℕ, Measurable fun X : ℕ → V =>
      ENNReal.ofReal (RWRS.valueExit G ξ ((Kseq j : Finset V) : Set V)
        (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat)) :=
    fun j => measurable_comp_exitNat (D : Set V)
      (ENNReal.measurable_ofReal.comp (measurable_of_countable _))
  have hmonoj : Monotone fun j : ℕ => fun X : ℕ → V =>
      ENNReal.ofReal (RWRS.valueExit G ξ ((Kseq j : Finset V) : Set V)
        (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat)) := by
    intro i j hij X
    exact ENNReal.ofReal_le_ofReal
      (valueExit_mono hdeg ξ (hmono hij) (hescK j) _)
  have hmc : (∫⁻ X, RWRS.odometerLimit G σ
        (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat) ∂μ)
      = ⨆ j : ℕ, ∫⁻ X, ENNReal.ofReal (RWRS.valueExit G ξ ((Kseq j : Finset V) : Set V)
          (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat)) ∂μ := by
    rw [← lintegral_iSup hmeasj hmonoj]
    refine lintegral_congr fun X => ?_
    exact (hsup _).symm
  rw [hmc]
  refine iSup_le fun j => ?_
  -- at each stage the finite-volume continuation inequality applies
  set K : Finset V := Kseq j with hK
  set F : V → ℝ := fun y => RWRS.valueExit G ξ (K : Set V) y with hF
  have hFnonneg : ∀ y, 0 ≤ F y := fun y => zero_le_valueExit hdeg ξ K (hescK j) y
  have hFle : ∀ y, F y ≤ valueBound G ξ K := valueExit_le_valueBound hdeg ξ K (hescK j)
  have hFint : Integrable (fun X => F (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat)) μ := by
    refine Integrable.mono' (integrable_const (valueBound G ξ K))
      (measurable_comp_exitNat (D : Set V) (measurable_of_countable F)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg _)]
    exact hFle _
  have hSint : Integrable (fun X => RWRS.payoffAtExit G ξ (D : Set V) X) μ :=
    integrable_payoffAtExit hdeg ξ D hescD x
  have hcont := integral_continuation_le hdeg ξ K D (hDK j) (hescK j) hescD x
  rw [integral_add hSint hFint] at hcont
  have hFle' : (∫ X, F (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat) ∂μ)
      ≤ F x + (-S) := by rw [hS]; linarith
  calc (∫⁻ X, ENNReal.ofReal (F (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat)) ∂μ)
      = ENNReal.ofReal (∫ X, F (X (LatticeProb.Graph.exitTime (D : Set V) X).toNat) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hFint
          (Filter.Eventually.of_forall fun X => hFnonneg _)).symm
    _ ≤ ENNReal.ofReal (F x + (-S)) := ENNReal.ofReal_le_ofReal hFle'
    _ ≤ ENNReal.ofReal (F x) + ENNReal.ofReal (-S) := ENNReal.ofReal_add_le
    _ ≤ RWRS.odometerLimit G σ x + ENNReal.ofReal (-S) := by
        gcongr
        exact ofReal_valueExit_le_odometerLimit hG hdeg σ K (hescK j) x

end RWRS.Support
