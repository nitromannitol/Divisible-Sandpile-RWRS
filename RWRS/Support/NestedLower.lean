/-
The lower half of `thm:nested-vol`: every finite set from which the walk escapes
contributes to the odometer,

    ∑_{v ∈ C} g_C(o,v) (σ(v) - 1) ≤ u_∞(o) .

The left side is `E_o[S_{τ_C}]` by the voltage identity, and the truncations
`τ_C ∧ m` are bounded stopping times, whose values `E_o[S_{τ_C ∧ m}]` are among
the ones the odometer dominates.  Since the exit time is integrable and the
payoff moves by at most a fixed step inside `C`, dominated convergence carries
the bound to the limit.
-/
import RWRS.Support.VoltageIdentity
import RWRS.Support.Representation
import RWRS.Support.Countable

namespace RWRS.Support

open MeasureTheory LatticeProb.Graph
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-! ### The payoff inside a finite set moves by a bounded step -/

/-- A bound for one step of the payoff at a site of `C`. -/
noncomputable def stepBound (G : SimpleGraph V) [G.LocallyFinite] (ξ : V → ℝ)
    (C : Finset V) : ℝ := ∑ v ∈ C, |ξ v / G.degree v|

theorem stepBound_nonneg (ξ : V → ℝ) (C : Finset V) : 0 ≤ stepBound G ξ C :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem le_stepBound {ξ : V → ℝ} {C : Finset V} {v : V} (hv : v ∈ C) :
    |ξ v / G.degree v| ≤ stepBound G ξ C :=
  Finset.single_le_sum (f := fun u => |ξ u / G.degree u|) (fun _ _ => abs_nonneg _) hv

theorem abs_payoff_le {ξ : V → ℝ} {C : Finset V} {n : ℕ} {X : ℕ → V}
    (hmem : ∀ k, k < n → X k ∈ C) :
    |RWRS.payoff G ξ n X| ≤ (n : ℝ) * stepBound G ξ C := by
  calc |RWRS.payoff G ξ n X| ≤ ∑ k ∈ Finset.range n, |ξ (X k) / G.degree (X k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, stepBound G ξ C :=
        Finset.sum_le_sum fun k hk => le_stepBound (hmem k (Finset.mem_range.1 hk))
    _ = (n : ℝ) * stepBound G ξ C := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The walk is inside `C` before the truncated exit time -/

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem mem_of_lt_exitTrunc (C : Finset V) (N : ℕ) (X : ℕ → V) {k : ℕ}
    (hk : k < exitTrunc (C : Set V) N X) : X k ∈ C := by
  classical
  by_cases hX : X ∈ stayIn (C : Set V) N
  · rw [exitTrunc, if_pos hX] at hk
    exact hX k (le_of_lt hk)
  · rw [exitTrunc_of_notMem hX] at hk
    have hlt : (k : ℕ∞) < LatticeProb.Graph.exitTime (C : Set V) X := by
      obtain ⟨heq, -, -⟩ := exitTime_eq_natCast_of_notMem hX
      rw [heq]
      exact_mod_cast hk
    have hmem : X ∈ stayIn (C : Set V) k := by
      rw [stayIn_eq_lt_exitTime]
      exact hlt
    exact hmem k le_rfl

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem dependsUpTo_payoff_exitTrunc (ξ : V → ℝ) (C : Finset V) (N : ℕ) :
    DependsUpTo N (fun X => RWRS.payoff G ξ (exitTrunc (C : Set V) N X) X) := by
  intro X Y hXY
  have hτ : exitTrunc (C : Set V) N X = exitTrunc (C : Set V) N Y :=
    dependsUpTo_of_isStopping (isStopping_exitTrunc (C : Set V) N)
      (exitTrunc_le (C : Set V) N) X Y hXY
  have hle := exitTrunc_le (C : Set V) N X
  simp only [RWRS.payoff]
  rw [hτ]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkN : k ≤ N := by
    have := Finset.mem_range.1 hk
    rw [← hτ] at this
    omega
  rw [hXY k hkN]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem abs_payoff_exitTrunc_le (ξ : V → ℝ) (C : Finset V) (N : ℕ) (X : ℕ → V) :
    |RWRS.payoff G ξ (exitTrunc (C : Set V) N X) X| ≤ (N : ℝ) * stepBound G ξ C := by
  have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := C)
    (n := exitTrunc (C : Set V) N X) (X := X)
    (fun k hk => mem_of_lt_exitTrunc C N X hk)
  have h2 : ((exitTrunc (C : Set V) N X : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast exitTrunc_le (C : Set V) N X
  have h3 : (0 : ℝ) ≤ stepBound G ξ C := stepBound_nonneg ξ C
  nlinarith

/-! ### The walk average is the library's -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem cons_eq_lib (x : V) (X : ℕ → V) :
    RWRS.cons x X = LatticeProb.Graph.cons x X := by
  funext k
  cases k with
  | zero => rfl
  | succ k => rfl

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem walkExp_eq_lib : ∀ (n : ℕ) (x : V) (F : (ℕ → V) → ℝ),
    RWRS.walkExp G n x F = LatticeProb.Graph.walkExp G n x F := by
  intro n
  induction n with
  | zero => intro x F; rfl
  | succ n ih =>
      intro x F
      show (∑ y ∈ G.neighborFinset x,
          RWRS.walkExp G n y (fun X => F (RWRS.cons x X))) / G.degree x
        = (∑ y ∈ G.neighborFinset x,
          LatticeProb.Graph.walkExp G n y (fun X => F (LatticeProb.Graph.cons x X)))
            / G.degree x
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      have hfun : (fun X => F (RWRS.cons x X))
          = fun X => F (LatticeProb.Graph.cons x X) := by
        funext X
        rw [cons_eq_lib]
      rw [ih y (fun X => F (RWRS.cons x X)), hfun]

/-! ### The truncated exit values are stopping values -/

theorem integral_payoff_exitTrunc_mem (hdeg : ∀ v : V, 0 < G.degree v)
    (ξ : V → ℝ) (C : Finset V) (N : ℕ) (o : V) :
    (∫ X, RWRS.payoff G ξ (exitTrunc (C : Set V) N X) X ∂(RWRS.walkLaw G o))
      ∈ RWRS.stopValues G ξ N o := by
  refine ⟨exitTrunc (C : Set V) N, isStopping_exitTrunc (C : Set V) N,
    exitTrunc_le (C : Set V) N, ?_⟩
  rw [walkExp_eq_lib N o, walkLaw_eq_lib o]
  exact (LatticeProb.Graph.walkExp_eq_integral hdeg N o _
    (measurable_of_dependsUpTo (dependsUpTo_payoff_exitTrunc ξ C N))
    ((N : ℝ) * stepBound G ξ C)
    (fun X => by
      rw [Real.norm_eq_abs]
      exact abs_payoff_exitTrunc_le ξ C N X)
    (dependsUpTo_payoff_exitTrunc ξ C N)).symm

/-! ### The lower half of the nested-volume representation -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem exitTrunc_le_exitNat {C : Finset V} {N : ℕ} {X : ℕ → V}
    (hX : LatticeProb.Graph.exitTime (C : Set V) X ≠ ⊤) :
    exitTrunc (C : Set V) N X ≤ (LatticeProb.Graph.exitTime (C : Set V) X).toNat := by
  classical
  by_cases h : X ∈ stayIn (C : Set V) N
  · rw [exitTrunc, if_pos h]
    by_contra hcon
    exact (notMem_stayIn_of_le hX (by omega)) h
  · rw [exitTrunc_of_notMem h]

/-- **The lower half of `thm:nested-vol`.**  Every finite set from which the
walk escapes contributes its electrical sum to the odometer. -/
theorem ofReal_sum_le_odometerLimit [Infinite V] (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (σ : V → ℝ) (o : V) (C : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V)) :
    ENNReal.ofReal (∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * (σ v - 1))
      ≤ RWRS.odometerLimit G σ o := by
  classical
  set ξ : V → ℝ := RWRS.excess σ with hξ
  set μ : Measure (ℕ → V) := RWRS.walkLaw G o with hμ
  -- the truncated exit values are dominated by the odometer
  have hstop : ∀ N : ℕ,
      ENNReal.ofReal (∫ X, RWRS.payoff G ξ (exitTrunc (C : Set V) N X) X ∂μ)
        ≤ RWRS.odometerLimit G σ o := by
    intro N
    have hmem := integral_payoff_exitTrunc_mem hdeg ξ C N o
    have hle := (odometer_isLUB hG σ N o).1 _ hmem
    exact le_trans (ENNReal.ofReal_le_ofReal hle)
      (le_iSup (fun n => ENNReal.ofReal (RWRS.odometer G σ n o)) N)
  -- dominated convergence towards the value at the exit
  have hfin := LatticeProb.Graph.ae_exitTime_ne_top hdeg C hesc o
  rw [← walkLaw_eq_lib o] at hfin
  have hbdd : Integrable
      (fun X => stepBound G ξ C
        * (((LatticeProb.Graph.exitTime (C : Set V) X).toNat : ℕ) : ℝ)) μ := by
    have := LatticeProb.Graph.integrable_exitNat hdeg C hesc o
    rw [← walkLaw_eq_lib o] at this
    exact this.const_mul _
  have hconv : Filter.Tendsto
      (fun N : ℕ => ∫ X, RWRS.payoff G ξ (exitTrunc (C : Set V) N X) X ∂μ)
      Filter.atTop
      (nhds (∫ X, RWRS.payoffAtExit G ξ (C : Set V) X ∂μ)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence _
      (fun N => (measurable_of_dependsUpTo
        (dependsUpTo_payoff_exitTrunc ξ C N)).aestronglyMeasurable) hbdd ?_ ?_
    · intro N
      filter_upwards [hfin] with X hX
      have hle := exitTrunc_le_exitNat (C := C) (N := N) hX
      have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := C)
        (n := exitTrunc (C : Set V) N X) (X := X)
        (fun k hk => mem_of_lt_exitTrunc C N X hk)
      have h2 : ((exitTrunc (C : Set V) N X : ℕ) : ℝ)
          ≤ (((LatticeProb.Graph.exitTime (C : Set V) X).toNat : ℕ) : ℝ) := by
        exact_mod_cast hle
      have h3 : (0 : ℝ) ≤ stepBound G ξ C := stepBound_nonneg ξ C
      rw [Real.norm_eq_abs]
      nlinarith
    · filter_upwards [hfin] with X hX
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      refine ⟨(LatticeProb.Graph.exitTime (C : Set V) X).toNat, fun N hN => ?_⟩
      rw [RWRS.payoffAtExit, exitTime_eq_lib,
        exitTrunc_of_notMem (notMem_stayIn_of_le hX hN)]
  -- pass to the limit
  have hlim : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (∫ X, RWRS.payoff G ξ (exitTrunc (C : Set V) N X) X ∂μ))
      Filter.atTop
      (nhds (ENNReal.ofReal (∫ X, RWRS.payoffAtExit G ξ (C : Set V) X ∂μ))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hconv
  have hgoal := le_of_tendsto hlim (Filter.Eventually.of_forall hstop)
  rwa [integral_payoffAtExit_eq hdeg C hesc ξ o] at hgoal

/-! ### The form the nested-volume representation uses -/

/-- The lower half of `thm:nested-vol` on a connected infinite graph, with no
measurable structure assumed: the discrete one is supplied, and the vertex set
is countable because the graph is connected and locally finite. -/
theorem ofReal_sum_le_odometerLimit' {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    [Infinite V] (hG : G.Connected) (σ : V → ℝ) (o : V) (C : Finset V) :
    ENNReal.ofReal (∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * (σ v - 1))
      ≤ RWRS.odometerLimit G σ o := by
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
  have hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (C : Set V) := by
    intro x
    obtain ⟨q, hq⟩ : ∃ q : V, q ∉ C := by
      by_contra hcon
      have hsub : (Set.univ : Set V) ⊆ (C : Set V) := by
        intro z _
        by_contra hz
        exact hcon ⟨z, hz⟩
      exact (Set.infinite_univ (α := V)) (Set.Finite.subset C.finite_toSet hsub)
    obtain ⟨p⟩ := hG.preconnected x q
    exact ⟨q, p, by simpa using hq⟩
  exact ofReal_sum_le_odometerLimit hG hdeg σ o C hesc

end RWRS.Support
