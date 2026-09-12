/-
The Wald--Bellman equation for the finite-volume value `v_K` of
`prop:finite-vol`, and the pieces its proof needs: the first-step decomposition
of an integrable functional, the behaviour of the payoff and of the exit time
under prepending a step, and the reduction of the supremum defining `v_K` to
the stopping times that are bounded.
-/
import RWRS.Support.FiniteVolume

namespace RWRS.Support

open MeasureTheory LatticeProb.Graph
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

/-! ### Prepending a step -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The trajectory is in `C` before the exit time and outside it at the exit
time, when the exit time is finite. -/
theorem exitNat_spec {C : Set V} {X : ℕ → V} (hX : LatticeProb.Graph.exitTime C X ≠ ⊤) :
    X ((LatticeProb.Graph.exitTime C X).toNat) ∉ C ∧ ∀ j < (LatticeProb.Graph.exitTime C X).toNat, X j ∈ C := by
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hX
  have hrr : (LatticeProb.Graph.exitTime C X).toNat = r := by rw [← hr]; simp
  refine ⟨?_, ?_⟩
  · rw [hrr]
    have hnot : X ∉ stayIn C r := by
      rw [stayIn_eq_lt_exitTime, Set.mem_setOf_eq, ← hr]
      exact_mod_cast lt_irrefl r
    by_contra hc
    refine hnot fun j hj => ?_
    rcases lt_or_eq_of_le hj with h | h
    · have : X ∈ stayIn C j := by
        rw [stayIn_eq_lt_exitTime, Set.mem_setOf_eq, ← hr]
        exact_mod_cast h
      exact this j le_rfl
    · rw [h]; exact hc
  · intro j hj
    rw [hrr] at hj
    have : X ∈ stayIn C j := by
      rw [stayIn_eq_lt_exitTime, Set.mem_setOf_eq, ← hr]
      exact_mod_cast hj
    exact this j le_rfl

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The exit time of a trajectory that starts with a step inside `C`. -/
theorem exitTime_cons_of_mem {C : Set V} {x : V} (hx : x ∈ C) (X : ℕ → V) :
    LatticeProb.Graph.exitTime C (RWRS.cons x X) = LatticeProb.Graph.exitTime C X + 1 := by
  by_cases h : LatticeProb.Graph.exitTime C X = ⊤
  · rw [h]
    have hall : ∀ k : ℕ, X ∈ stayIn C k := (exitTime_eq_top_iff C X).mp h
    have : ∀ k : ℕ, RWRS.cons x X ∈ stayIn C k := by
      intro k j hj
      cases j with
      | zero => exact hx
      | succ i => exact hall i i le_rfl
    rw [(exitTime_eq_top_iff C (RWRS.cons x X)).mpr this]
    simp
  · obtain ⟨hout, hin⟩ := exitNat_spec h
    set r := (LatticeProb.Graph.exitTime C X).toNat with hrdef
    have hr : LatticeProb.Graph.exitTime C X = (r : ℕ∞) := (ENat.coe_toNat h).symm
    have hout' : RWRS.cons x X (r + 1) ∉ C := hout
    have hin' : ∀ j < r + 1, RWRS.cons x X j ∈ C := by
      intro j hj
      cases j with
      | zero => exact hx
      | succ i => exact hin i (by omega)
    rw [exitTime_eq_natCast_of C hout' hin', hr]
    push_cast
    ring

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The exit time of a trajectory that starts outside `C`. -/
theorem exitTime_cons_of_notMem {C : Set V} {x : V} (hx : x ∉ C) (X : ℕ → V) :
    LatticeProb.Graph.exitTime C (RWRS.cons x X) = 0 :=
  exitTime_eq_natCast_of C (n := 0) hx (by omega)

/-! ### Measurability and integrability at a stopping time -/

omit [DecidableEq V] in
/-- A stopping time is measurable, with no bound assumed on it. -/
theorem measurable_of_isStopping {τ : (ℕ → V) → ℕ} (hτ : RWRS.IsStopping τ) :
    Measurable τ := by
  classical
  refine measurable_to_countable' fun k => ?_
  have hdep : LatticeProb.Graph.DependsUpTo k (fun X : ℕ → V => if τ X = k then (1 : ℝ) else 0) := by
    intro X Y hXY
    show (if τ X = k then (1 : ℝ) else 0) = (if τ Y = k then (1 : ℝ) else 0)
    by_cases h : τ X = k
    · rw [if_pos h, if_pos (hτ k X Y hXY h)]
    · have h' : τ Y ≠ k := fun hc => h (hτ k Y X (fun j hj => (hXY j hj).symm) hc)
      rw [if_neg h, if_neg h']
  have hm : Measurable (fun X : ℕ → V => if τ X = k then (1 : ℝ) else 0) :=
    LatticeProb.Graph.measurable_of_dependsUpTo hdep
  have hset : τ ⁻¹' {k} = (fun X : ℕ → V => if τ X = k then (1 : ℝ) else 0) ⁻¹' {(1 : ℝ)} := by
    ext X
    by_cases h : τ X = k <;> simp [h]
  rw [hset]
  exact hm (measurableSet_singleton _)

omit [DecidableEq V] in
/-- The payoff at a fixed horizon is measurable. -/
theorem measurable_payoff (ξ : V → ℝ) (n : ℕ) :
    Measurable (fun X : ℕ → V => RWRS.payoff G ξ n X) := by
  simp only [RWRS.payoff]
  refine Finset.measurable_sum _ fun k _ => ?_
  exact (measurable_of_countable
    (fun v : V => ξ v / (G.degree v : ℝ))).comp (measurable_pi_apply k)

omit [DecidableEq V] in
/-- The payoff at a stopping time is measurable. -/
theorem measurable_payoff_stopping {τ : (ℕ → V) → ℕ} (hτ : RWRS.IsStopping τ) (ξ : V → ℝ) :
    Measurable (fun X : ℕ → V => RWRS.payoff G ξ (τ X) X) := by
  have h1 : Measurable τ := measurable_of_isStopping hτ
  have h2 : Measurable (fun p : (ℕ → V) × ℕ => RWRS.payoff G ξ p.2 p.1) :=
    measurable_from_prod_countable_left fun n => measurable_payoff ξ n
  exact h2.comp (measurable_id.prodMk h1)

/-- The payoff at a stopping time bounded by the exit time of a finite set is
integrable: it is dominated by the step bound times the exit time. -/
theorem integrable_payoff_stopping (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ)
    (K : Finset V) (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    {τ : (ℕ → V) → ℕ} (hτ : RWRS.IsStopping τ)
    (hτle : ∀ X, (τ X : ℕ∞) ≤ LatticeProb.Graph.exitTime (K : Set V) X) (x : V) :
    Integrable (fun X => RWRS.payoff G ξ (τ X) X) (RWRS.walkLaw G x) := by
  classical
  set μ : Measure (ℕ → V) := RWRS.walkLaw G x with hμ
  have hbdd : Integrable
      (fun X => stepBound G ξ K
        * (((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ) : ℝ)) μ := by
    have := LatticeProb.Graph.integrable_exitNat hdeg K hesc x
    rw [← walkLaw_eq_lib x] at this
    exact this.const_mul _
  have hfin := LatticeProb.Graph.ae_exitTime_ne_top hdeg K hesc x
  rw [← walkLaw_eq_lib x] at hfin
  refine Integrable.mono' hbdd (measurable_payoff_stopping hτ ξ).aestronglyMeasurable ?_
  filter_upwards [hfin] with X hX
  have hmem : ∀ k, k < τ X → X k ∈ K := by
    intro k hk
    refine mem_of_lt_exitTime (C := (K : Set V)) ?_
    exact lt_of_lt_of_le (by exact_mod_cast hk) (hτle X)
  have h1 := abs_payoff_le (G := G) (ξ := ξ) (C := K) (n := τ X) (X := X) hmem
  have h2 : ((τ X : ℕ) : ℝ)
      ≤ (((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ) : ℝ) := by
    have : (τ X : ℕ∞) ≤ ((LatticeProb.Graph.exitTime (K : Set V) X).toNat : ℕ∞) := by
      rw [ENat.coe_toNat hX]
      exact hτle X
    exact_mod_cast this
  have h3 : (0 : ℝ) ≤ stepBound G ξ K := stepBound_nonneg ξ K
  rw [Real.norm_eq_abs]
  nlinarith

/-! ### The first-step decomposition of an integrable functional -/

/-- The first-step decomposition of an integral, for an integrable functional.
The library's version asks for a uniform bound, which the payoff at an unbounded
stopping time does not have. -/
theorem integral_walkLaw_firstStep' (x : V) (hx : 0 < G.degree x)
    (f : (ℕ → V) → ℝ) (hfm : Measurable f)
    (hf : Integrable f (LatticeProb.Graph.walkLaw G x)) :
    ∫ X, f X ∂(LatticeProb.Graph.walkLaw G x)
      = (G.degree x : ℝ)⁻¹
        * ∑ y ∈ G.neighborFinset x, ∫ X, f (LatticeProb.Graph.cons x X)
            ∂(LatticeProb.Graph.walkLaw G y) := by
  classical
  have hdne : (G.degree x : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).2 hx.ne'
  have h0 : ((G.degree x : ℝ≥0∞))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (by simp)
  have htop : ((G.degree x : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hdne
  rw [LatticeProb.Graph.walkLaw_firstStep x hx] at hf ⊢
  have hsum : Integrable f (∑ y ∈ G.neighborFinset x,
      (LatticeProb.Graph.walkLaw G y).map (LatticeProb.Graph.cons x)) :=
    (integrable_smul_measure h0 htop).1 hf
  have heach : ∀ y ∈ G.neighborFinset x, Integrable f
      ((LatticeProb.Graph.walkLaw G y).map (LatticeProb.Graph.cons x)) := by
    intro y hy
    refine hsum.mono_measure ?_
    exact Finset.single_le_sum (f := fun y =>
      (LatticeProb.Graph.walkLaw G y).map (LatticeProb.Graph.cons x))
      (fun _ _ => bot_le) hy
  rw [integral_smul_measure, integral_finsetSum_measure heach]
  have hmap : ∀ y : V, ∫ X, f X ∂((LatticeProb.Graph.walkLaw G y).map
      (LatticeProb.Graph.cons x))
      = ∫ X, f (LatticeProb.Graph.cons x X) ∂(LatticeProb.Graph.walkLaw G y) := fun y =>
    integral_map (LatticeProb.Graph.measurable_cons x).aemeasurable hfm.aestronglyMeasurable
  simp only [hmap, smul_eq_mul]
  congr 1
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-! ### The Wald--Bellman equation -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem cons_shift (X : ℕ → V) : RWRS.cons (X 0) (shift X) = X := by
  funext k
  cases k with
  | zero => rfl
  | succ k => rfl

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
/-- The exit time seen from the second step. -/
theorem exitTime_shift {C : Set V} {X : ℕ → V} (hx : X 0 ∈ C) :
    LatticeProb.Graph.exitTime C X = LatticeProb.Graph.exitTime C (shift X) + 1 := by
  conv_lhs => rw [← cons_shift X]
  exact exitTime_cons_of_mem hx _

/-- The right side of the Wald--Bellman equation `eq:vK-bellman`, before the
positive part. -/
noncomputable def bellman (G : SimpleGraph V) [G.LocallyFinite]
    (ξ : V → ℝ) (K : Set V) (x : V) : ℝ :=
  ξ x / G.degree x + (G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x, RWRS.valueExit G ξ K y

/-- The value at a site of `K` is at most the Bellman right side. -/
theorem valueExit_le_bellman (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    {x : V} (hx : x ∈ K) :
    RWRS.valueExit G ξ (K : Set V) x ≤ max 0 (bellman G ξ (K : Set V) x) := by
  classical
  refine csSup_le ⟨0, zero_mem_stopValuesExit ξ _ x⟩ ?_
  rintro a ⟨τ, hτ, hτle, rfl⟩
  by_cases h0 : τ (fun _ => x) = 0
  · have hae : ∀ᵐ X ∂(RWRS.walkLaw G x), RWRS.payoff G ξ (τ X) X = 0 := by
      have := LatticeProb.Graph.ae_walkLaw_start (G := G) x
      rw [← walkLaw_eq_lib x] at this
      filter_upwards [this] with X hX
      rw [stopping_of_zero hτ hX h0]
      rfl
    rw [integral_congr_ae hae, integral_zero]
    exact le_max_left _ _
  · have hne : ∀ X : ℕ → V, X 0 = x → τ X ≠ 0 := fun X hX => stopping_ne_zero hτ hX h0
    -- the shifted stopping time
    set τ' : (ℕ → V) → ℕ := fun X' => τ (RWRS.cons x X') - 1 with hτ'def
    have hτ'stop : RWRS.IsStopping τ' := isStopping_shift hτ x hne
    have hτ'le : ∀ X, (τ' X : ℕ∞) ≤ LatticeProb.Graph.exitTime (K : Set V) X := by
      intro X
      have h1 : (τ (RWRS.cons x X) : ℕ∞)
          ≤ LatticeProb.Graph.exitTime (K : Set V) (RWRS.cons x X) := hτle _
      rw [exitTime_cons_of_mem (by exact_mod_cast hx : x ∈ (K : Set V)) X] at h1
      have h2 : τ (RWRS.cons x X) ≠ 0 := hne _ rfl
      obtain ⟨m, hm⟩ : ∃ m, τ (RWRS.cons x X) = m + 1 := ⟨τ (RWRS.cons x X) - 1, by omega⟩
      have : τ' X = m := by simp only [hτ'def, hm]; omega
      rw [this]
      rw [hm] at h1
      have hcast : ((m + 1 : ℕ) : ℕ∞) = (m : ℕ∞) + 1 := by push_cast; ring
      rw [hcast] at h1
      exact (WithTop.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).1 h1
    -- the first-step decomposition
    have hint : Integrable (fun X => RWRS.payoff G ξ (τ X) X) (LatticeProb.Graph.walkLaw G x) := by
      have := integrable_payoff_stopping hdeg ξ K hesc hτ hτle x
      rwa [walkLaw_eq_lib x] at this
    have hfs := integral_walkLaw_firstStep' (G := G) x (hdeg x)
      (fun X => RWRS.payoff G ξ (τ X) X) (measurable_payoff_stopping hτ ξ) hint
    rw [walkLaw_eq_lib x, hfs]
    have hterm : ∀ y ∈ G.neighborFinset x,
        ∫ X, RWRS.payoff G ξ (τ (LatticeProb.Graph.cons x X)) (LatticeProb.Graph.cons x X)
            ∂(LatticeProb.Graph.walkLaw G y)
          ≤ ξ x / G.degree x + RWRS.valueExit G ξ (K : Set V) y := by
      intro y _
      have hrw : ∀ X : ℕ → V,
          RWRS.payoff G ξ (τ (LatticeProb.Graph.cons x X)) (LatticeProb.Graph.cons x X)
            = ξ x / G.degree x + RWRS.payoff G ξ (τ' X) X := by
        intro X
        rw [← cons_eq_lib]
        have h2 : τ (RWRS.cons x X) ≠ 0 := hne _ rfl
        obtain ⟨m, hm⟩ : ∃ m, τ (RWRS.cons x X) = m + 1 := ⟨τ (RWRS.cons x X) - 1, by omega⟩
        have hm' : τ' X = m := by simp only [hτ'def, hm]; omega
        rw [hm, hm', payoff_cons]
      simp only [hrw]
      have hint' : Integrable (fun X => RWRS.payoff G ξ (τ' X) X)
          (LatticeProb.Graph.walkLaw G y) := by
        have := integrable_payoff_stopping hdeg ξ K hesc hτ'stop hτ'le y
        rwa [walkLaw_eq_lib y] at this
      rw [integral_add (integrable_const _) hint']
      have : ∫ X, RWRS.payoff G ξ (τ' X) X ∂(LatticeProb.Graph.walkLaw G y)
          ≤ RWRS.valueExit G ξ (K : Set V) y := by
        refine le_csSup (bddAbove_stopValuesExit hdeg ξ K hesc y) ?_
        exact ⟨τ', hτ'stop, hτ'le, by rw [walkLaw_eq_lib y]⟩
      have hprob : IsProbabilityMeasure (LatticeProb.Graph.walkLaw G y) := by infer_instance
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      linarith
    have hsum := Finset.sum_le_sum hterm
    have hdx : (0 : ℝ) < (G.degree x : ℝ) := by exact_mod_cast hdeg x
    refine le_trans ?_ (le_max_right 0 (bellman G ξ (K : Set V) x))
    rw [bellman]
    rw [Finset.sum_add_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul] at hsum
    have hstep : (G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x,
        ∫ X, RWRS.payoff G ξ (τ (LatticeProb.Graph.cons x X)) (LatticeProb.Graph.cons x X)
            ∂(LatticeProb.Graph.walkLaw G y)
        ≤ (G.degree x : ℝ)⁻¹ * ((G.degree x : ℝ) * (ξ x / G.degree x)
            + ∑ y ∈ G.neighborFinset x, RWRS.valueExit G ξ (K : Set V) y) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    field_simp

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] in
/-- Prepending one step to a family of stopping times, with the trajectories
that start outside `K` stopped at once. -/
theorem isStopping_prepend_guard (K : Finset V) {τ : V → (ℕ → V) → ℕ}
    (hτ : ∀ y, RWRS.IsStopping (τ y)) :
    RWRS.IsStopping (fun X => if X 0 ∈ K then 1 + τ (X 1) (shift X) else 0) := by
  intro k X Y hXY hk
  have h0 : X 0 = Y 0 := hXY 0 (by omega)
  simp only at hk ⊢
  by_cases hxK : X 0 ∈ K
  · rw [if_pos hxK] at hk
    rw [if_pos (h0 ▸ hxK)]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have h1 : X 1 = Y 1 := hXY 1 (by omega)
    have hm : τ (X 1) (shift X) = m := by omega
    have h2 : τ (X 1) (shift Y) = m :=
      hτ (X 1) m (shift X) (shift Y) (fun j hj => hXY (j + 1) (by omega)) hm
    rw [← h1, h2]
    omega
  · rw [if_neg hxK] at hk
    rw [if_neg (h0 ▸ hxK)]
    omega

/-- The Bellman right side is at most the value at a site of `K`. -/
theorem bellman_le_valueExit (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    {x : V} (hx : x ∈ K) :
    bellman G ξ (K : Set V) x ≤ RWRS.valueExit G ξ (K : Set V) x := by
  classical
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hchoice : ∀ y : V, ∃ τy : (ℕ → V) → ℕ, RWRS.IsStopping τy ∧
      (∀ X, (τy X : ℕ∞) ≤ LatticeProb.Graph.exitTime (K : Set V) X) ∧
      RWRS.valueExit G ξ (K : Set V) y - ε
        < ∫ X, RWRS.payoff G ξ (τy X) X ∂(LatticeProb.Graph.walkLaw G y) := by
    intro y
    have hlt : RWRS.valueExit G ξ (K : Set V) y - ε < RWRS.valueExit G ξ (K : Set V) y := by
      linarith
    obtain ⟨a, ha, hlta⟩ := exists_lt_of_lt_csSup ⟨0, zero_mem_stopValuesExit ξ _ y⟩ hlt
    obtain ⟨τy, hτy, hτyle, rfl⟩ := ha
    exact ⟨τy, hτy, hτyle, by rwa [walkLaw_eq_lib y] at hlta⟩
  choose τy hτystop hτyle hτygt using hchoice
  set τ : (ℕ → V) → ℕ := fun X => if X 0 ∈ K then 1 + τy (X 1) (shift X) else 0 with hτdef
  have hτstop : RWRS.IsStopping τ := isStopping_prepend_guard K hτystop
  have hτle : ∀ X, (τ X : ℕ∞) ≤ LatticeProb.Graph.exitTime (K : Set V) X := by
    intro X
    by_cases hxK : X 0 ∈ K
    · have hmem : X 0 ∈ (K : Set V) := by exact_mod_cast hxK
      rw [exitTime_shift hmem]
      have h1 := hτyle (X 1) (shift X)
      simp only [hτdef, if_pos hxK]
      have hcast : ((1 + τy (X 1) (shift X) : ℕ) : ℕ∞)
          = (τy (X 1) (shift X) : ℕ∞) + 1 := by push_cast; ring
      rw [hcast]
      gcongr
    · simp only [hτdef, if_neg hxK]
      simp
  have hint : Integrable (fun X => RWRS.payoff G ξ (τ X) X) (LatticeProb.Graph.walkLaw G x) := by
    have := integrable_payoff_stopping hdeg ξ K hesc hτstop hτle x
    rwa [walkLaw_eq_lib x] at this
  have hfs := integral_walkLaw_firstStep' (G := G) x (hdeg x)
    (fun X => RWRS.payoff G ξ (τ X) X) (measurable_payoff_stopping hτstop ξ) hint
  have hterm : ∀ y ∈ G.neighborFinset x,
      ξ x / G.degree x + (RWRS.valueExit G ξ (K : Set V) y - ε)
        ≤ ∫ X, RWRS.payoff G ξ (τ (LatticeProb.Graph.cons x X)) (LatticeProb.Graph.cons x X)
            ∂(LatticeProb.Graph.walkLaw G y) := by
    intro y _
    have hstart := LatticeProb.Graph.ae_walkLaw_start (G := G) y
    have hae : ∀ᵐ X ∂(LatticeProb.Graph.walkLaw G y),
        RWRS.payoff G ξ (τ (LatticeProb.Graph.cons x X)) (LatticeProb.Graph.cons x X)
          = ξ x / G.degree x + RWRS.payoff G ξ (τy y X) X := by
      filter_upwards [hstart] with X hX
      rw [← cons_eq_lib]
      have h1 : τ (RWRS.cons x X) = 1 + τy (X 0) X := by
        simp only [hτdef, cons_zero, cons_succ, shift_cons, if_pos hx]
      rw [h1, hX, show 1 + τy y X = τy y X + 1 from Nat.add_comm _ _, payoff_cons]
    rw [integral_congr_ae hae]
    have hint' : Integrable (fun X => RWRS.payoff G ξ (τy y X) X)
        (LatticeProb.Graph.walkLaw G y) := by
      have := integrable_payoff_stopping hdeg ξ K hesc (hτystop y) (hτyle y) y
      rwa [walkLaw_eq_lib y] at this
    rw [integral_add (integrable_const _) hint']
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith [hτygt y]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul] at hsum
  have hdx : (0 : ℝ) < (G.degree x : ℝ) := by exact_mod_cast hdeg x
  have hval : ∫ X, RWRS.payoff G ξ (τ X) X ∂(LatticeProb.Graph.walkLaw G x)
      ≤ RWRS.valueExit G ξ (K : Set V) x := by
    refine le_csSup (bddAbove_stopValuesExit hdeg ξ K hesc x) ?_
    exact ⟨τ, hτstop, hτle, by rw [walkLaw_eq_lib x]⟩
  rw [hfs] at hval
  have hmul : (G.degree x : ℝ)⁻¹ * ((G.degree x : ℝ) * (ξ x / G.degree x)
      + ∑ y ∈ G.neighborFinset x, (RWRS.valueExit G ξ (K : Set V) y - ε))
      ≤ (G.degree x : ℝ)⁻¹ * ∑ y ∈ G.neighborFinset x,
        ∫ X, RWRS.payoff G ξ (τ (LatticeProb.Graph.cons x X)) (LatticeProb.Graph.cons x X)
            ∂(LatticeProb.Graph.walkLaw G y) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have hexp : (G.degree x : ℝ)⁻¹ * ((G.degree x : ℝ) * (ξ x / G.degree x)
      + ∑ y ∈ G.neighborFinset x, (RWRS.valueExit G ξ (K : Set V) y - ε))
      = bellman G ξ (K : Set V) x - ε := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul, bellman]
    field_simp
    ring
  rw [hexp] at hmul
  linarith

end RWRS.Support
