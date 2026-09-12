/-
The four clauses of `prop:finite-vol`.

The value `v_K` vanishes off `K`, every connected subset of `K` through the
source contributes its electrical sum to `v_K(o)`, and on the active component
of `o` the value is the exit payoff.  Together these say that `v_K(o)` is the
largest of `0` and the electrical sums.
-/
import RWRS.Support.ExitValue
import RWRS.Support.Component

namespace RWRS.Support

open MeasureTheory LatticeProb.Graph LatticeProb.Network
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V] [DecidableEq V]

/-! ### The value vanishes off `K` -/

/-- Off `K` the exit time is zero, so every admissible rule stops at once. -/
theorem valueExit_eq_zero_of_notMem_set (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ)
    (K : Finset V) (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    {x : V} (hx : x ∉ K) : RWRS.valueExit G ξ (K : Set V) x = 0 := by
  classical
  refine le_antisymm ?_ (zero_le_valueExit hdeg ξ K hesc x)
  refine csSup_le ⟨0, zero_mem_stopValuesExit ξ _ x⟩ ?_
  rintro a ⟨τ, hτ, hτle, rfl⟩
  have hstart := LatticeProb.Graph.ae_walkLaw_start (G := G) x
  rw [← walkLaw_eq_lib x] at hstart
  have hae : ∀ᵐ X ∂(RWRS.walkLaw G x), RWRS.payoff G ξ (τ X) X = 0 := by
    filter_upwards [hstart] with X hX
    have h0 : LatticeProb.Graph.exitTime (K : Set V) X = 0 :=
      LatticeProb.Graph.exitTime_eq_natCast_of (K : Set V) (n := 0)
        (by rw [hX]; exact_mod_cast hx) (by omega)
    have hτ0 : τ X = 0 := by
      have hle : (τ X : ℕ∞) ≤ LatticeProb.Graph.exitTime (K : Set V) X := hτle X
      rw [h0] at hle
      exact_mod_cast Nat.le_zero.1 (by exact_mod_cast hle)
    rw [hτ0]
    rfl
  rw [integral_congr_ae hae, integral_zero]

/-! ### Every connected subset contributes -/

/-- **Every connected subset of `K` through the source contributes its
electrical sum to the value.**  The truncated exit times of `C` are admissible
rules for `K`, and their values converge to the exit payoff of `C`. -/
theorem sum_killedGreen_le_valueExit (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ)
    (K : Finset V) (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (C : Finset V) (hCK : C ⊆ K) (o : V) :
    ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * ξ v
      ≤ RWRS.valueExit G ξ (K : Set V) o := by
  classical
  have hCK' : (C : Set V) ⊆ (K : Set V) := by exact_mod_cast hCK
  have hescC : ∀ z : V, ∃ (r : V) (_ : G.Walk z r), r ∉ (C : Set V) := by
    intro z
    obtain ⟨r, p, hr⟩ := hesc z
    exact ⟨r, p, fun hc => hr (hCK' hc)⟩
  have hCle : ∀ X : ℕ → V,
      LatticeProb.Graph.exitTime (C : Set V) X ≤ LatticeProb.Graph.exitTime (K : Set V) X := by
    intro X
    refine sInf_le_sInf ?_
    rintro t ⟨n, rfl, hn⟩
    exact ⟨n, rfl, fun hc => hn (hCK' hc)⟩
  have hadm : ∀ (N : ℕ) (X : ℕ → V),
      ((exitTrunc (C : Set V) N X : ℕ) : ℕ∞)
        ≤ LatticeProb.Graph.exitTime (K : Set V) X := by
    intro N X
    by_cases h : X ∈ stayIn (C : Set V) N
    · rw [exitTrunc, if_pos h]
      have hK : X ∈ stayIn (K : Set V) N := fun j hj => hCK' (h j hj)
      rw [stayIn_eq_lt_exitTime] at hK
      exact le_of_lt hK
    · rw [exitTrunc_of_notMem h]
      have hfin : LatticeProb.Graph.exitTime (C : Set V) X ≠ ⊤ := by
        intro hc
        exact h ((LatticeProb.Graph.exitTime_eq_top_iff (C : Set V) X).mp hc N)
      rw [ENat.coe_toNat hfin]
      exact hCle X
  set μ : Measure (ℕ → V) := RWRS.walkLaw G o with hμ
  have hstop : ∀ N : ℕ,
      ∫ X, RWRS.payoff G ξ (exitTrunc (C : Set V) N X) X ∂μ
        ≤ RWRS.valueExit G ξ (K : Set V) o := by
    intro N
    refine le_csSup (bddAbove_stopValuesExit hdeg ξ K hesc o) ?_
    exact ⟨exitTrunc (C : Set V) N, isStopping_exitTrunc (C : Set V) N, hadm N, rfl⟩
  have hfin := LatticeProb.Graph.ae_exitTime_ne_top hdeg C hescC o
  rw [← walkLaw_eq_lib o] at hfin
  have hbdd : Integrable
      (fun X => stepBound G ξ C
        * (((LatticeProb.Graph.exitTime (C : Set V) X).toNat : ℕ) : ℝ)) μ := by
    have := LatticeProb.Graph.integrable_exitNat hdeg C hescC o
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
  have hgoal := le_of_tendsto hconv (Filter.Eventually.of_forall hstop)
  rwa [integral_payoffAtExit_eq hdeg C hescC ξ o] at hgoal

/-! ### The active component -/

open scoped Classical in
/-- `D_K(o)`, the connected component of `o` in `{x ∈ K : v_K(x) > 0}`, as a
finite set. -/
noncomputable def activeComp (G : SimpleGraph V) [G.LocallyFinite]
    (ξ : V → ℝ) (K : Finset V) (o : V) : Finset V :=
  K.filter (fun z => z ∈ RWRS.compIn G (RWRS.activeSet G ξ (K : Set V)) o)

omit [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem coe_activeComp (ξ : V → ℝ) (K : Finset V) (o : V) :
    (activeComp G ξ K o : Set V) = RWRS.compIn G (RWRS.activeSet G ξ (K : Set V)) o := by
  classical
  ext z
  simp only [activeComp, Finset.coe_filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    exact ⟨by exact_mod_cast (compIn_subset _ _ h).1, h⟩

omit [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem activeComp_subset (ξ : V → ℝ) (K : Finset V) (o : V) : activeComp G ξ K o ⊆ K := by
  classical
  exact Finset.filter_subset _ _

omit [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem mem_activeComp (ξ : V → ℝ) (K : Finset V) {o : V}
    (ho : o ∈ RWRS.activeSet G ξ (K : Set V)) : o ∈ activeComp G ξ K o := by
  have : o ∈ (activeComp G ξ K o : Set V) := by
    rw [coe_activeComp]; exact mem_compIn_self ho
  exact_mod_cast this

omit [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem activeComp_pos (ξ : V → ℝ) (K : Finset V) (o : V) {x : V}
    (hx : x ∈ activeComp G ξ K o) : 0 < RWRS.valueExit G ξ (K : Set V) x := by
  have hx' : x ∈ (activeComp G ξ K o : Set V) := by exact_mod_cast hx
  rw [coe_activeComp] at hx'
  exact (compIn_subset _ _ hx').2

theorem activeComp_bdry (hdeg : ∀ v : V, 0 < G.degree v) (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) (o : V) {x y : V}
    (hx : x ∈ activeComp G ξ K o) (hadj : G.Adj x y) (hy : y ∉ activeComp G ξ K o) :
    RWRS.valueExit G ξ (K : Set V) y = 0 := by
  by_cases hyK : y ∈ K
  · by_contra hne
    have hpos : 0 < RWRS.valueExit G ξ (K : Set V) y :=
      lt_of_le_of_ne (zero_le_valueExit hdeg ξ K hesc y) (Ne.symm hne)
    have hyA : y ∈ RWRS.activeSet G ξ (K : Set V) := ⟨by exact_mod_cast hyK, hpos⟩
    have hx' : x ∈ (activeComp G ξ K o : Set V) := by exact_mod_cast hx
    rw [coe_activeComp] at hx'
    have : y ∈ (activeComp G ξ K o : Set V) := by
      rw [coe_activeComp]
      exact mem_compIn_of_adj hx' hadj hyA
    exact hy (by exact_mod_cast this)
  · exact valueExit_eq_zero_of_notMem_set hdeg ξ K hesc hyK

omit [MeasurableSingletonClass V] [Countable V] [DecidableEq V] in
theorem connected_activeComp (ξ : V → ℝ) (K : Finset V) {o : V}
    (ho : o ∈ RWRS.activeSet G ξ (K : Set V)) :
    (G.induce (activeComp G ξ K o : Set V)).Connected := by
  rw [coe_activeComp]
  exact connected_induce_compIn ho

/-! ### The value on the active component, and the supremum -/

/-- **The third clause of `prop:finite-vol`.**  At a source of positive value
the value is the expected payoff at the exit from the active component. -/
theorem valueExit_eq_integral_activeComp (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) {o : V}
    (ho : o ∈ RWRS.activeSet G ξ (K : Set V)) :
    Integrable (fun X => RWRS.payoffAtExit G ξ
        (RWRS.compIn G (RWRS.activeSet G ξ (K : Set V)) o) X) (RWRS.walkLaw G o) ∧
      RWRS.valueExit G ξ (K : Set V) o
        = ∫ X, RWRS.payoffAtExit G ξ
            (RWRS.compIn G (RWRS.activeSet G ξ (K : Set V)) o) X ∂(RWRS.walkLaw G o) := by
  classical
  set D : Finset V := activeComp G ξ K o with hD
  have hDcoe : (D : Set V) = RWRS.compIn G (RWRS.activeSet G ξ (K : Set V)) o :=
    coe_activeComp ξ K o
  have hDK : D ⊆ K := activeComp_subset ξ K o
  have hoD : o ∈ D := mem_activeComp ξ K ho
  obtain ⟨q, -, hq⟩ := hesc o
  have hqD : q ∉ D := fun hc => hq (by exact_mod_cast hDK hc)
  have hescD : ∀ z : V, ∃ (r : V) (_ : G.Walk z r), r ∉ (D : Set V) := by
    intro z
    obtain ⟨r, p, hr⟩ := hesc z
    exact ⟨r, p, fun hc => hr (by exact_mod_cast hDK (by exact_mod_cast hc))⟩
  have hkey := valueExit_eq_exitValue hG hdeg ξ K hesc D hDK
    (fun x hx => activeComp_pos ξ K o hx)
    (fun x hx y hadj hy => activeComp_bdry hdeg ξ K hesc o hx hadj hy) hqD hoD
  refine ⟨?_, ?_⟩
  · rw [← hDcoe, walkLaw_eq_lib o]
    exact integrable_payoffAtExit hdeg ξ D hescD o
  · rw [hkey, exitValue, hDcoe, walkLaw_eq_lib o]

/-- The value at the source is itself `0` or one of the electrical sums. -/
theorem valueExit_mem_insert_zero (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) {o : V} (hoK : o ∈ K) :
    RWRS.valueExit G ξ (K : Set V) o ∈ insert (0 : ℝ)
      {a : ℝ | ∃ C : Finset V, C ⊆ K ∧ (G.induce (C : Set V)).Connected ∧ o ∈ C ∧
        a = ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * ξ v} := by
  classical
  by_cases ho : o ∈ RWRS.activeSet G ξ (K : Set V)
  · right
    set D : Finset V := activeComp G ξ K o with hD
    have hDcoe : (D : Set V) = RWRS.compIn G (RWRS.activeSet G ξ (K : Set V)) o :=
      coe_activeComp ξ K o
    have hDK : D ⊆ K := activeComp_subset ξ K o
    have hoD : o ∈ D := mem_activeComp ξ K ho
    have hescD : ∀ z : V, ∃ (r : V) (_ : G.Walk z r), r ∉ (D : Set V) := by
      intro z
      obtain ⟨r, p, hr⟩ := hesc z
      exact ⟨r, p, fun hc => hr (by exact_mod_cast hDK (by exact_mod_cast hc))⟩
    refine ⟨D, hDK, connected_activeComp ξ K ho, hoD, ?_⟩
    have h3 := (valueExit_eq_integral_activeComp hG hdeg ξ K hesc ho).2
    rw [h3, ← hDcoe, integral_payoffAtExit_eq hdeg D hescD ξ o]
  · left
    exact valueExit_eq_zero_of_not_mem_activeSet hdeg ξ K hesc hoK ho

/-- **The fourth clause of `prop:finite-vol`.**  The value at the source is the
least upper bound of `0` and of the electrical sums over the connected subsets
of `K` through the source. -/
theorem isLUB_valueExit (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (ξ : V → ℝ) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) {o : V} (hoK : o ∈ K) :
    IsLUB (insert (0 : ℝ)
        {a : ℝ | ∃ C : Finset V, C ⊆ K ∧ (G.induce (C : Set V)).Connected ∧ o ∈ C ∧
          a = ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * ξ v})
      (RWRS.valueExit G ξ (K : Set V) o) := by
  classical
  have hub : ∀ a ∈ insert (0 : ℝ)
      {a : ℝ | ∃ C : Finset V, C ⊆ K ∧ (G.induce (C : Set V)).Connected ∧ o ∈ C ∧
        a = ∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * ξ v},
      a ≤ RWRS.valueExit G ξ (K : Set V) o := by
    rintro a (rfl | ⟨C, hCK, -, -, rfl⟩)
    · exact zero_le_valueExit hdeg ξ K hesc o
    · exact sum_killedGreen_le_valueExit hdeg ξ K hesc C hCK o
  have hmem := valueExit_mem_insert_zero hG hdeg ξ K hesc hoK
  exact ⟨hub, fun b hb => hb hmem⟩

end RWRS.Support
