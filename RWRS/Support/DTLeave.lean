/-
Two elementary facts behind the constants of Step 1: a centred law puts less
than full mass below any negative level, and the walk leaves a finite set so
soon that staying in it up to a large time has small probability.
-/
import RWRS.Support.DTWalkGood
import RWRS.Support.Truncation

namespace RWRS.Support

open MeasureTheory LatticeProb Filter
open scoped Classical ENNReal

/-- **A centred law puts less than full mass below a negative level.** -/
theorem measure_Iic_lt_one {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h0 : RWRS.extMean ν = 0) {ε : ℝ} (hε : 0 < ε) : ν (Set.Iic (-ε)) < 1 := by
  by_contra hcon
  have h1 : ν (Set.Iic (-ε)) = 1 := le_antisymm prob_le_one (not_lt.1 hcon)
  have hae : ∀ᵐ z ∂ν, z ≤ -ε := by
    rw [MeasureTheory.ae_iff]
    have hset : {z : ℝ | ¬ z ≤ -ε} = (Set.Iic (-ε))ᶜ := by
      ext z
      simp
    rw [hset, MeasureTheory.measure_compl measurableSet_Iic (by rw [h1]; exact ENNReal.one_ne_top),
      h1, measure_univ, tsub_self]
  have hint := RWRS.Support.integrable_id_of_extMean_zero h0
  have hle : ∫ z, z ∂ν ≤ ∫ _z : ℝ, (-ε) ∂ν :=
    MeasureTheory.integral_mono_ae hint (MeasureTheory.integrable_const _) hae
  rw [RWRS.Support.integral_id_zero h0, MeasureTheory.integral_const] at hle
  simp only [probReal_univ, smul_eq_mul, one_mul] at hle
  linarith

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [G.LocallyFinite] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable V] [Infinite V]

omit [DecidableEq V] [Infinite V] in
/-- **The event of staying in a finite set is eventually small.** -/
theorem exists_N_stayIn_le (hdeg : ∀ v : V, 0 < G.degree v) (K : Finset V)
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V)) (o : V)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ N : ℕ, (LatticeProb.Graph.walkLaw G o)
      (LatticeProb.Graph.stayIn (K : Set V) N) ≤ η := by
  have hmeas : ∀ n : ℕ, MeasurableSet (LatticeProb.Graph.stayIn (K : Set V) n) := by
    intro n
    have hset : LatticeProb.Graph.stayIn (K : Set V) n
        = ⋂ j ∈ Finset.range (n + 1), {X : ℕ → V | X j ∈ K} := by
      ext X
      simp [LatticeProb.Graph.stayIn, Finset.mem_range]
    rw [hset]
    refine MeasurableSet.biInter (Finset.countable_toSet _) fun j _ => ?_
    have hm : MeasurableSet ((K : Set V)) := K.finite_toSet.measurableSet
    have heq : {X : ℕ → V | X j ∈ K} = (fun X : ℕ → V => X j) ⁻¹' ((K : Set V)) := rfl
    rw [heq]
    exact (measurable_pi_apply j) hm
  have hanti : Antitone (fun n : ℕ => LatticeProb.Graph.stayIn (K : Set V) n) :=
    fun _ _ hmn => LatticeProb.Graph.stayIn_antitone _ hmn
  have hinter : (⋂ n : ℕ, LatticeProb.Graph.stayIn (K : Set V) n)
      = {X : ℕ → V | LatticeProb.Graph.exitTime (K : Set V) X = ⊤} := by
    ext X
    rw [Set.mem_iInter, Set.mem_setOf_eq, LatticeProb.Graph.exitTime_eq_top_iff]
  have hnull : (LatticeProb.Graph.walkLaw G o)
      {X : ℕ → V | LatticeProb.Graph.exitTime (K : Set V) X = ⊤} = 0 := by
    have hae := LatticeProb.Graph.ae_exitTime_ne_top hdeg K hesc o
    rw [MeasureTheory.ae_iff] at hae
    simpa using hae
  have htend := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := LatticeProb.Graph.walkLaw G o)
    (s := fun n : ℕ => LatticeProb.Graph.stayIn (K : Set V) n)
    (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, by simp⟩
  rw [hinter, hnull] at htend
  have hev := htend.eventually (gt_mem_nhds hη)
  obtain ⟨N, hN⟩ := hev.exists
  exact ⟨N, le_of_lt hN⟩

end RWRS.Support
