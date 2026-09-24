import RWRS.Support.DTNoHit

/-!
# The integral partition over the stage hit events

For fixed blocks, the scenery integral of any integrable function splits
over the disjoint stage hit events and the no-hit event.  This is the
per-trajectory decomposition of Step 1: conditionally on the walk, the
value at the capped rule is read at the stage times on the hit events.
-/

open scoped Classical
open MeasureTheory

namespace RWRS.Support

variable {V : Type*} [DecidableEq V] [MeasurableSpace V]

omit [DecidableEq V] [MeasurableSpace V] in
/-- **The integral splits over the stage hit events and the no-hit event.**
For fixed blocks and any integrable function of the scenery, the integral
over the scenery space is the sum over the disjoint stage hit events plus
the no-hit event. -/
theorem integral_partition_hitEvent_add_noHit (C : ℕ → Finset V) (ε : ℝ) (n : ℕ)
    {μ : Measure (V → ℝ)}
    (f : (V → ℝ) → ℝ) (hf : Integrable f μ) :
    ∫ ξ, f ξ ∂μ
      = ∑ i ∈ Finset.range (n), ∫ ξ, (hitEvent C ε i).indicator f ξ ∂μ
        + ∫ ξ, ({ξ : V → ℝ | ∀ j < n, ξ ∉ trapEvent (C j) ε}).indicator f ξ ∂μ := by
  have hpart : ∀ ξ, f ξ = (∑ i ∈ Finset.range (n), (hitEvent C ε i).indicator f ξ)
      + ({ξ : V → ℝ | ∀ j < n, ξ ∉ trapEvent (C j) ε}).indicator f ξ := by
    intro ξ
    by_cases hex : ∃ i ∈ Finset.range (n), ξ ∈ hitEvent C ε i
    · obtain ⟨i, hi⟩ := hex
      set F := {i ∈ Finset.range (n) | ξ ∈ hitEvent C ε i} with hFdef
      have hFne : F.Nonempty := ⟨i, Finset.mem_filter.2 hi⟩
      set i₀ := F.min' hFne with hi₀def
      have hi₀mem : i₀ ∈ F := Finset.min'_mem F hFne
      obtain ⟨hi₀lt, hi₀hit⟩ := Finset.mem_filter.1 hi₀mem
      have hi₀trap : ξ ∈ trapEvent (C i₀) ε := hi₀hit.1
      have hsum : ∑ i' ∈ Finset.range (n), (hitEvent C ε i').indicator f ξ
          = f ξ := by
        have hsingle : ∑ i' ∈ Finset.range (n), (hitEvent C ε i').indicator f ξ
            = (hitEvent C ε i₀).indicator f ξ :=
          Finset.sum_eq_single i₀
            (fun i' hi' hne => by
              rcases Nat.lt_or_ge i' i₀ with hlt | hge
              · have hnot : ξ ∉ hitEvent C ε i' := by
                  intro hmem
                  have : i' ∈ F := Finset.mem_filter.2 ⟨hi', hmem⟩
                  have : F.min' hFne ≤ i' := Finset.min'_le F i' this
                  omega
                rw [Set.indicator_of_notMem hnot]
              · have hnot : ξ ∉ hitEvent C ε i' := by
                  intro hmem
                  obtain ⟨_, hb⟩ := (hmem : ξ ∈ trapEvent (C i') ε ∩ _)
                  exact Set.mem_setOf.1 hb i₀ (by omega) hi₀trap
                rw [Set.indicator_of_notMem hnot])
            (fun hcon => absurd (Finset.mem_filter.1 hi₀mem).1 hcon)
        rw [hsingle, Set.indicator_of_mem hi₀hit]
      rw [hsum]
      rw [Set.indicator_of_notMem (fun hmem =>
        Set.mem_setOf.1 (hmem : ξ ∈ {ξ' : V → ℝ | ∀ j < n, ξ' ∉ trapEvent (C j) ε})
          i₀ (Finset.mem_range.1 hi₀lt) hi₀trap)]
      ring
    · have hnohit : ξ ∈ {ξ : V → ℝ | ∀ j < n, ξ ∉ trapEvent (C j) ε} := by
        by_contra hcon
        have hex' : ∃ j < n, ξ ∈ trapEvent (C j) ε := by
          by_contra hno
          exact hcon (Set.mem_setOf.2 (by
            intro j hj
            by_contra htrap
            exact hno ⟨j, hj, htrap⟩))
        obtain ⟨j, hjlt, hjtrap⟩ := hex'
        -- minimal such j
        have hexn : ∃ t, t < n ∧ ξ ∈ trapEvent (C t) ε := ⟨j, hjlt, hjtrap⟩
        set j₀ := Nat.find hexn with hj₀def
        have hj₀lt : j₀ < n := (Nat.find_spec hexn).1
        have hj₀trap : ξ ∈ trapEvent (C j₀) ε := (Nat.find_spec hexn).2
        have hhit : ξ ∈ hitEvent C ε j₀ :=
          ⟨hj₀trap, fun j hj jtrap => absurd ⟨by omega, jtrap⟩ (Nat.find_min hexn hj)⟩
        exact hex ⟨j₀, Finset.mem_range.2 hj₀lt, hhit⟩
      have hsum : ∑ i' ∈ Finset.range (n), (hitEvent C ε i').indicator f ξ = 0 := by
        refine Finset.sum_eq_zero fun i' hi' => ?_
        rw [Set.indicator_of_notMem (fun hmem => hex ⟨i', hi', hmem⟩)]
      rw [hsum, Set.indicator_of_mem hnohit]
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpart)]
  have hint1 : Integrable (fun ξ => ∑ i ∈ Finset.range (n), (hitEvent C ε i).indicator f ξ) μ :=
    integrable_finsetSum _ fun i _ => Integrable.indicator hf (measurableSet_hitEvent C ε i)
  have hint2 : Integrable
      (fun ξ => ({ξ : V → ℝ | ∀ j < n, ξ ∉ trapEvent (C j) ε}).indicator f ξ) μ :=
    Integrable.indicator hf (measurableSet_noHit C ε (n))
  rw [integral_add hint1 hint2, integral_finsetSum _ fun i _ =>
    Integrable.indicator hf (measurableSet_hitEvent C ε i)]

end RWRS.Support