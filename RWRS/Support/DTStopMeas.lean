/-
Measurability of stopping times and of the shifted trajectory.

For an `IsWalkStoppingE` stopping time `τ`, the level sets `{τ = n}` are
measurable (the indicator depends on the trajectory only up to `n`), hence
`X ↦ (τ X).toNat` is measurable, and so is the shifted trajectory
`X ↦ shiftPath (τ X).toNat X`.
-/
import LatticeProb.Graph.MarkovAE
import LatticeProb.Graph.PathSpace

open LatticeProb LatticeProb.Graph MeasureTheory
open scoped ENNReal

namespace RWRS.Support

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- **The event that a stopping time takes a given finite value is
measurable.** -/
theorem measurableSet_eq_of_isWalkStopping (τ : (ℕ → V) → ℕ∞)
    (hτ : IsWalkStoppingE τ) (n : ℕ) :
    MeasurableSet {X : ℕ → V | τ X = (n : ℕ∞)} := by
  classical
  set ind : (ℕ → V) → ℝ :=
    fun X => Set.indicator {Z : ℕ → V | τ Z = (n : ℕ∞)} (fun _ => (1 : ℝ)) X with hind
  have hdep : DependsUpTo n ind := by
    intro X Y hXY
    by_cases h : τ X = (n : ℕ∞)
    · have hY : τ Y = (n : ℕ∞) := hτ n X Y hXY h
      simp [hind, h, hY, Set.indicator_of_mem]
    · have hY : τ Y ≠ (n : ℕ∞) := by
        intro hY
        exact h (hτ n Y X (fun k hk => (hXY k hk).symm) hY)
      simp [hind, h, hY]
  have hmeas : Measurable ind := measurable_of_dependsUpTo hdep
  have hpre : {X : ℕ → V | τ X = (n : ℕ∞)}
      = ind ⁻¹' {(1 : ℝ)} := by
    ext X
    simp [hind, Set.indicator_apply]
  rw [hpre]
  exact hmeas (measurableSet_singleton _)

/-- **The truncated value of a stopping time is measurable.** -/
theorem measurable_stopNat (τ : (ℕ → V) → ℕ∞) (hτ : IsWalkStoppingE τ) :
    Measurable fun X : ℕ → V => (τ X).toNat := by
  refine measurable_to_countable' fun n => ?_
  have htop : MeasurableSet {X : ℕ → V | τ X = ⊤} := by
    have hU : {X : ℕ → V | τ X = ⊤}
        = (⋃ m : ℕ, {X : ℕ → V | τ X = (m : ℕ∞)})ᶜ := by
      ext X
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      constructor
      · intro h m hm
        simp only [Set.mem_setOf_eq] at h hm
        rw [h] at hm
        exact absurd hm (by simp)
      · intro hc
        by_contra hne
        obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hne
        exact hc m hm.symm
    rw [hU]
    exact MeasurableSet.compl (MeasurableSet.iUnion fun m =>
      measurableSet_eq_of_isWalkStopping τ hτ m)
  match n with
  | 0 =>
      have h0 : (fun X : ℕ → V => (τ X).toNat) ⁻¹' {0}
          = {X : ℕ → V | τ X = ⊤} ∪ {X : ℕ → V | τ X = (0 : ℕ∞)} := by
        ext X
        simp only [ENat.toNat_eq_zero, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_union, Set.mem_setOf_eq]
        tauto
      rw [h0]
      exact htop.union (measurableSet_eq_of_isWalkStopping τ hτ 0)
  | (m + 1) =>
      have h1 : (fun X : ℕ → V => (τ X).toNat) ⁻¹' {m + 1}
          = {X : ℕ → V | τ X = ((m + 1 : ℕ) : ℕ∞)} := by
        ext X
        by_cases hX : τ X = ⊤
        · simp only [hX, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_setOf_eq]
          have h0 : ¬ ((0 : ℕ) = m + 1) := by omega
          simp only [ENat.toNat_top]
          exact ⟨fun h => absurd h h0,
            fun h : (⊤ : ℕ∞) = ↑(m + 1) =>
              (ENat.coe_ne_top (m + 1) h.symm).elim⟩
        · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hX
          simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
          rw [← hk]
          simp only [ENat.toNat_coe]
          exact ENat.coe_inj.symm
      rw [h1]
      exact measurableSet_eq_of_isWalkStopping τ hτ (m + 1)

/-- **The shifted trajectory at a stopping time is measurable.** -/
theorem measurable_shiftPath_stop (τ : (ℕ → V) → ℕ∞) (hτ : IsWalkStoppingE τ) :
    Measurable fun X : ℕ → V => shiftPath (τ X).toNat X := by
  have h1 : Measurable
      fun p : (ℕ → V) × ℕ => shiftPath p.2 p.1 :=
    measurable_from_prod_countable_left fun n => measurable_shiftPath n
  exact h1.comp ((Measurable.prodMk measurable_id (measurable_stopNat τ hτ)))

end RWRS.Support
