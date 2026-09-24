import RWRS.Support.DTAgreement

/-!
# Converting `ℕ∞` stage-time bounds to `ℕ`

The stage recursion records its times in `ℕ∞`; the walk-good event and the
capped rule compare them with the horizon `N`.  This module provides the
strict conversion used throughout the Step-1 assembly.
-/

namespace RWRS.Support

open MeasureTheory

/-- **A stage time strictly below the horizon is strictly below it as a `ℕ`.** -/
theorem toNat_lt_of_lt_coe (t : ℕ∞) (N : ℕ) (h : t < (N : ℕ∞)) : t.toNat < N := by
  have hne : t ≠ ⊤ := fun htop => absurd (htop ▸ h) (by simp)
  have h1 : t.toNat ≤ N := by
    have h2 : t ≤ (N : ℕ∞) := le_of_lt h
    have h3 : (N : ℕ∞).toNat = N := ENat.toNat_coe N
    have := ENat.toNat_le_toNat h2 (by simp)
    rwa [h3] at this
  rcases Nat.lt_or_ge t.toNat N with h' | h'
  · exact h'
  · exfalso
    have h6 : t.toNat = N := Nat.le_antisymm h1 h'
    have h7 : t = (t.toNat : ℕ∞) := ((ENat.coe_toNat_eq_self).mpr hne).symm
    rw [h6] at h7
    rw [h7] at h
    exact absurd h (by simp)

end RWRS.Support