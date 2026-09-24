/-
Auxiliary facts about the exit time of a set along a trajectory: the
trajectory is outside the set at the (finite) exit time.
-/
import LatticeProb.Graph.ExitTime

open LatticeProb LatticeProb.Graph

namespace RWRS.Support

variable {V : Type*}

/-- **At its exit time the trajectory is outside the set.**  For a finite
exit time, `X` at `(exitTime C X).toNat` is not in `C`. -/
theorem exitTime_notMem_at (C : Set V) (X : ℕ → V) (h : exitTime C X ≠ ⊤) :
    X ((exitTime C X).toNat) ∉ C := by
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp h
  have hnot : X ∉ stayIn C ((exitTime C X).toNat) := notMem_stayIn_of_le h le_rfl
  by_contra hc
  refine hnot fun j hj => ?_
  rcases Nat.lt_or_ge j ((exitTime C X).toNat) with hj' | hj'
  · by_contra hmem
    have hle : exitTime C X ≤ (j : ℕ∞) := by
      have hw : (j : ℕ∞) ∈ {k : ℕ∞ | ∃ n : ℕ, (k : ℕ∞) = n ∧ X n ∉ C} :=
        ⟨j, rfl, hmem⟩
      show exitTime C X ≤ (j : ℕ∞)
      exact sInf_le hw
    rw [← hr] at hle
    have htr : (exitTime C X).toNat = r := by rw [← hr, ENat.toNat_coe]
    rw [htr] at hj'
    rw [ENat.coe_le_coe] at hle
    omega
  · have hjr : j = (exitTime C X).toNat := Nat.le_antisymm hj hj'
    subst hjr
    exact hc

end RWRS.Support