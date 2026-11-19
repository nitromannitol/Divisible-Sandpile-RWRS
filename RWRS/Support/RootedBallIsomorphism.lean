import RWRS.Support.RootedBallType

/-!
# Rooted ball types and isomorphism

Root-preserving graph isomorphisms preserve finite ball codes and the least
matching code.
-/

namespace RWRS.Support

private theorem mem_ball_iff_of_equiv {m : ℕ} {N N' : Net m} (φ : ℕ ≃ ℕ)
    (hadj : ∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j))
    (hroot : φ (netRoot N) = netRoot N') :
    ∀ r i, i ∈ netBallSet N r ↔ φ i ∈ netBallSet N' r := by
  intro r
  induction r with
  | zero =>
      intro i
      constructor
      · intro hi
        have hi' : i = netRoot N := hi
        subst i
        exact hroot
      · intro hi
        have hi' : φ i = netRoot N' := hi
        exact φ.injective (hi'.trans hroot.symm)
  | succ r ih =>
      intro i
      constructor
      · rintro (hi | ⟨w, hw, hwi⟩)
        · exact Or.inl ((ih i).1 hi)
        · exact Or.inr ⟨φ w, (ih w).1 hw, (hadj w i).1 hwi⟩
      · rintro (hi | ⟨w, hw, hwi⟩)
        · exact Or.inl ((ih i).2 hi)
        · refine Or.inr ⟨φ.symm w, ?_, ?_⟩
          · apply (ih (φ.symm w)).2
            simpa only [Equiv.apply_symm_apply] using hw
          · apply (hadj (φ.symm w) i).2
            simpa only [Equiv.apply_symm_apply] using hwi

private theorem netBallMatches_of_equiv {m : ℕ} {N N' : Net m} (φ : ℕ ≃ ℕ)
    (hadj : ∀ i j, (netGraph N).Adj i j ↔ (netGraph N').Adj (φ i) (φ j))
    (hroot : φ (netRoot N) = netRoot N') {r : ℕ} {c : RootedFiniteGraph}
    (h : NetBallMatches N r c) : NetBallMatches N' r c := by
  obtain ⟨e, he, heroot, heball, headj⟩ := h
  refine ⟨φ ∘ e, φ.injective.comp he, ?_, ?_, ?_⟩
  · exact hroot.symm.trans (congrArg φ heroot)
  · intro v
    constructor
    · intro hv
      have hu : φ.symm v ∈ netBallSet N r := by
        apply (mem_ball_iff_of_equiv φ hadj hroot r (φ.symm v)).2
        simpa only [Equiv.apply_symm_apply] using hv
      obtain ⟨i, hi⟩ := (heball (φ.symm v)).1 hu
      refine ⟨i, ?_⟩
      change φ (e i) = v
      rw [hi, Equiv.apply_symm_apply]
    · rintro ⟨i, hi⟩
      have hu : e i ∈ netBallSet N r := (heball (e i)).2 ⟨i, rfl⟩
      have hv := (mem_ball_iff_of_equiv φ hadj hroot r (e i)).1 hu
      change φ (e i) = v at hi
      rw [← hi]
      exact hv
  · intro i j
    exact (hadj (e i) (e j)).symm.trans (headj i j)

/-- Isomorphic rooted networks have the same finite rooted-ball codes. -/
theorem netBallMatches_iff_of_netIso {m : ℕ} {N N' : Net m} (h : NetIso N N')
    (r : ℕ) (c : RootedFiniteGraph) :
    NetBallMatches N r c ↔ NetBallMatches N' r c := by
  obtain ⟨φ, hadj, hroot, -⟩ := h
  constructor
  · exact netBallMatches_of_equiv φ hadj hroot
  · apply netBallMatches_of_equiv φ.symm
    · intro i j
      simpa only [Equiv.apply_symm_apply] using (hadj (φ.symm i) (φ.symm j)).symm
    · exact φ.symm_apply_eq.mpr hroot.symm

/-- Isomorphic rooted networks have the same rooted-ball type at every radius. -/
theorem netBallType_eq_of_netIso {m : ℕ} {N N' : Net m} (h : NetIso N N')
    (r : ℕ) : netBallType N r = netBallType N' r :=
  netBallType_eq_of_matches_iff r (netBallMatches_iff_of_netIso h r)

end RWRS.Support
