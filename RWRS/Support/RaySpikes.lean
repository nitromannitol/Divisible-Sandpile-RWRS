/-
The sites of the ray graph that can carry a spike, and the good events.

`lem:rec-good` is proved for an abstract family of pairwise disjoint sets of
vertices whose cardinalities grow; here the family is the one the section names,
the sites in the first half of every terminal pipe of the `k`-th gadget, read in
the ray graph.  Two of them are disjoint because two gadgets meet only at their
roots and these sites are not roots.
-/
import RWRS.Support.RayGrowth
import RWRS.Support.TrGood
import RWRS.Frozen.RecGoodEvents

namespace RWRS.Support

open scoped Classical

variable {B : ℕ} {α : ℝ} {m s : ℕ → ℕ}

theorem mem_gadgetSites_of_firstHalf (hc : RWRS.CombCond B α) {n : ℕ} (hn : 1 ≤ n)
    {v : List (Fin B) × ℕ} (hv : v ∈ firstHalfFinset B (RWRS.combLen B α) n) :
    v ∈ RWRS.gadgetSites B (RWRS.combLen B α) n := by
  obtain ⟨hw, h1, h2⟩ := firstHalf_of_mem hv
  have h4 : 4 ≤ RWRS.combLen B α n := four_le_combLen hc hn
  refine ⟨Or.inr ⟨?_, h1, ?_⟩, le_of_eq hw⟩
  · intro hnil
    rw [hnil] at hw
    simp only [List.length_nil] at hw
    omega
  · rw [hw]
    omega

/-- The sites of the `k`-th gadget in the first half of a terminal pipe. -/
noncomputable def gadgetFirstHalf (B : ℕ) (α : ℝ) (m : ℕ → ℕ) (k : ℕ) :
    Finset (RWRS.gadgetSites B (RWRS.combLen B α) (m k)) :=
  (firstHalfFinset B (RWRS.combLen B α) (m k)).subtype
    (fun v => v ∈ RWRS.gadgetSites B (RWRS.combLen B α) (m k))

/-- Those sites, read in the ray graph. -/
noncomputable def raySpikeSites (B : ℕ) (α : ℝ) (m s : ℕ → ℕ) (k : ℕ) :
    Finset (RayV B (RWRS.combLen B α) m) :=
  (gadgetFirstHalf B α m k).image (rayEmb B (RWRS.combLen B α) m s k)

theorem card_gadgetFirstHalf (hc : RWRS.CombCond B α) {k : ℕ} (hk : 1 ≤ m k) :
    (gadgetFirstHalf B α m k).card = (firstHalfFinset B (RWRS.combLen B α) (m k)).card := by
  rw [gadgetFirstHalf, Finset.card_subtype, Finset.filter_true_of_mem]
  intro v hv
  exact mem_gadgetSites_of_firstHalf hc hk hv

theorem card_raySpikeSites (hc : RWRS.CombCond B α) {k : ℕ} (hk : 1 ≤ m k) :
    (raySpikeSites B α m s k).card = (firstHalfFinset B (RWRS.combLen B α) (m k)).card := by
  rw [raySpikeSites, Finset.card_image_of_injective _ (rayEmb_injective k),
    card_gadgetFirstHalf hc hk]

theorem encard_raySpikeSites_ge (hc : RWRS.CombCond B α) {k : ℕ} (hk : 1 ≤ m k) :
    ENNReal.ofReal ((B : ℝ) ^ m k * (RWRS.combLen B α (m k) : ℝ) / 4)
      ≤ ((raySpikeSites B α m s k : Finset (RayV B (RWRS.combLen B α) m)) :
          Set (RayV B (RWRS.combLen B α) m)).encard := by
  rw [Set.encard_coe_eq_coe_finsetCard, card_raySpikeSites hc hk]
  have h := card_firstHalfFinset_ge hc hk
  have h2 : ENNReal.ofReal ((B : ℝ) ^ m k * (RWRS.combLen B α (m k) : ℝ) / 4)
      ≤ ENNReal.ofReal ((firstHalfFinset B (RWRS.combLen B α) (m k)).card : ℝ) :=
    ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_natCast] at h2
  exact h2

theorem snd_pos_of_mem_raySpikeSites {k : ℕ} {v : RWRS.gadgetSites B (RWRS.combLen B α) (m k)}
    (hv : v ∈ gadgetFirstHalf B α m k) : v ≠ RWRS.gadgetRoot B (RWRS.combLen B α) (m k) := by
  rw [gadgetFirstHalf, Finset.mem_subtype] at hv
  obtain ⟨-, h1, -⟩ := firstHalf_of_mem hv
  intro hroot
  rw [hroot] at h1
  simp only [RWRS.gadgetRoot, RWRS.pipeRoot] at h1
  omega

theorem pairwise_disjoint_raySpikeSites :
    Pairwise (Function.onFun Disjoint
      (fun k => ((raySpikeSites B α m s k : Finset (RayV B (RWRS.combLen B α) m)) :
        Set (RayV B (RWRS.combLen B α) m)))) := by
  intro k l hkl
  simp only [Function.onFun]
  refine Set.disjoint_left.2 fun x hx hy => ?_
  rw [Finset.mem_coe, raySpikeSites, Finset.mem_image] at hx hy
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨w, hw, hvw⟩ := hy
  obtain ⟨hv0, -⟩ := rayGadget_rayGraph.disjoint l k w v hkl.symm hvw
  exact snd_pos_of_mem_raySpikeSites hw hv0

/-- **Infinitely many gadgets carry a spike, almost surely.** -/
theorem good_events_rayGraph {d_f K : ℝ} (hc : RWRS.CombCond B α) (hdf : d_f = 1 + 1 / α)
    (hK : 0 < K) (ν : MeasureTheory.Measure ℝ)
    (hν : MeasureTheory.IsProbabilityMeasure ν) (hpar : RWRS.IsPareto ν d_f)
    (hm : ∀ k, 1 ≤ k → 1 ≤ m k) :
    ∀ᵐ Y ∂(RWRS.iidLaw (RayV B (RWRS.combLen B α) m) ν),
      {k : ℕ | ∃ v ∈ ((raySpikeSites B α m s k :
          Finset (RayV B (RWRS.combLen B α) m)) : Set (RayV B (RWRS.combLen B α) m)),
        K * (RWRS.combLen B α (m k) : ℝ) ≤ Y v}.Infinite := by
  obtain ⟨η, -, -, -, hinf⟩ := RWRS.Frozen.recGoodEvents B α d_f K hc hdf hK ν hν hpar m
    (fun k => ((raySpikeSites B α m s k : Finset (RayV B (RWRS.combLen B α) m)) :
      Set (RayV B (RWRS.combLen B α) m)))
    pairwise_disjoint_raySpikeSites
    (fun k hk => encard_raySpikeSites_ge hc (hm k hk))
  exact hinf

end RWRS.Support
