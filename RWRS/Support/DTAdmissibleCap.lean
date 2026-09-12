/-
The admissibility cap of Step 1 of `prop:doubly-transient-really-general`:
the total killed-Green interaction of the earlier trap blocks with the stage
centre is at most one, by the admissibility of the centre for the used set.
Supporting lemmas: the `toReal` of a finite ENNReal sum, the domination of
the killed Green function by the free Green function at the level of real
numbers, and the double-sum bound over disjoint blocks.
-/
import LatticeProb.Network.KilledGreenEscape
import RWRS.Basic
import RWRS.Support.SeriesLaw
import RWRS.Support.DTAdmissible
import RWRS.Support.DTStageEvents
import RWRS.Support.KilledGreen

open LatticeProb RWRS

open scoped ENNReal

namespace RWRS.Support

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [G.LocallyFinite]

omit [DecidableEq V] in
/-- The `toReal` of a finite sum of extended naturals is the sum of the
`toReal`s, provided no term is `⊤`. -/
theorem toReal_sum_of_ne_top (F : Finset V) (f : V → ℝ≥0∞)
    (h : ∀ v ∈ F, f v ≠ ⊤) :
    (∑ v ∈ F, f v).toReal = ∑ v ∈ F, (f v).toReal := by
  exact ENNReal.toReal_sum h

omit [DecidableEq V] in
/-- The killed Green function as a real number is dominated by the free Green
function as a real number, whenever the free Green function is finite. -/
theorem killedGreenReal_le_greenReal {C : Set V} {x v : V}
    (hv : RWRS.green G x v ≠ ⊤) :
    RWRS.killedGreenReal G C x v ≤ (RWRS.green G x v).toReal := by
  rw [RWRS.killedGreenReal]
  have hkg : RWRS.killedGreen G C x v ≠ ⊤ :=
    fun hc => hv (le_antisymm le_top (hc ▸ RWRS.Support.killedGreen_le_green (G := G) (C := C) x v))
  exact (ENNReal.toReal_le_toReal hkg hv).mpr (RWRS.Support.killedGreen_le_green (G := G) (C := C) x v)

/-- A double sum over pairwise disjoint blocks contained in `F` is bounded by
the sum over `F`, for nonnegative weights. -/
theorem sum_range_le_sum_finset (C : ℕ → Finset V) (i : ℕ) (F : Finset V) (f : V → ℝ)
    (hf : ∀ v, 0 ≤ f v)
    (hCF : ∀ j < i, C j ⊆ F)
    (hdisj : ∀ a < i, ∀ b < i, a ≠ b → Disjoint (C a) (C b)) :
    ∑ j ∈ Finset.range i, ∑ v ∈ C j, f v ≤ ∑ v ∈ F, f v := by
  classical
  have hub : (Finset.range i).biUnion C ⊆ F := by
    intro v hv
    simp only [Finset.mem_biUnion, Finset.mem_range] at hv
    obtain ⟨j, hj, hvj⟩ := hv
    exact hCF j hj hvj
  have hpd : ((Finset.range i : Set ℕ)).PairwiseDisjoint C := by
    intro a ha b hb hab
    exact hdisj a (Finset.mem_range.1 ha) b (Finset.mem_range.1 hb) hab
  have hsplit : ∑ v ∈ F, f v
      = ∑ v ∈ F ∩ (Finset.range i).biUnion C, f v
        + ∑ v ∈ F \ (Finset.range i).biUnion C, f v :=
    (Finset.sum_inter_add_sum_sdiff F ((Finset.range i).biUnion C) f).symm
  have hint : F ∩ (Finset.range i).biUnion C = (Finset.range i).biUnion C := by
    ext v
    simp only [Finset.mem_inter]
    exact ⟨fun h => h.2, fun h => ⟨hub h, h⟩⟩
  rw [hsplit, hint, Finset.sum_biUnion hpd]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun v _ => hf v)

/-- **The total earlier-block interaction is capped by admissibility.**  If `y`
is admissible for the used set `F` (its Green interaction with `F` is at most
one) and every earlier block lies in `F`, then the sum over the earlier blocks
of the killed Green interactions with `y` is at most one. -/
theorem sum_earlierBlocks_le_one (C : ℕ → Finset V) (i : ℕ) (y : V) (F K : Finset V)
    (r : ℕ)
    (hescK : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ (K : Set V))
    (hCF : ∀ j < i, C j ⊆ F)
    (hdisj : ∀ a < i, ∀ b < i, a ≠ b → Disjoint (C a) (C b))
    (hadm : RWRS.Support.Admissible G r F y)
    (hgreen : ∀ v ∈ F, RWRS.green G v y ≠ ⊤) :
    ∑ j ∈ Finset.range i, ∑ v ∈ C j,
        RWRS.killedGreenReal G (K : Set V) v y ≤ 1 := by
  have hnn : ∀ v, 0 ≤ RWRS.killedGreenReal G (K : Set V) v y :=
    fun v => RWRS.Support.killedGreenReal_nonneg_of_escape K hescK v y
  have h1 : ∑ j ∈ Finset.range i, ∑ v ∈ C j, RWRS.killedGreenReal G (K : Set V) v y
      ≤ ∑ v ∈ F, RWRS.killedGreenReal G (K : Set V) v y :=
    sum_range_le_sum_finset C i F _ hnn hCF hdisj
  have h2 : ∑ v ∈ F, RWRS.killedGreenReal G (K : Set V) v y
      ≤ ∑ v ∈ F, (RWRS.green G v y).toReal :=
    Finset.sum_le_sum fun v hv => killedGreenReal_le_greenReal G (hgreen v hv)
  have h3 : (∑ v ∈ F, RWRS.green G v y).toReal = ∑ v ∈ F, (RWRS.green G v y).toReal :=
    toReal_sum_of_ne_top F _ hgreen
  have h4 : ∑ v ∈ F, (RWRS.green G v y).toReal ≤ 1 := by
    have hsumtop : (∑ v ∈ F, RWRS.green G v y) ≠ ⊤ := by
      intro hc
      have h1' : (∑ v ∈ F, RWRS.green G v y) ≤ 1 := hadm.2
      rw [hc] at h1'
      exact absurd h1' (by simp)
    have h5 : (∑ v ∈ F, RWRS.green G v y).toReal ≤ (1 : ℝ≥0∞).toReal :=
      (ENNReal.toReal_le_toReal hsumtop ENNReal.one_ne_top).mpr hadm.2
    have h6 : (1:ℝ≥0∞).toReal = 1 := by simp
    rwa [h3, h6] at h5
  exact le_trans h1 (le_trans h2 h4)
end RWRS.Support
