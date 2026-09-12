/-
The growth exponent of the ray with the gadgets.

`thm:recurrent-nonstab` reads the cardinality of a ball as a natural number,
which is its cardinality only because the balls are finite; the three lemmas
here move between that natural number and the `[0,∞]`-valued `encard` the volume
proposition bounds, and the last theorem reads the exponent off the two bounds.
-/
import RWRS.Support.RecData
import RWRS.Support.RayVolume

namespace RWRS.Support

open Filter
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V}

theorem one_le_encard_closedBall (o : V) (R : ℕ) :
    1 ≤ (RWRS.closedBall G o R).encard := by
  refine Set.one_le_encard_iff_nonempty.2 ⟨o, ?_⟩
  show G.edist o o ≤ (R : ℕ∞)
  simp

theorem toNat_encard_pos (o : V) (R : ℕ) (hfin : (RWRS.closedBall G o R).Finite) :
    1 ≤ (RWRS.closedBall G o R).encard.toNat := by
  have hne : (RWRS.closedBall G o R).encard ≠ ⊤ := hfin.encard_lt_top.ne
  have h1 := one_le_encard_closedBall (G := G) o R
  have : ((RWRS.closedBall G o R).encard.toNat : ℕ∞) = (RWRS.closedBall G o R).encard :=
    ENat.coe_toNat hne
  rw [← this] at h1
  exact_mod_cast h1

theorem toNat_encard_le_of_le {s : Set V} (hfin : s.Finite) {x : ℝ} (hx : 0 ≤ x)
    (h : s.encard ≤ ENNReal.ofReal x) : (s.encard.toNat : ℝ) ≤ x := by
  have hne : s.encard ≠ ⊤ := hfin.encard_lt_top.ne
  have hcoe : ((s.encard.toNat : ℕ) : ℕ∞) = s.encard := ENat.coe_toNat hne
  have h2 : ((s.encard.toNat : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal x := by
    refine le_trans (le_of_eq ?_) h
    rw [← hcoe]
    simp
  rw [← ENNReal.ofReal_natCast] at h2
  exact (ENNReal.ofReal_le_ofReal_iff hx).1 h2

theorem le_toNat_encard_of_le {s : Set V} (hfin : s.Finite) {x : ℝ}
    (h : ENNReal.ofReal x ≤ s.encard) : x ≤ (s.encard.toNat : ℝ) := by
  have hne : s.encard ≠ ⊤ := hfin.encard_lt_top.ne
  have hcoe : ((s.encard.toNat : ℕ) : ℕ∞) = s.encard := ENat.coe_toNat hne
  have h2 : ENNReal.ofReal x ≤ ((s.encard.toNat : ℕ) : ℝ≥0∞) := by
    rw [← hcoe] at h
    simpa using h
  rw [← ENNReal.ofReal_natCast] at h2
  by_cases hx : 0 ≤ x
  · exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  · have hxle : x ≤ 0 := le_of_not_ge hx
    exact le_trans hxle (by positivity)

section
variable {B : ℕ} {α d_f ρ : ℝ} {m s : ℕ → ℕ}

/-- **The growth exponent of the ray with the gadgets is `d_f`.** -/
theorem limsup_growth_rayGraph (hc : RWRS.CombCond B α) (hdf : d_f = 1 + 1 / α) (hρ : 0 < ρ)
    (hρ' : ρ < Real.log (RWRS.combLambda B α) / (α * Real.log B) / (d_f + 1))
    (hsdef : ∀ k, s k = ⌈(RWRS.gadgetRadius (RWRS.combLen B α) (m k) : ℝ) ^ ρ⌉₊)
    (hsep : ∀ k, s k + RWRS.gadgetRadius (RWRS.combLen B α) (m k) < s (k + 1))
    (hvolc : ∀ k, (∑ j ∈ Finset.range (k + 1),
        (RWRS.gadgetSize B (RWRS.combLen B α) (m j) : ℝ)) ≤ (s (k + 1) : ℝ) ^ d_f)
    (hsm : StrictMono s) (hmm : StrictMono m) :
    limsup (fun R : ℕ => Real.log ((RWRS.closedBall (rayGraph B (RWRS.combLen B α) m s)
        (rayPt B (RWRS.combLen B α) m 0) R).encard.toNat) / Real.log R) atTop = d_f := by
  obtain ⟨⟨C_G, hCpos, hup⟩, ⟨cg, hcpos, hlow⟩⟩ :=
    volumeGrowth_rayGraph hc hdf hρ hρ' hsdef hsep hvolc
  set r : ℕ → ℕ := fun k =>
    s (k + 1) + RWRS.gadgetRadius (RWRS.combLen B α) (m (k + 1)) with hrdef
  have hrmono : StrictMono r := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    have h1 : s (k + 1) < s (k + 1 + 1) := hsm (by omega)
    have h2 : RWRS.gadgetRadius (RWRS.combLen B α) (m (k + 1))
        ≤ RWRS.gadgetRadius (RWRS.combLen B α) (m (k + 1 + 1)) :=
      gadgetRadius_mono _ (le_of_lt (hmm (by omega)))
    simp only [hrdef]
    omega
  refine limsup_log_card C_G cg d_f hCpos hcpos _ ?_ ?_ r hrmono ?_
  · intro R
    exact toNat_encard_pos _ R (finite_closedBall_rayGraph hsm R)
  · intro R hR
    refine toNat_encard_le_of_le (finite_closedBall_rayGraph hsm R) ?_ (hup R hR)
    have : (0 : ℝ) ≤ (R : ℝ) ^ d_f := Real.rpow_nonneg (Nat.cast_nonneg R) _
    positivity
  · intro k
    exact le_toNat_encard_of_le (finite_closedBall_rayGraph hsm (r k)) (hlow (k + 1) (by omega))

end

end RWRS.Support
