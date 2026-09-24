/-
The part of `C_k` outside the comb is small.

Every vertex of `C_k` other than the comb sits at ray level below the attachment
point of the `k`-th gadget, and the gadgets are radially disjoint, so it lies in
the ball of radius `s_k` around the root.  The volume upper bound of
`prop:rec-growth` then bounds its number by `C_G s_k^{d_f}`.
-/
import RWRS.Support.RayTransport
import RWRS.Support.RayGadget

namespace RWRS.Support

open scoped Classical ENNReal

variable {B : ℕ} {L : ℕ → ℕ} {m s : ℕ → ℕ}

/-- The ray vertex `r_i` is at distance at most `i` from the root. -/
theorem edist_rayPt_le (i : ℕ) :
    (rayGraph B L m s).edist (rayPt B L m i) (rayPt B L m 0) ≤ (i : ℕ∞) := by
  calc (rayGraph B L m s).edist (rayPt B L m i) (rayPt B L m 0)
      = (rayGraph B L m s).edist (rayPt B L m 0) (rayPt B L m i) := SimpleGraph.edist_comm
    _ ≤ (((rayWalk (rayGadget_rayGraph (B := B) (L := L) (m := m) (s := s)) i).length : ℕ) :
          ℕ∞) := SimpleGraph.edist_le _
    _ = (i : ℕ∞) := by rw [rayWalk_length]

/-- **The vertices below the attachment point lie in the ball of radius `s_k`.** -/
theorem rayBall_subset_closedBall (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    (hsep : ∀ j, s j + RWRS.gadgetRadius L (m j) < s (j + 1)) {k : ℕ} (hsk : 1 ≤ s k) :
    ((rayBall B L m s hs (s k - 1) : Finset (RayV B L m)) : Set (RayV B L m))
      ⊆ RWRS.closedBall (rayGraph B L m s) (rayPt B L m 0) (s k) := by
  rintro x hx
  rw [Finset.mem_coe, mem_rayBall] at hx
  match x with
  | Sum.inl i =>
      have hi : i ≤ s k - 1 := hx
      refine le_trans (edist_rayPt_le (B := B) (L := L) (m := m) (s := s) i) ?_
      exact_mod_cast Nat.cast_le.2 (by omega : i ≤ s k)
  | Sum.inr ⟨j, ⟨v, hv⟩⟩ =>
      have hj : s j ≤ s k - 1 := hx
      have hjk : j < k := hs.lt_iff_lt.1 (by omega)
      have hbound := edist_le_of_mem_gadget (G := rayGraph B L m s) rayGadget_rayGraph hL j v
      rw [rayEmb_of_ne hv] at hbound
      refine le_trans hbound ?_
      have h1 : s j + RWRS.gadgetRadius L (m j) < s (j + 1) := hsep j
      have h2 : s (j + 1) ≤ s k := hs.le_iff_le.2 (by omega)
      exact_mod_cast Nat.cast_le.2 (by omega : s j + RWRS.gadgetRadius L (m j) ≤ s k)

/-- The number of those vertices, from the volume upper bound. -/
theorem card_rayBall_le {C_G d_f : ℝ} (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    (hsep : ∀ j, s j + RWRS.gadgetRadius L (m j) < s (j + 1))
    (hVG : ∀ r : ℕ, 1 ≤ r →
      (RWRS.closedBall (rayGraph B L m s) (rayPt B L m 0) r).encard
        ≤ ENNReal.ofReal (C_G * (r : ℝ) ^ d_f))
    {k : ℕ} (hsk : 1 ≤ s k) (hnn : 0 ≤ C_G * (s k : ℝ) ^ d_f) :
    ((rayBall B L m s hs (s k - 1)).card : ℝ) ≤ C_G * (s k : ℝ) ^ d_f := by
  have hsub := rayBall_subset_closedBall (B := B) hL hs hsep (k := k) hsk
  have hcard : ((rayBall B L m s hs (s k - 1) : Finset (RayV B L m)) :
      Set (RayV B L m)).encard = ((rayBall B L m s hs (s k - 1)).card : ℕ∞) :=
    Set.encard_coe_eq_coe_finsetCard _
  have hchain : (((rayBall B L m s hs (s k - 1)).card : ℕ∞) : ℝ≥0∞)
      ≤ ENNReal.ofReal (C_G * (s k : ℝ) ^ d_f) := by
    rw [← hcard]
    exact le_trans (by exact_mod_cast Set.encard_le_encard hsub) (hVG (s k) hsk)
  have hcast : (((rayBall B L m s hs (s k - 1)).card : ℕ∞) : ℝ≥0∞)
      = ENNReal.ofReal (((rayBall B L m s hs (s k - 1)).card : ℝ)) := by
    rw [ENNReal.ofReal_natCast]
    rfl
  rw [hcast] at hchain
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 hchain

end RWRS.Support
