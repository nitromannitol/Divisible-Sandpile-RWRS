/-
The final display of `thm:recurrent-nonstab`.

The sum over `C_k` splits into the comb and the rest.  On the comb the voltage
is the comb's own voltage, so `cor:rec-loc` bounds that part below by
`c_loc R_{m_k}^δ`.  The rest lies in the ball of radius `s_k`, where the voltage
is at most `s_k + 1` and the mass at least `-b`, so it costs at most
`b C_G (s_k+1)^{d_f+1}`.  Condition `eq:rec-cond-div` makes the first term at
least `k` times the second scale, and the sum diverges along the good gadgets.
-/
import RWRS.Support.RayBallCard
import RWRS.Support.NestedLower
import RWRS.Support.TrGood
import RWRS.Support.CombOdometer

namespace RWRS.Support

open scoped Classical ENNReal

variable {B : ℕ} {L : ℕ → ℕ} {m s : ℕ → ℕ}

/-- The scenery of the ray graph read on the sites of the `k`-th gadget. -/
noncomputable def rayPullFun (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (k : ℕ)
    (Y : RayV B L m → ℝ) (u : List (Fin B) × ℕ) : ℝ :=
  if h : u ∈ RWRS.gadgetSites B L (m k) then Y (rayEmb B L m s k ⟨u, h⟩) else 1

theorem one_le_rayPullFun {k : ℕ} {Y : RayV B L m → ℝ} (hY : ∀ v, 1 ≤ Y v)
    (u : List (Fin B) × ℕ) : 1 ≤ rayPullFun B L m s k Y u := by
  rw [rayPullFun]
  split_ifs with h
  · exact hY _
  · exact le_rfl

theorem image_combGadget {n : ℕ} (ω : List (Fin B)) :
    (combGadget B L n ω).image Subtype.val = combFinset B L n ω := by
  ext u
  simp only [Finset.mem_image, combGadget, Finset.mem_subtype]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact hv
  · intro hu
    have huS : u ∈ RWRS.combSet B L n ω := by
      rw [← Finset.mem_coe, coe_combFinset] at hu
      exact hu
    exact ⟨⟨u, combSet_subset_gadgetSites n ω huS⟩, hu, rfl⟩

section
variable [inst : (rayGraph B L m s).LocallyFinite]

/-- **The comb's contribution, read as a sum over the tree of pipes.** -/
theorem sum_rayComb_eq (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (hs : StrictMono s)
    {k : ℕ} {ω : List (Fin B)} (hω : ω.length = m k) (hmk : 1 ≤ m k) (hsk : 1 ≤ s k)
    (Y : RayV B L m → ℝ) (b : ℝ) :
    ∑ x ∈ rayComb B L m s k ω,
        RWRS.killedGreenReal (rayGraph B L m s)
          ((recSet B L m s hs k ω : Finset (RayV B L m)) : Set (RayV B L m))
          (rayPt B L m 0) x * (Y x - b)
      = ∑' u : ↥(RWRS.combSet B L (m k) ω),
          RWRS.combVoltage B L true (m k) ω u
            * (rayPullFun B L m s k Y (u : List (Fin B) × ℕ) - b) := by
  classical
  rw [rayComb, Finset.sum_image (fun a _ c _ h => rayEmb_injective k h)]
  have hterm : ∀ z ∈ combGadget B L (m k) ω,
      RWRS.killedGreenReal (rayGraph B L m s)
          ((recSet B L m s hs k ω : Finset (RayV B L m)) : Set (RayV B L m))
          (rayPt B L m 0) (rayEmb B L m s k z) * (Y (rayEmb B L m s k z) - b)
        = RWRS.combVoltage B L true (m k) ω (z : List (Fin B) × ℕ)
            * (rayPullFun B L m s k Y (z : List (Fin B) × ℕ) - b) := by
    intro z _
    rw [ray_eq_combVoltage hB hL2 hs hω hmk hsk z, rayPullFun, dif_pos z.2]
  rw [Finset.sum_congr rfl hterm]
  have himg : ∑ z ∈ combGadget B L (m k) ω,
      RWRS.combVoltage B L true (m k) ω (z : List (Fin B) × ℕ)
        * (rayPullFun B L m s k Y (z : List (Fin B) × ℕ) - b)
      = ∑ u ∈ (combGadget B L (m k) ω).image Subtype.val,
          RWRS.combVoltage B L true (m k) ω u * (rayPullFun B L m s k Y u - b) :=
    (Finset.sum_image (f := fun u : List (Fin B) × ℕ =>
      RWRS.combVoltage B L true (m k) ω u * (rayPullFun B L m s k Y u - b))
      (fun a _ c _ h => Subtype.ext h)).symm
  rw [himg, image_combGadget,
    ← coe_combFinset (B := B) (L := L) (m k) ω]
  exact (Finset.tsum_subtype' (combFinset B L (m k) ω)
    (fun u => RWRS.combVoltage B L true (m k) ω u
      * (rayPullFun B L m s k Y u - b))).symm

/-- **The cost of everything outside the comb.** -/
theorem sum_sdiff_ge (hL : ∀ j, 1 ≤ j → 1 ≤ L j) (hs : StrictMono s)
    {k : ℕ} {ω : List (Fin B)} (hmk : 1 ≤ m k)
    (Y : RayV B L m → ℝ) (hY : ∀ v, 1 ≤ Y v) (b : ℝ) (hb : 0 ≤ b) :
    -(b * ((s k : ℝ) + 1) * ((rayBall B L m s hs (s k - 1)).card : ℝ))
      ≤ ∑ x ∈ recSet B L m s hs k ω \ rayComb B L m s k ω,
          RWRS.killedGreenReal (rayGraph B L m s)
            ((recSet B L m s hs k ω : Finset (RayV B L m)) : Set (RayV B L m))
            (rayPt B L m 0) x * (Y x - b) := by
  classical
  set S := recSet B L m s hs k ω \ rayComb B L m s k ω with hS
  have hSsub : S ⊆ rayBall B L m s hs (s k - 1) := by
    intro x hx
    rw [hS, Finset.mem_sdiff] at hx
    rcases Finset.mem_union.1 hx.1 with h | h
    · exact h
    · exact absurd h hx.2
  have hterm : ∀ x ∈ S, -(b * ((s k : ℝ) + 1))
      ≤ RWRS.killedGreenReal (rayGraph B L m s)
          ((recSet B L m s hs k ω : Finset (RayV B L m)) : Set (RayV B L m))
          (rayPt B L m 0) x * (Y x - b) := by
    intro x _
    have h0 := recVolt_nonneg hL hs k ω x
    have h1 := recVolt_le hL hs (m := m) (k := k) (w := ω) hmk x
    have h2 : -b ≤ Y x - b := by linarith [hY x]
    nlinarith [h0, h1, h2, hb]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (S.card : ℝ) ≤ ((rayBall B L m s hs (s k - 1)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hSsub
  have hbs : (0 : ℝ) ≤ b * ((s k : ℝ) + 1) := by positivity
  nlinarith [hsum, hcard, hbs]

/-- **The final display.**  The comb contributes at least `c_loc R_{m_k}^δ` and
the rest of `C_k` costs at most `b C_G (s_k+1)^{d_f+1}`. -/
theorem sum_recSet_ge (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j) (hs : StrictMono s)
    {d_f C_comb c_loc δ C_G : ℝ} (hd2 : 2 < d_f) (hCG : 0 < C_G)
    (hsep : ∀ j, s j + RWRS.gadgetRadius L (m j) < s (j + 1))
    (hVG : ∀ r : ℕ, 1 ≤ r →
      (RWRS.closedBall (rayGraph B L m s) (rayPt B L m 0) r).encard
        ≤ ENNReal.ofReal (C_G * (r : ℝ) ^ d_f))
    (hloc : ∀ (e : Bool) (n : ℕ) (ω : List (Fin B)), ω.length = n → 1 ≤ n →
      ∀ (Z : List (Fin B) × ℕ → ℝ) (b : ℝ), 0 ≤ b → (∀ v, 1 ≤ Z v) →
        ∀ v ∈ RWRS.combFirstHalf B L n ω,
          (2 + 2 * b * (C_comb + 1)) * (L n : ℝ) ≤ Z v →
          c_loc * (RWRS.gadgetRadius L n : ℝ) ^ δ
            ≤ ∑' u : ↥(RWRS.combSet B L n ω),
                RWRS.combVoltage B L e n ω u * (Z u - b))
    {k : ℕ} {ω : List (Fin B)} (hω : ω.length = m k) (hmk : 1 ≤ m k) (hsk : 1 ≤ s k)
    (b : ℝ) (hb : 0 ≤ b) (Y : RayV B L m → ℝ) (hY : ∀ v, 1 ≤ Y v)
    {v : List (Fin B) × ℕ} (hvmem : v ∈ RWRS.combFirstHalf B L (m k) ω)
    (hthr : (2 + 2 * b * (C_comb + 1)) * (L (m k) : ℝ)
      ≤ rayPullFun B L m s k Y v) :
    c_loc * (RWRS.gadgetRadius L (m k) : ℝ) ^ δ - b * C_G * ((s k : ℝ) + 1) ^ (d_f + 1)
      ≤ ∑ x ∈ recSet B L m s hs k ω,
          RWRS.killedGreenReal (rayGraph B L m s)
            ((recSet B L m s hs k ω : Finset (RayV B L m)) : Set (RayV B L m))
            (rayPt B L m 0) x * (Y x - b) := by
  classical
  have hL : ∀ j, 1 ≤ j → 1 ≤ L j := one_le_of_two_le hL2
  have hsub : rayComb B L m s k ω ⊆ recSet B L m s hs k ω := Finset.subset_union_right
  have hsplit := Finset.sum_sdiff (f := fun x => RWRS.killedGreenReal (rayGraph B L m s)
      ((recSet B L m s hs k ω : Finset (RayV B L m)) : Set (RayV B L m))
      (rayPt B L m 0) x * (Y x - b)) hsub
  -- the comb
  have hcomb := hloc true (m k) ω hω hmk (rayPullFun B L m s k Y) b hb
    (one_le_rayPullFun hY) v hvmem hthr
  rw [← sum_rayComb_eq hB hL2 hs hω hmk hsk Y b] at hcomb
  -- the rest
  have hrest := sum_sdiff_ge (m := m) hL hs (k := k) (ω := ω) hmk Y hY b hb
  have hsk0 : (0 : ℝ) ≤ (s k : ℝ) := Nat.cast_nonneg _
  have hnn : 0 ≤ C_G * (s k : ℝ) ^ d_f := by positivity
  have hcard := card_rayBall_le (B := B) hL hs hsep hVG hsk hnn
  have hd0 : (0 : ℝ) < d_f := by linarith
  have hpow : ((s k : ℝ)) ^ d_f ≤ ((s k : ℝ) + 1) ^ d_f :=
    Real.rpow_le_rpow hsk0 (by linarith) hd0.le
  have hone : (0 : ℝ) < (s k : ℝ) + 1 := by linarith
  have hsplitpow : ((s k : ℝ) + 1) ^ (d_f + 1) = ((s k : ℝ) + 1) ^ d_f * ((s k : ℝ) + 1) := by
    rw [Real.rpow_add hone, Real.rpow_one]
  have hbig : b * ((s k : ℝ) + 1) * ((rayBall B L m s hs (s k - 1)).card : ℝ)
      ≤ b * C_G * ((s k : ℝ) + 1) ^ (d_f + 1) := by
    have h1 : b * ((s k : ℝ) + 1) * ((rayBall B L m s hs (s k - 1)).card : ℝ)
        ≤ b * ((s k : ℝ) + 1) * (C_G * (s k : ℝ) ^ d_f) := by
      have hnn2 : (0 : ℝ) ≤ b * ((s k : ℝ) + 1) := by positivity
      exact mul_le_mul_of_nonneg_left hcard hnn2
    have h2 : b * ((s k : ℝ) + 1) * (C_G * (s k : ℝ) ^ d_f)
        ≤ b * C_G * ((s k : ℝ) + 1) ^ (d_f + 1) := by
      rw [hsplitpow]
      have h3 : b * C_G * ((s k : ℝ) + 1) * ((s k : ℝ) ^ d_f)
          ≤ b * C_G * ((s k : ℝ) + 1) * (((s k : ℝ) + 1) ^ d_f) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      nlinarith [h3]
    linarith
  linarith [hsplit, hcomb, hrest, hbig]

/-- The sites of the ray graph that can carry a spike. -/
noncomputable def raySpikes (B : ℕ) (L : ℕ → ℕ) (m s : ℕ → ℕ) (k : ℕ) :
    Finset (RayV B L m) :=
  ((firstHalfFinset B L (m k)).subtype
    (fun v => v ∈ RWRS.gadgetSites B L (m k))).image (rayEmb B L m s k)

/-- **The odometer is infinite at the root.** -/
theorem odometerLimit_ray_top (hB : 2 ≤ B) (hL2 : ∀ j, 1 ≤ j → 2 ≤ L j)
    (hs : StrictMono s) (hmS : StrictMono m)
    {d_f C_comb c_loc δ C_G : ℝ} (hd2 : 2 < d_f) (hCG : 0 < C_G)
    (hsep : ∀ j, s j + RWRS.gadgetRadius L (m j) < s (j + 1))
    (hVG : ∀ r : ℕ, 1 ≤ r →
      (RWRS.closedBall (rayGraph B L m s) (rayPt B L m 0) r).encard
        ≤ ENNReal.ofReal (C_G * (r : ℝ) ^ d_f))
    (hdiv : ∀ j : ℕ, ((s (j + 1) : ℝ) + 1) ^ (d_f + 1) * (((j + 1 : ℕ) : ℝ))
      ≤ c_loc * (RWRS.gadgetRadius L (m (j + 1)) : ℝ) ^ δ)
    (hloc : ∀ (e : Bool) (n : ℕ) (ω : List (Fin B)), ω.length = n → 1 ≤ n →
      ∀ (Z : List (Fin B) × ℕ → ℝ) (b : ℝ), 0 ≤ b → (∀ v, 1 ≤ Z v) →
        ∀ v ∈ RWRS.combFirstHalf B L n ω,
          (2 + 2 * b * (C_comb + 1)) * (L n : ℝ) ≤ Z v →
          c_loc * (RWRS.gadgetRadius L n : ℝ) ^ δ
            ≤ ∑' u : ↥(RWRS.combSet B L n ω),
                RWRS.combVoltage B L e n ω u * (Z u - b))
    (b : ℝ) (hb : 0 ≤ b) (Y : RayV B L m → ℝ) (hY : ∀ v, 1 ≤ Y v)
    (hgood : {k : ℕ | ∃ x ∈ raySpikes B L m s k,
      (2 + 2 * b * (C_comb + 1)) * (L (m k) : ℝ) ≤ Y x}.Infinite) :
    RWRS.odometerLimit (rayGraph B L m s) (fun x => Y x - b + 1) (rayPt B L m 0) = ⊤ := by
  classical
  have hL : ∀ j, 1 ≤ j → 1 ≤ L j := one_le_of_two_le hL2
  haveI : Infinite (RayV B L m) := infinite_rayV
  have hG : (rayGraph B L m s).Connected := rayGraph_connected hL
  refine eq_top_of_forall_ofReal_le fun M => ?_
  obtain ⟨k, hk, hkM⟩ := hgood.exists_gt (max 1 (⌈M + b * C_G⌉₊ + ⌈b * C_G⌉₊))
  obtain ⟨x, hx, hthr⟩ := hk
  have hk1 : 1 ≤ k := le_trans (le_max_left _ _) hkM.le
  have hmk : 1 ≤ m k := le_trans hk1 (hmS.le_apply)
  have hsk : 1 ≤ s k := le_trans hk1 (hs.le_apply)
  -- the spike, read on the tree of pipes
  rw [raySpikes, Finset.mem_image] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  rw [Finset.mem_subtype] at hz
  obtain ⟨hw, h1, h2⟩ := firstHalf_of_mem hz
  have hpull : rayPullFun B L m s k Y (z : List (Fin B) × ℕ) = Y x := by
    rw [rayPullFun, dif_pos z.2, ← hzx]
  have hvmem : (z : List (Fin B) × ℕ)
      ∈ RWRS.combFirstHalf B L (m k) (z : List (Fin B) × ℕ).1 := ⟨rfl, h1, h2⟩
  have hmain := sum_recSet_ge hB hL2 hs hd2 hCG hsep hVG hloc (k := k)
    (ω := (z : List (Fin B) × ℕ).1) hw hmk hsk b hb Y hY hvmem (by rw [hpull]; exact hthr)
  -- the divergence condition
  have hdivk := hdiv (k - 1)
  rw [show k - 1 + 1 = k by omega] at hdivk
  have hone : (1 : ℝ) ≤ ((s k : ℝ) + 1) ^ (d_f + 1) :=
    Real.one_le_rpow (by simp) (by linarith)
  have hkNat : ⌈M + b * C_G⌉₊ + ⌈b * C_G⌉₊ ≤ k :=
    le_trans (le_max_right 1 _) hkM.le
  have hkge : M + b * C_G ≤ (k : ℝ) := by
    have h1 : (⌈M + b * C_G⌉₊ : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (by omega : ⌈M + b * C_G⌉₊ ≤ k)
    exact le_trans (Nat.le_ceil _) h1
  have hkCG : b * C_G ≤ (k : ℝ) := by
    have h1 : (⌈b * C_G⌉₊ : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (by omega : ⌈b * C_G⌉₊ ≤ k)
    exact le_trans (Nat.le_ceil _) h1
  have hfinal : M ≤ ∑ y ∈ recSet B L m s hs k (z : List (Fin B) × ℕ).1,
      RWRS.killedGreenReal (rayGraph B L m s)
        ((recSet B L m s hs k (z : List (Fin B) × ℕ).1 : Finset (RayV B L m)) :
          Set (RayV B L m))
        (rayPt B L m 0) y * (Y y - b) := by
    have hstep : ((k : ℝ) - b * C_G) * ((s k : ℝ) + 1) ^ (d_f + 1)
        ≤ c_loc * (RWRS.gadgetRadius L (m k) : ℝ) ^ δ
            - b * C_G * ((s k : ℝ) + 1) ^ (d_f + 1) := by
      have : ((s k : ℝ) + 1) ^ (d_f + 1) * (k : ℝ)
          ≤ c_loc * (RWRS.gadgetRadius L (m k) : ℝ) ^ δ := by
        have hcast : ((k : ℕ) : ℝ) = (k : ℝ) := rfl
        simpa using hdivk
      nlinarith [this]
    have hMle : M ≤ ((k : ℝ) - b * C_G) * ((s k : ℝ) + 1) ^ (d_f + 1) := by
      have hnn : (0 : ℝ) ≤ (k : ℝ) - b * C_G := by linarith [hkCG]
      nlinarith [hkge, hone, hnn]
    linarith [hmain, hstep, hMle]
  have hlow := ofReal_sum_le_odometerLimit' (G := rayGraph B L m s) hG
    (fun x => Y x - b + 1) (rayPt B L m 0)
    (recSet B L m s hs k (z : List (Fin B) × ℕ).1)
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlow
  refine le_trans hfinal (le_of_eq (Finset.sum_congr rfl fun y _ => by ring_nf))

end

end RWRS.Support
