import RWRS.Support.CombExists
import RWRS.Support.PipeTransient
import RWRS.Support.NestedLower
import RWRS.Support.IidMap
import RWRS.Frozen.CombEstimates

namespace RWRS.Support

open Filter MeasureTheory
open scoped ENNReal Classical

variable {B : ℕ} {α : ℝ}

/-- Every site of the comb is a site of the tree of pipes. -/
theorem combSet_subset_pipeSites {L : ℕ → ℕ} (n : ℕ) (w : List (Fin B)) :
    combSet B L n w ⊆ pipeSites B L := fun _ hv => hv.1

/-- The comb, as a finite set of sites of the tree of pipes. -/
noncomputable def combFinsetSub (B : ℕ) (L : ℕ → ℕ) (n : ℕ) (w : List (Fin B)) :
    Finset (pipeSites B L) :=
  (combFinset B L n w).subtype (fun v => v ∈ pipeSites B L)

theorem coe_combFinsetSub {L : ℕ → ℕ} (n : ℕ) (w : List (Fin B)) :
    ((combFinsetSub B L n w : Finset (pipeSites B L)) : Set (pipeSites B L))
      = Subtype.val ⁻¹' (combSet B L n w) := by
  ext v
  simp only [Set.mem_preimage, Finset.mem_coe, combFinsetSub, Finset.mem_subtype]
  rw [← Finset.mem_coe, coe_combFinset]

theorem image_combFinsetSub {L : ℕ → ℕ} (n : ℕ) (w : List (Fin B)) :
    (combFinsetSub B L n w).image Subtype.val = combFinset B L n w := by
  ext u
  simp only [Finset.mem_image, combFinsetSub, Finset.mem_subtype]
  constructor
  · rintro ⟨v, hv, rfl⟩; exact hv
  · intro hu
    have hval : u ∈ pipeSites B L := by
      have : u ∈ combSet B L n w := by rw [← coe_combFinset]; exact hu
      exact combSet_subset_pipeSites n w this
    exact ⟨⟨u, hval⟩, hu, rfl⟩

/-- The comb sum on the sites of the tree of pipes is the comb sum of
`prop:comb-estimates`. -/
theorem sum_combFinsetSub (n : ℕ) (w : List (Fin B))
    (a : List (Fin B) × ℕ → ℝ) :
    ∑ v ∈ combFinsetSub B (combLen B α) n w,
        RWRS.killedGreenReal (pipeSub B (combLen B α))
          ((combFinsetSub B (combLen B α) n w : Finset (pipeSites B (combLen B α))) :
            Set (pipeSites B (combLen B α)))
          (pipeRootSub B (combLen B α)) v * a (v : List (Fin B) × ℕ)
      = ∑' u : ↥(combSet B (combLen B α) n w),
          combVoltage B (combLen B α) false n w u * a u := by
  have hterm : ∀ v ∈ combFinsetSub B (combLen B α) n w,
      RWRS.killedGreenReal (pipeSub B (combLen B α))
          ((combFinsetSub B (combLen B α) n w : Finset (pipeSites B (combLen B α))) :
            Set (pipeSites B (combLen B α)))
          (pipeRootSub B (combLen B α)) v * a (v : List (Fin B) × ℕ)
        = combVoltage B (combLen B α) false n w (v : List (Fin B) × ℕ)
            * a (v : List (Fin B) × ℕ) := by
    intro v _
    rw [coe_combFinsetSub, killedGreenReal_pipeSub]
    rfl
  have htsum : (∑' u : ↥(combSet B (combLen B α) n w),
        combVoltage B (combLen B α) false n w u * a u)
      = ∑ u ∈ combFinset B (combLen B α) n w,
        combVoltage B (combLen B α) false n w u * a u := by
    rw [← coe_combFinset (B := B) (L := combLen B α) n w]
    exact Finset.tsum_subtype' (combFinset B (combLen B α) n w)
      (fun u => combVoltage B (combLen B α) false n w u * a u)
  rw [htsum, Finset.sum_congr rfl hterm,
    ← image_combFinsetSub (B := B) (L := combLen B α) n w]
  exact (Finset.sum_image (f := fun u : List (Fin B) × ℕ =>
    combVoltage B (combLen B α) false n w u * a u) (fun x _ y _ h => Subtype.ext h)).symm

theorem eq_top_of_forall_ofReal_le {x : ℝ≥0∞} (h : ∀ M : ℝ, ENNReal.ofReal M ≤ x) : x = ⊤ := by
  by_contra hx
  have hM := h (x.toReal + 1)
  rw [ENNReal.ofReal_le_iff_le_toReal hx] at hM
  linarith

/-- **A good pipe at every large level makes the odometer infinite at the root.**
The comb `D_{w,n}` around a good level-`n` pipe contributes at least `λⁿ/4` to
the supremum of `thm:nested-vol`, and `λ > 1`. -/
theorem odometerLimit_pipe_top (hc : CombCond B α) (b : ℝ) (hb : 0 ≤ b)
    (Ccomb : ℝ)
    (hspike : ∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
      ∀ (a : List (Fin B) × ℕ → ℝ) (b' : ℝ), 0 ≤ b' →
        (∀ u ∈ combSet B (combLen B α) n w, -b' ≤ a u) →
        ∀ v ∈ combFirstHalf B (combLen B α) n w,
          (2 + 2 * b' * (Ccomb + 1)) * (combLen B α n : ℝ) - b' ≤ a v →
          combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2
            ≤ ∑' u : ↥(combSet B (combLen B α) n w),
                combVoltage B (combLen B α) e n w u * a u)
    (hgrow : ∀ (e : Bool) (n : ℕ) (w : List (Fin B)), w.length = n → 1 ≤ n →
      combLambda B α ^ n / 4
        ≤ combI B (combLen B α) e n w n * (combLen B α n : ℝ) ^ 2)
    (Y : List (Fin B) × ℕ → ℝ) (hY : ∀ u, 0 ≤ Y u)
    (hgood : ∀ᶠ n : ℕ in atTop, ∃ w : List (Fin B), w.length = n ∧
      ∃ v ∈ combFirstHalf B (combLen B α) n w,
        (2 + 2 * b * (Ccomb + 1)) * (combLen B α n : ℝ) ≤ Y v) :
    RWRS.odometerLimit (pipeSub B (combLen B α))
        (fun v : pipeSites B (combLen B α) => Y (v : List (Fin B) × ℕ) - b + 1)
        (pipeRootSub B (combLen B α)) = ⊤ := by
  have hB : 1 ≤ B := le_trans (by norm_num) hc.1
  have hL : ∀ j, 1 ≤ j → 1 ≤ combLen B α j := fun j _ => one_le_combLen hc j
  haveI : Infinite (pipeSites B (combLen B α)) := pipeSites_infinite hB
  have hG : (pipeSub B (combLen B α)).Connected := pipeSub_connected hL
  -- at every large level the comb contributes at least `λⁿ/4`
  have hstep : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (combLambda B α ^ n / 4)
        ≤ RWRS.odometerLimit (pipeSub B (combLen B α))
            (fun v : pipeSites B (combLen B α) => Y (v : List (Fin B) × ℕ) - b + 1)
            (pipeRootSub B (combLen B α)) := by
    filter_upwards [hgood, eventually_ge_atTop 1] with n hn h1
    obtain ⟨w, hw, v, hv, hYv⟩ := hn
    have hbound := hspike false n w hw h1 (fun u => Y u - b) b hb
      (fun u _ => by have := hY u; linarith) v hv (by linarith [hYv])
    have hgrw := hgrow false n w hw h1
    have hsum := sum_combFinsetSub (B := B) (α := α) n w (fun u => Y u - b)
    have hlow := ofReal_sum_le_odometerLimit' (G := pipeSub B (combLen B α)) hG
      (fun v : pipeSites B (combLen B α) => Y (v : List (Fin B) × ℕ) - b + 1)
      (pipeRootSub B (combLen B α)) (combFinsetSub B (combLen B α) n w)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlow
    have hcongr : ∑ v ∈ combFinsetSub B (combLen B α) n w,
        RWRS.killedGreenReal (pipeSub B (combLen B α))
          ((combFinsetSub B (combLen B α) n w : Finset (pipeSites B (combLen B α))) :
            Set (pipeSites B (combLen B α)))
          (pipeRootSub B (combLen B α)) v
          * ((Y (v : List (Fin B) × ℕ) - b + 1) - 1)
        = ∑' u : ↥(combSet B (combLen B α) n w),
            combVoltage B (combLen B α) false n w u * (Y u - b) := by
      rw [← hsum]
      exact Finset.sum_congr rfl fun v _ => by ring_nf
    rw [hcongr]
    linarith
  -- and `λ > 1`
  have hlam : 1 < combLambda B α := hc.2.2.2.2.2.2
  refine eq_top_of_forall_ofReal_le fun M => ?_
  have htend : Tendsto (fun n : ℕ => combLambda B α ^ n / 4) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) (tendsto_pow_atTop_atTop_of_one_lt hlam)
  obtain ⟨n, hn1, hn2⟩ := ((htend.eventually_ge_atTop M).and hstep).exists
  exact le_trans (ENNReal.ofReal_le_ofReal hn1) hn2

end RWRS.Support
