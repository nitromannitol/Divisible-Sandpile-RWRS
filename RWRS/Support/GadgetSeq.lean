/-
The depths of the gadgets of `sec:recurrent-nonstab`, chosen inductively.

At every step the three conditions `eq:rec-cond-sep`, `eq:rec-cond-vol` and
`eq:rec-cond-div` ask a positive power of the gadget radius to dominate
quantities already fixed by the earlier steps, and every one of them therefore
holds for all large depths.  The state carried along the recursion is the last
depth together with the running total of the gadget sizes, which is what
`eq:rec-cond-vol` reads.
-/
import RWRS.Support.GadgetChoice

namespace RWRS.Support

open Filter

variable {B : ℕ} {α : ℝ}

section
variable {d_f ρ δ c_loc : ℝ} (hc : CombCond B α) (hdf : 0 < d_f) (hρ : 0 < ρ)
  (hcloc : 0 < c_loc) (hρδ : ρ * (d_f + 1) < δ)

/-- The next gadget depth, chosen so that the three conditions of
`sec:recurrent-nonstab` hold. -/
noncomputable def nextGadget (M0 : ℕ) (S : ℝ) (k : ℕ) : ℕ :=
  (exists_next_gadget hc hdf hρ hcloc hρδ M0 S k).choose

theorem nextGadget_spec (M0 : ℕ) (S : ℝ) (k : ℕ) :
    M0 < nextGadget hc hdf hρ hcloc hρδ M0 S k ∧
      ⌈(gadgetRadius (combLen B α) M0 : ℝ) ^ ρ⌉₊ + gadgetRadius (combLen B α) M0
        < ⌈(gadgetRadius (combLen B α)
            (nextGadget hc hdf hρ hcloc hρδ M0 S k) : ℝ) ^ ρ⌉₊ ∧
      S ≤ (⌈(gadgetRadius (combLen B α)
            (nextGadget hc hdf hρ hcloc hρδ M0 S k) : ℝ) ^ ρ⌉₊ : ℝ) ^ d_f ∧
      ((⌈(gadgetRadius (combLen B α)
            (nextGadget hc hdf hρ hcloc hρδ M0 S k) : ℝ) ^ ρ⌉₊ : ℝ) + 1) ^ (d_f + 1) * (k : ℝ)
        ≤ c_loc * (gadgetRadius (combLen B α)
            (nextGadget hc hdf hρ hcloc hρδ M0 S k) : ℝ) ^ δ :=
  (exists_next_gadget hc hdf hρ hcloc hρδ M0 S k).choose_spec

/-- The depths of the gadgets, with the running total of their sizes. -/
noncomputable def gadgetSeq : ℕ → ℕ × ℝ
  | 0 => (1, (gadgetSize B (combLen B α) 1 : ℝ))
  | k + 1 =>
      let M := nextGadget hc hdf hρ hcloc hρδ (gadgetSeq k).1 (gadgetSeq k).2 (k + 1)
      (M, (gadgetSeq k).2 + (gadgetSize B (combLen B α) M : ℝ))

/-- The depth of the `k`-th gadget. -/
noncomputable def mSeq (k : ℕ) : ℕ := (gadgetSeq hc hdf hρ hcloc hρδ k).1

/-- The ray vertex the `k`-th gadget is attached to. -/
noncomputable def sSeq (k : ℕ) : ℕ :=
  ⌈(gadgetRadius (combLen B α) (mSeq hc hdf hρ hcloc hρδ k) : ℝ) ^ ρ⌉₊

theorem gadgetSeq_snd (k : ℕ) :
    (gadgetSeq hc hdf hρ hcloc hρδ k).2
      = ∑ j ∈ Finset.range (k + 1),
          (gadgetSize B (combLen B α) (mSeq hc hdf hρ hcloc hρδ j) : ℝ) := by
  induction k with
  | zero => simp [gadgetSeq, mSeq]
  | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      rfl

theorem mSeq_lt_succ (k : ℕ) :
    mSeq hc hdf hρ hcloc hρδ k < mSeq hc hdf hρ hcloc hρδ (k + 1) :=
  (nextGadget_spec hc hdf hρ hcloc hρδ _ _ _).1

theorem mSeq_strictMono : StrictMono (mSeq hc hdf hρ hcloc hρδ) :=
  strictMono_nat_of_lt_succ (mSeq_lt_succ hc hdf hρ hcloc hρδ)

theorem sSeq_sep (k : ℕ) :
    sSeq hc hdf hρ hcloc hρδ k
        + gadgetRadius (combLen B α) (mSeq hc hdf hρ hcloc hρδ k)
      < sSeq hc hdf hρ hcloc hρδ (k + 1) :=
  (nextGadget_spec hc hdf hρ hcloc hρδ _ _ _).2.1

theorem sSeq_strictMono : StrictMono (sSeq hc hdf hρ hcloc hρδ) := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  have := sSeq_sep hc hdf hρ hcloc hρδ k
  omega

theorem sSeq_vol (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
        (gadgetSize B (combLen B α) (mSeq hc hdf hρ hcloc hρδ j) : ℝ))
      ≤ (sSeq hc hdf hρ hcloc hρδ (k + 1) : ℝ) ^ d_f := by
  rw [← gadgetSeq_snd hc hdf hρ hcloc hρδ k]
  exact (nextGadget_spec hc hdf hρ hcloc hρδ
    (gadgetSeq hc hdf hρ hcloc hρδ k).1 (gadgetSeq hc hdf hρ hcloc hρδ k).2 (k + 1)).2.2.1

theorem sSeq_div (k : ℕ) :
    ((sSeq hc hdf hρ hcloc hρδ (k + 1) : ℝ) + 1) ^ (d_f + 1) * (((k + 1 : ℕ) : ℝ))
      ≤ c_loc * (gadgetRadius (combLen B α) (mSeq hc hdf hρ hcloc hρδ (k + 1)) : ℝ) ^ δ :=
  (nextGadget_spec hc hdf hρ hcloc hρδ
    (gadgetSeq hc hdf hρ hcloc hρδ k).1 (gadgetSeq hc hdf hρ hcloc hρδ k).2 (k + 1)).2.2.2

end

end RWRS.Support
