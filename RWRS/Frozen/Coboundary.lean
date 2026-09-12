/-
Lemma 6.5 of `rwrs.tex`, frozen.  `rwrs.tex:1478-1480` (label
`ex:coboundary`):

  "Let $f\colon V\to[0,\infty)$ and set $\sigma\coloneqq1-\Delta f$.  Then
   $u_\infty(x)\leq f(x)$ for every $x\in V$; in particular, $\sigma$
   stabilizes."

`u_∞(x)` lives in `[0,∞]` and is compared with `f(x)` pushed there by
`ENNReal.ofReal`, which is the value of `f(x)` since `f ≥ 0`.
-/
import RWRS.Support.Representation

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.coboundary [Infinite V] (hG : G.Connected) (f : V → ℝ)
    (hf : ∀ v : V, 0 ≤ f v) :
    (∀ x : V, RWRS.odometerLimit G (fun v => 1 - RWRS.laplacian G f v) x
        ≤ ENNReal.ofReal (f x)) ∧
      RWRS.Stabilizes G (fun v => 1 - RWRS.laplacian G f v)
-- FROZEN-STATEMENT-END
:= by
  have hd : ∀ x : V, (G.degree x : ℝ) ≠ 0 := fun x =>
    Nat.cast_ne_zero.mpr (RWRS.Support.degree_pos hG x).ne'
  have hζ : ∀ x : V, RWRS.scenery G (fun v => 1 - RWRS.laplacian G f v) x
      = f x - RWRS.walkOp G f x := by
    intro x
    have := RWRS.Support.laplacian_div (G := G) hG f x
    rw [RWRS.scenery,
      show (1 - RWRS.laplacian G f x - 1) = -RWRS.laplacian G f x from by ring,
      neg_div, this]
    ring
  have key : ∀ (n : ℕ) (x : V),
      RWRS.odometer G (fun v => 1 - RWRS.laplacian G f v) n x ≤ f x := by
    intro n
    induction n with
    | zero => intro x; simpa [RWRS.odometer] using hf x
    | succ n ih =>
        intro x
        rw [RWRS.Frozen.recursion hG _ n x, hζ]
        refine max_le ?_ (hf x)
        have := RWRS.Support.walkOp_mono (G := G) ih x
        linarith
  refine ⟨fun x => ?_, fun v => ?_⟩
  · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (key n x)
  · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun n => ENNReal.ofReal_le_ofReal (key n v))
