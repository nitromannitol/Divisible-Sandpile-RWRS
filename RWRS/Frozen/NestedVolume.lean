/-
Theorem 3.4 of `rwrs.tex`, frozen.  `rwrs.tex:448-471` (label
`thm:nested-vol`):

  "Assume $G$ is infinite.  Then
   $u_\infty(o)=\max\{0,\sup_{C\subseteq V, C\text{ finite connected},
     o\in C}\sum_{v\in C}g_C(v)(\sigma(v)-1)\}$."

Both sides live in `[0,∞]`.  The supremum over the empty family is `0` and
`ENNReal.ofReal` sends a negative sum to `0`, so the `max` with `0` of the
paper is carried by the target type and needs no separate term.  Each `C` is a
`Finset`, which is the paper's finiteness; since `G` is infinite, `V ∖ C` is
automatically nonempty.  `hG` is the standing assumption of `ssec:notation`.
-/
import RWRS.Support.BallWalk

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.nestedVolume [Infinite V] (hG : G.Connected) (σ : V → ℝ) (o : V) :
    RWRS.odometerLimit G σ o =
      ⨆ (C : Finset V) (_ : (G.induce (C : Set V)).Connected) (_ : o ∈ C),
        ENNReal.ofReal (∑ v ∈ C, RWRS.killedGreenReal G (C : Set V) o v * (σ v - 1))
-- FROZEN-STATEMENT-END
:= by
  refine le_antisymm (iSup_le fun n => RWRS.Support.ofReal_odometer_le_iSup' hG σ o n) ?_
  refine iSup_le fun C => iSup_le fun _ => iSup_le fun _ => ?_
  exact RWRS.Support.ofReal_sum_le_odometerLimit' hG σ o C
