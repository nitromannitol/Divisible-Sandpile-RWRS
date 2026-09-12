/-
Theorem 3.2 of `rwrs.tex`, frozen.  `rwrs.tex:393-398` (label `thm:RW`):

  "Let $v_n(x) \coloneqq \sup_{\tau \leq n} \E_x[S_\tau]$, where the supremum
   is taken over stopping times (with respect to the natural filtration of
   $(X_k)_{k\in\N}$) bounded by $n$.  For all $n \geq 0$, we have
   $u_n(x) = v_n(x) = \E_x[S_{\tau_n^*}]$.  Here
   $\tau_n^* \coloneqq \min\{0 \leq k \leq n : v_{n-k}(X_k) = 0\}$."

The first equality is stated as `IsLUB`, so that no junk value of an
unattained supremum can satisfy it, and it says both that `u_n(x)` is an upper
bound for every bounded stopping rule and that it is the least one; that is the
identity `u_n = v_n`, since `RWRS.value` is the supremum of the same set.  The
scenery is the excess mass `ξ = σ - 1`, so the payoff is the paper's
`S_n = ∑_{k<n} ζ(X_k)`.  `hG` and `[Infinite V]` are the standing assumptions of `ssec:notation` and of
Section 3.
-/
import RWRS.Support.Representation

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

-- FROZEN-STATEMENT-BEGIN
theorem RWRS.Frozen.randomWalkRepresentation [Infinite V] (hG : G.Connected) (σ : V → ℝ) (n : ℕ) (x : V) :
    IsLUB (RWRS.stopValues G (RWRS.excess σ) n x) (RWRS.odometer G σ n x) ∧
      RWRS.odometer G σ n x =
        RWRS.walkExp G n x (fun X =>
          RWRS.payoff G (RWRS.excess σ) (RWRS.optimalStop G (RWRS.excess σ) n X) X)
-- FROZEN-STATEMENT-END
:= ⟨RWRS.Support.isLUB_odometer hG σ n x, (RWRS.Support.walkExp_optimalStop hG σ n x).symm⟩
