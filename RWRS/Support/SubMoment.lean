/-
`eq:poly-moment`: the local-time moments of a discrete interval.

`lem:local-time` bounds `∑_v E_x[L_n(v)^p]` for the walk run from time zero.
The chaining of `prop:subcritical` needs the same bound for the interval
`I = [a,b)`, "by the Markov property at the start of `I`".  The proof is the
proof of `lem:local-time` with the visit times ranging over `I`: the local time
over `I` is the local time of the trajectory started at `a`, the pathwise bound
of `lem:local-time` applies to that trajectory, and the Markov property at each
visit time `a+i` restarts the walk with the remaining horizon `b-(a+i)`, which
is at most `|I|`.  The heat kernel is a sub-probability on every finite set of
targets, so the sum over the vertices costs nothing and the bound is
`C_p |I| Λ_p(|I|)`, uniformly in the starting vertex.
-/
import RWRS.Support.LocalTimeSum
import RWRS.Support.SubIncrement

namespace RWRS.Support

open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- **`eq:poly-moment`.**  The local-time moments of a discrete interval, summed
over any finite set of vertices, uniformly in the starting vertex. -/
theorem sum_walkExp_localTimeOn_rpow_le [Infinite V] (hG : G.Connected) {d_s A p : ℝ}
    (hds : 0 < d_s) (hsp : RWRS.SpectralDimensionBound G d_s A) (hp : 1 ≤ p)
    (x : V) {a b : ℕ} (hab : a < b) (S : Finset V) :
    ∑ v ∈ S, walkExp G b x (fun X => ((localTimeOn a b v X : ℕ) : ℝ) ^ p)
      ≤ p * momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1) * ((b - a : ℕ) : ℝ) := by
  classical
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hba : 1 ≤ b - a := by omega
  have hCnn : (0 : ℝ) ≤ momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1) := by
    have h1 := (momConst_pos ⌈p⌉₊).le
    have h2 := (Real.rpow_pos_of_pos (clockH_pos A d_s hba) (p - 1)).le
    positivity
  have hone : ∀ v : V,
      walkExp G b x (fun X => ((localTimeOn a b v X : ℕ) : ℝ) ^ p)
        ≤ p * ∑ i ∈ Finset.range (b - a),
            heat G (a + i) x v * (momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1)) := by
    intro v
    have hpath : ∀ X : ℕ → V, ((localTimeOn a b v X : ℕ) : ℝ) ^ p
        ≤ p * ∑ i ∈ Finset.range (b - a), (if X (a + i) = v then (1 : ℝ) else 0)
            * ((tailTime i (b - a) v (fun j => X (a + j)) : ℕ) : ℝ) ^ (p - 1) := by
      intro X
      rw [localTimeOn_eq_localTime]
      exact localTime_rpow_le hp (b - a) v (fun j => X (a + j))
    refine le_trans (walkExp_mono hpath) ?_
    rw [walkExp_const_mul, walkExp_finsetSum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by linarith)
    have hilt : i < b - a := Finset.mem_range.1 hi
    have hkb : a + i ≤ b := by omega
    have hnk : 1 ≤ b - (a + i) := by omega
    have hrw : walkExp G b x (fun X => (if X (a + i) = v then (1 : ℝ) else 0)
        * ((tailTime i (b - a) v (fun j => X (a + j)) : ℕ) : ℝ) ^ (p - 1))
        = heat G (a + i) x v * walkExp G (b - (a + i)) v
            (fun Y => ((RWRS.localTime (b - (a + i)) v Y : ℕ) : ℝ) ^ (p - 1)) := by
      rw [← walkExp_markov (G := G) v
        (fun Y => ((RWRS.localTime (b - (a + i)) v Y : ℕ) : ℝ) ^ (p - 1)) (a + i) b x hkb]
      refine walkExp_congr fun X _ => ?_
      have hidx : (fun j => X (a + (i + j))) = fun j => X (a + i + j) := by
        funext j; congr 1; omega
      have hlen : b - a - i = b - (a + i) := by omega
      simp only [tailTime_eq_localTime]
      rw [hidx, hlen]
    rw [hrw]
    refine mul_le_mul_of_nonneg_left ?_ (heat_nonneg (a + i) x v)
    have hpj : p ≤ (⌈p⌉₊ : ℝ) := Nat.le_ceil p
    have hsub := walkExp_localTime_rpow_le hG hds hsp ⌈p⌉₊ (p - 1) (by linarith)
      (by linarith) (b - (a + i)) hnk v
    refine le_trans hsub ?_
    have hmono : clockH A d_s (b - (a + i)) ^ (p - 1) ≤ clockH A d_s (b - a) ^ (p - 1) :=
      Real.rpow_le_rpow (clockH_pos A d_s hnk).le (clockH_mono A d_s (by omega)) (by linarith)
    exact mul_le_mul_of_nonneg_left hmono (momConst_pos _).le
  refine le_trans (Finset.sum_le_sum fun v _ => hone v) ?_
  rw [← Finset.mul_sum]
  have hswap : ∑ v ∈ S, ∑ i ∈ Finset.range (b - a),
      heat G (a + i) x v * (momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1))
      = (∑ i ∈ Finset.range (b - a), ∑ v ∈ S, heat G (a + i) x v)
          * (momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1)) := by
    rw [Finset.sum_mul, Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
  rw [hswap]
  have hheat : ∑ i ∈ Finset.range (b - a), ∑ v ∈ S, heat G (a + i) x v ≤ ((b - a : ℕ) : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun i _ => sum_heat_le_one hdeg (a + i) x S) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hstep : (∑ i ∈ Finset.range (b - a), ∑ v ∈ S, heat G (a + i) x v)
      * (momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1))
      ≤ ((b - a : ℕ) : ℝ) * (momConst ⌈p⌉₊ * clockH A d_s (b - a) ^ (p - 1)) :=
    mul_le_mul_of_nonneg_right hheat hCnn
  have hfin := mul_le_mul_of_nonneg_left hstep (by linarith : (0:ℝ) ≤ p)
  refine le_trans hfin (le_of_eq ?_)
  ring

end RWRS.Support
