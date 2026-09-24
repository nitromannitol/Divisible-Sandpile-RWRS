/-
The sum over the vertices of the local-time moments.

Conditioning on the first visit to `v` costs the heat kernel from the start and
leaves the moment at `v` itself, which the previous module bounds uniformly; the
heat kernel from the start is a sub-probability on every finite set of targets,
so the sum over the vertices costs only the horizon `n`.
-/
import RWRS.Support.LocalTimeMoment

namespace RWRS.Support

open scoped Classical ENNReal

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- A nonnegative family whose finite sums are bounded has a bounded sum. -/
theorem tsum_ofReal_le_of_sum_le {f : V → ℝ} (hf : ∀ v, 0 ≤ f v) {C : ℝ}
    (h : ∀ S : Finset V, ∑ v ∈ S, f v ≤ C) :
    ∑' v : V, ENNReal.ofReal (f v) ≤ ENNReal.ofReal C := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => hf v)]
  exact ENNReal.ofReal_le_ofReal (h S)

/-- **The local-time moments summed over the vertices.** -/
theorem sum_walkExp_localTime_rpow_le [Infinite V] (hG : G.Connected) {d_s A p : ℝ}
    (hds : 0 < d_s) (hsp : RWRS.SpectralDimensionBound G d_s A) (hp : 1 ≤ p)
    (x : V) {n : ℕ} (hn : 1 ≤ n) (S : Finset V) :
    ∑ v ∈ S, walkExp G n x (fun X => ((RWRS.localTime n v X : ℕ) : ℝ) ^ p)
      ≤ p * momConst ⌈p⌉₊ * clockH A d_s n ^ (p - 1) * (n : ℝ) := by
  classical
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hCnn : (0 : ℝ) ≤ momConst ⌈p⌉₊ * clockH A d_s n ^ (p - 1) := by
    have h1 := (momConst_pos ⌈p⌉₊).le
    have h2 := (Real.rpow_pos_of_pos (clockH_pos A d_s hn) (p - 1)).le
    positivity
  -- each vertex
  have hone : ∀ v : V,
      walkExp G n x (fun X => ((RWRS.localTime n v X : ℕ) : ℝ) ^ p)
        ≤ p * ∑ k ∈ Finset.range n,
            heat G k x v * (momConst ⌈p⌉₊ * clockH A d_s n ^ (p - 1)) := by
    intro v
    have hpath : ∀ X : ℕ → V, ((RWRS.localTime n v X : ℕ) : ℝ) ^ p
        ≤ p * ∑ k ∈ Finset.range n, (if X k = v then (1 : ℝ) else 0)
            * ((tailTime k n v X : ℕ) : ℝ) ^ (p - 1) :=
      fun X => localTime_rpow_le hp n v X
    refine le_trans (walkExp_mono hpath) ?_
    rw [walkExp_const_mul, walkExp_finsetSum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (by linarith)
    have hklt : k < n := Finset.mem_range.1 hk
    have hkn : k ≤ n := le_of_lt hklt
    have hnk : 1 ≤ n - k := by omega
    have hrw : walkExp G n x (fun X => (if X k = v then (1 : ℝ) else 0)
        * ((tailTime k n v X : ℕ) : ℝ) ^ (p - 1))
        = heat G k x v * walkExp G (n - k) v
            (fun Y => ((RWRS.localTime (n - k) v Y : ℕ) : ℝ) ^ (p - 1)) := by
      rw [← walkExp_markov (G := G) v
        (fun Y => ((RWRS.localTime (n - k) v Y : ℕ) : ℝ) ^ (p - 1)) k n x hkn]
      refine walkExp_congr fun X _ => ?_
      rw [tailTime_eq_localTime]
    rw [hrw]
    refine mul_le_mul_of_nonneg_left ?_ (heat_nonneg k x v)
    have hpj : p ≤ (⌈p⌉₊ : ℝ) := Nat.le_ceil p
    have hsub := walkExp_localTime_rpow_le hG hds hsp ⌈p⌉₊ (p - 1) (by linarith)
      (by linarith) (n - k) hnk v
    refine le_trans hsub ?_
    have hmono : clockH A d_s (n - k) ^ (p - 1) ≤ clockH A d_s n ^ (p - 1) :=
      Real.rpow_le_rpow (clockH_pos A d_s hnk).le (clockH_mono A d_s (by omega)) (by linarith)
    exact mul_le_mul_of_nonneg_left hmono (momConst_pos _).le
  refine le_trans (Finset.sum_le_sum fun v _ => hone v) ?_
  rw [← Finset.mul_sum]
  have hswap : ∑ v ∈ S, ∑ k ∈ Finset.range n,
      heat G k x v * (momConst ⌈p⌉₊ * clockH A d_s n ^ (p - 1))
      = (∑ k ∈ Finset.range n, ∑ v ∈ S, heat G k x v)
          * (momConst ⌈p⌉₊ * clockH A d_s n ^ (p - 1)) := by
    rw [Finset.sum_mul, Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
  rw [hswap]
  have hheat : ∑ k ∈ Finset.range n, ∑ v ∈ S, heat G k x v ≤ (n : ℝ) := by
    refine le_trans (Finset.sum_le_sum fun k _ => sum_heat_le_one hdeg k x S) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hstep : (∑ k ∈ Finset.range n, ∑ v ∈ S, heat G k x v)
      * (momConst ⌈p⌉₊ * clockH A d_s n ^ (p - 1))
      ≤ (n : ℝ) * (momConst ⌈p⌉₊ * clockH A d_s n ^ (p - 1)) :=
    mul_le_mul_of_nonneg_right hheat hCnn
  have hfin := mul_le_mul_of_nonneg_left hstep (by linarith : (0:ℝ) ≤ p)
  refine le_trans hfin (le_of_eq ?_)
  ring

end RWRS.Support
