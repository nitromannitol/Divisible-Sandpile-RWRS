/-
Bernstein's inequality for a weighted sum of the scenery read through
SITE-DEPENDENT maps, for `prop:poly-growth`.

`prop:subcritical` reads every site of the scenery through the same map, the
centring `z ↦ z - m`, and `RWRS.Support.meas_weighted_sum_ge_bernstein` is
part (c) of `lem:fuk-nagaev` in that form.  Step 4 of `prop:poly-growth` reads
the site `v` through `siteShift ρ M m (t v)`, which depends on the site, so the
same transfer is made once more with the map carried by the site.  The
coordinates of an i.i.d. field remain independent after site-dependent maps are
applied to them, which is the only property of the field the inequality uses.
-/
import RWRS.Support.FukNagaevWeighted

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {V : Type*} {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- **The Bernstein tail of a weighted sum of the scenery read through
site-dependent maps**, part (c) of `lem:fuk-nagaev` on an arbitrary vertex
set. -/
theorem meas_weighted_sum_ge_bernstein_site
    (hBer : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
          B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
    (S : Finset V) (w : V → ℝ) {f : V → ℝ → ℝ} (hf : ∀ v : V, Measurable (f v))
    (hfint : ∀ v : V, Integrable (f v) ν) (hfsq : ∀ v : V, Integrable (fun z => f v z ^ 2) ν)
    (hf0 : ∀ v : V, ∫ z, f v z ∂ν = 0)
    (M B : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hbd : ∀ v ∈ S, ∀ z : ℝ, |w v * f v z| ≤ M)
    (hB2 : B ^ 2 = ∑ v ∈ S, w v ^ 2 * ∫ z, f v z ^ 2 ∂ν)
    (t : ℝ) (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f v (ξ v)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))) := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw (Fin S.card) ν) := instIsProbabilityMeasureIid ν
  set n : ℕ := S.card with hn
  set e : Fin n ≃ ((S : Set V) : Type _) := finsetEquiv S with he
  set Y : Fin n → (Fin n → ℝ) → ℝ :=
    fun i z => w ((e i : (S : Set V)) : V) * f ((e i : (S : Set V)) : V) (z i) with hY
  have hindep : iIndepFun Y (RWRS.iidLaw (Fin n) ν) :=
    (iIndepFun_coord (V := Fin n) ν).comp
      (fun i (z : ℝ) => w ((e i : (S : Set V)) : V) * f ((e i : (S : Set V)) : V) z)
      (fun i => (hf _).const_mul _)
  have hint : ∀ i, Integrable (Y i) (RWRS.iidLaw (Fin n) ν) := fun i =>
    (integrable_coord ν i (hfint _)).const_mul _
  have hzero : ∀ i, ∫ z, Y i z ∂(RWRS.iidLaw (Fin n) ν) = 0 := by
    intro i
    rw [hY, integral_const_mul, integral_coord ν i (hfint _).aestronglyMeasurable, hf0, mul_zero]
  have hbdd : ∀ i, ∀ᵐ z ∂(RWRS.iidLaw (Fin n) ν), |Y i z| ≤ M := by
    intro i
    refine Filter.Eventually.of_forall fun z => ?_
    exact hbd _ (finsetEquiv_mem S i) (z i)
  have hsq : ∀ i, ∫ z, Y i z ^ 2 ∂(RWRS.iidLaw (Fin n) ν)
      = w ((e i : (S : Set V)) : V) ^ 2
        * ∫ y, f ((e i : (S : Set V)) : V) y ^ 2 ∂ν := by
    intro i
    have hpt : ∀ z : Fin n → ℝ, Y i z ^ 2
        = w ((e i : (S : Set V)) : V) ^ 2
          * f ((e i : (S : Set V)) : V) (z i) ^ 2 := fun z => by rw [hY]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_coord ν i (hfsq _).aestronglyMeasurable]
  have hsqint : ∀ i, Integrable (fun z => Y i z ^ 2) (RWRS.iidLaw (Fin n) ν) := by
    intro i
    have hpt : (fun z : Fin n → ℝ => Y i z ^ 2)
        = fun z => w ((e i : (S : Set V)) : V) ^ 2
          * f ((e i : (S : Set V)) : V) (z i) ^ 2 := by
      funext z; rw [hY]; ring
    rw [hpt]
    exact (integrable_coord ν i (hfsq _)).const_mul _
  have hB2' : B ^ 2 = ∑ i, ∫ z, Y i z ^ 2 ∂(RWRS.iidLaw (Fin n) ν) := by
    rw [hB2, sum_finset_eq_sum_fin e (fun v => w v ^ 2 * ∫ y, f v y ^ 2 ∂ν)]
    exact Finset.sum_congr rfl fun i _ => (hsq i).symm
  have hEmeas : MeasurableSet {z : Fin n → ℝ | t ≤ |∑ i, Y i z|} := by
    refine measurableSet_le measurable_const ?_
    have hsum : Measurable fun z : Fin n → ℝ => ∑ i, Y i z :=
      Finset.measurable_sum _ fun i _ => ((hf _).comp (measurable_pi_apply i)).const_mul _
    fun_prop
  have hset : {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f v (ξ v)|}
      = {ξ : V → ℝ | (fun j : Fin n => ξ ((e j : (S : Set V)) : V))
          ∈ {z : Fin n → ℝ | t ≤ |∑ i, Y i z|}} := by
    ext ξ
    simp only [Set.mem_setOf_eq, hY]
    rw [sum_finset_eq_sum_fin e (fun v => w v * f v (ξ v))]
  rw [hset, meas_readAlong (S : Set V) e hEmeas]
  exact hBer (RWRS.iidLaw (Fin n) ν) inferInstance Y hindep hint hzero M B hM hB hbdd hB2'
    hsqint t ht

end RWRS.Support
