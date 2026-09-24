/-
`lem:fuk-nagaev` applied to a weighted sum of the scenery over a finite set of
vertices.

The three cited inequalities quantify over a probability space and an index set
in the lowest universe.  The scenery lives on the vertex set of a graph, at an
arbitrary universe, so the inequalities are applied to the i.i.d. field indexed
by `Fin n` and the answer is carried back by `FinsetTransfer`.
-/
import RWRS.Support.FinsetTransfer
import RWRS.Support.SharpIndep

namespace RWRS.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {V : Type*} {ν : Measure ℝ} [IsProbabilityMeasure ν]

/-- A bijection of `Fin S.card` with the sites of `S`. -/
noncomputable def finsetEquiv (S : Finset V) : Fin S.card ≃ ((S : Set V) : Type _) :=
  S.equivFin.symm.trans (Equiv.subtypeEquivRight fun _ => Finset.mem_coe.symm)

theorem finsetEquiv_mem (S : Finset V) (j : Fin S.card) :
    ((finsetEquiv S j : (S : Set V)) : V) ∈ S :=
  (finsetEquiv S j).2

/-- The `p`-th absolute moment of a weighted coordinate. -/
theorem lintegral_abs_weighted_rpow {n : ℕ} (c p : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (i : Fin n) :
    (∫⁻ z : Fin n → ℝ, ENNReal.ofReal (|c * f (z i)| ^ p) ∂(RWRS.iidLaw (Fin n) ν))
      = ENNReal.ofReal (|c| ^ p) * ∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν := by
  have hpt : ∀ y : ℝ, ENNReal.ofReal (|c * f y| ^ p)
      = ENNReal.ofReal (|c| ^ p) * ENNReal.ofReal (|f y| ^ p) := by
    intro y
    rw [abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg (f y)),
      ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg c) p)]
  have hmeas : Measurable fun y : ℝ => ENNReal.ofReal (|f y| ^ p) := by
    fun_prop
  calc (∫⁻ z : Fin n → ℝ, ENNReal.ofReal (|c * f (z i)| ^ p) ∂(RWRS.iidLaw (Fin n) ν))
      = ∫⁻ z : Fin n → ℝ, ENNReal.ofReal (|c| ^ p) * ENNReal.ofReal (|f (z i)| ^ p)
          ∂(RWRS.iidLaw (Fin n) ν) := by
        exact lintegral_congr fun z => hpt (z i)
    _ = ENNReal.ofReal (|c| ^ p)
          * ∫⁻ z : Fin n → ℝ, ENNReal.ofReal (|f (z i)| ^ p) ∂(RWRS.iidLaw (Fin n) ν) :=
        lintegral_const_mul _ (hmeas.comp (measurable_pi_apply i))
    _ = ENNReal.ofReal (|c| ^ p) * ∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν := by
        rw [lintegral_coord i hmeas]

/-- **The polynomial tail of a weighted sum of the scenery**, part (a) of
`lem:fuk-nagaev` on an arbitrary vertex set. -/
theorem meas_weighted_sum_ge {p Cp : ℝ}
    (hFN : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|} ≤ ENNReal.ofReal (Cp * Mp / t ^ p))
    (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hfint : Integrable f ν) (hf0 : ∫ z, f z ∂ν = 0)
    (hfp : (∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν) ≠ ⊤)
    (t : ℝ) (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|}
      ≤ ENNReal.ofReal (Cp * (∑ v ∈ S, |w v| ^ p
          * (∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν).toReal) / t ^ p) := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw (Fin S.card) ν) := instIsProbabilityMeasureIid ν
  set n : ℕ := S.card with hn
  set e : Fin n ≃ ((S : Set V) : Type _) := finsetEquiv S with he
  set m : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν with hm
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun i z => w ((e i : (S : Set V)) : V) * f (z i) with hY
  -- the hypotheses of the cited inequality
  have hindep : iIndepFun Y (RWRS.iidLaw (Fin n) ν) := by
    have h := (iIndepFun_coord (V := Fin n) ν).comp
      (fun i (z : ℝ) => w ((e i : (S : Set V)) : V) * f z)
      (fun i => hf.const_mul _)
    exact h
  have hint : ∀ i, Integrable (Y i) (RWRS.iidLaw (Fin n) ν) := fun i =>
    (integrable_coord ν i hfint).const_mul _
  have hzero : ∀ i, ∫ z, Y i z ∂(RWRS.iidLaw (Fin n) ν) = 0 := by
    intro i
    rw [hY, integral_const_mul, integral_coord ν i hfint.aestronglyMeasurable, hf0, mul_zero]
  have hmom : ∀ i, (∫⁻ z, ENNReal.ofReal (|Y i z| ^ p) ∂(RWRS.iidLaw (Fin n) ν))
      = ENNReal.ofReal (|w ((e i : (S : Set V)) : V)| ^ p) * m := fun i =>
    lintegral_abs_weighted_rpow _ p hf i
  have hmomfin : ∀ i, (∫⁻ z, ENNReal.ofReal (|Y i z| ^ p) ∂(RWRS.iidLaw (Fin n) ν)) ≠ ⊤ := by
    intro i
    rw [hmom i]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfp
  have hMp : (∑ v ∈ S, |w v| ^ p * m.toReal)
      = ∑ i, (∫⁻ z, ENNReal.ofReal (|Y i z| ^ p) ∂(RWRS.iidLaw (Fin n) ν)).toReal := by
    rw [sum_finset_eq_sum_fin e (fun v => |w v| ^ p * m.toReal)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmom i, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) p)]
  -- the transferred event
  have hEmeas : MeasurableSet {z : Fin n → ℝ | t ≤ |∑ i, Y i z|} := by
    refine measurableSet_le measurable_const ?_
    have hsum : Measurable fun z : Fin n → ℝ => ∑ i, Y i z :=
      Finset.measurable_sum _ fun i _ => (hf.comp (measurable_pi_apply i)).const_mul _
    fun_prop
  have hset : {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|}
      = {ξ : V → ℝ | (fun j : Fin n => ξ ((e j : (S : Set V)) : V))
          ∈ {z : Fin n → ℝ | t ≤ |∑ i, Y i z|}} := by
    ext ξ
    simp only [Set.mem_setOf_eq, hY]
    rw [sum_finset_eq_sum_fin e (fun v => w v * f (ξ v))]
  rw [hset, meas_readAlong (S : Set V) e hEmeas, hMp]
  exact hFN (RWRS.iidLaw (Fin n) ν) inferInstance Y hindep hint hzero _ rfl hmomfin t ht


/-- **The Bernstein tail of a weighted sum of the scenery**, part (c) of
`lem:fuk-nagaev` on an arbitrary vertex set. -/
theorem meas_weighted_sum_ge_bernstein
    (hBer : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ M B : ℝ, 0 < M → 0 < B → (∀ i, ∀ᵐ ω ∂P, |Y i ω| ≤ M) →
          B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P → (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))))
    (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hfint : Integrable f ν) (hfsq : Integrable (fun z => f z ^ 2) ν)
    (hf0 : ∫ z, f z ∂ν = 0)
    (M B : ℝ) (hM : 0 < M) (hB : 0 < B)
    (hbd : ∀ v ∈ S, ∀ z : ℝ, |w v * f z| ≤ M)
    (hB2 : B ^ 2 = ∑ v ∈ S, w v ^ 2 * ∫ z, f z ^ 2 ∂ν)
    (t : ℝ) (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2 / 2) / (B ^ 2 + M * t / 3))) := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw (Fin S.card) ν) := instIsProbabilityMeasureIid ν
  set n : ℕ := S.card with hn
  set e : Fin n ≃ ((S : Set V) : Type _) := finsetEquiv S with he
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun i z => w ((e i : (S : Set V)) : V) * f (z i) with hY
  have hindep : iIndepFun Y (RWRS.iidLaw (Fin n) ν) :=
    (iIndepFun_coord (V := Fin n) ν).comp
      (fun i (z : ℝ) => w ((e i : (S : Set V)) : V) * f z) (fun i => hf.const_mul _)
  have hint : ∀ i, Integrable (Y i) (RWRS.iidLaw (Fin n) ν) := fun i =>
    (integrable_coord ν i hfint).const_mul _
  have hzero : ∀ i, ∫ z, Y i z ∂(RWRS.iidLaw (Fin n) ν) = 0 := by
    intro i
    rw [hY, integral_const_mul, integral_coord ν i hfint.aestronglyMeasurable, hf0, mul_zero]
  have hbdd : ∀ i, ∀ᵐ z ∂(RWRS.iidLaw (Fin n) ν), |Y i z| ≤ M := by
    intro i
    refine Filter.Eventually.of_forall fun z => ?_
    exact hbd _ (finsetEquiv_mem S i) (z i)
  have hsq : ∀ i, ∫ z, Y i z ^ 2 ∂(RWRS.iidLaw (Fin n) ν)
      = w ((e i : (S : Set V)) : V) ^ 2 * ∫ y, f y ^ 2 ∂ν := by
    intro i
    have hpt : ∀ z : Fin n → ℝ, Y i z ^ 2
        = w ((e i : (S : Set V)) : V) ^ 2 * f (z i) ^ 2 := fun z => by rw [hY]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_coord ν i hfsq.aestronglyMeasurable]
  have hsqint : ∀ i, Integrable (fun z => Y i z ^ 2) (RWRS.iidLaw (Fin n) ν) := by
    intro i
    have hpt : (fun z : Fin n → ℝ => Y i z ^ 2)
        = fun z => w ((e i : (S : Set V)) : V) ^ 2 * f (z i) ^ 2 := by
      funext z; rw [hY]; ring
    rw [hpt]
    exact (integrable_coord ν i hfsq).const_mul _
  have hB2' : B ^ 2 = ∑ i, ∫ z, Y i z ^ 2 ∂(RWRS.iidLaw (Fin n) ν) := by
    rw [hB2, sum_finset_eq_sum_fin e (fun v => w v ^ 2 * ∫ y, f y ^ 2 ∂ν)]
    exact Finset.sum_congr rfl fun i _ => (hsq i).symm
  have hEmeas : MeasurableSet {z : Fin n → ℝ | t ≤ |∑ i, Y i z|} := by
    refine measurableSet_le measurable_const ?_
    have hsum : Measurable fun z : Fin n → ℝ => ∑ i, Y i z :=
      Finset.measurable_sum _ fun i _ => (hf.comp (measurable_pi_apply i)).const_mul _
    fun_prop
  have hset : {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|}
      = {ξ : V → ℝ | (fun j : Fin n => ξ ((e j : (S : Set V)) : V))
          ∈ {z : Fin n → ℝ | t ≤ |∑ i, Y i z|}} := by
    ext ξ
    simp only [Set.mem_setOf_eq, hY]
    rw [sum_finset_eq_sum_fin e (fun v => w v * f (ξ v))]
  rw [hset, meas_readAlong (S : Set V) e hEmeas]
  exact hBer (RWRS.iidLaw (Fin n) ν) inferInstance Y hindep hint hzero M B hM hB hbdd hB2'
    hsqint t ht


/-- **The polynomial and Gaussian tail of a weighted sum of the scenery**, part
(b) of `lem:fuk-nagaev` on an arbitrary vertex set. -/
theorem meas_weighted_sum_ge_gaussian {p c Cp : ℝ}
    (hFN : ∀ {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω),
      IsProbabilityMeasure P → ∀ (Y : ι → Ω → ℝ), iIndepFun Y P →
        (∀ i, Integrable (Y i) P) → (∀ i, ∫ ω, Y i ω ∂P = 0) →
        ∀ Mp B : ℝ, Mp = ∑ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P).toReal →
          (∀ i, (∫⁻ ω, ENNReal.ofReal (|Y i ω| ^ p) ∂P) ≠ ⊤) →
          0 < B → B ^ 2 = ∑ i, ∫ ω, Y i ω ^ 2 ∂P →
          (∀ i, Integrable (fun ω => Y i ω ^ 2) P) →
          ∀ t : ℝ, 0 < t →
            P {ω | t ≤ |∑ i, Y i ω|}
              ≤ ENNReal.ofReal (Cp * Mp / t ^ p + 2 * Real.exp (-c * t ^ 2 / B ^ 2)))
    (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hfint : Integrable f ν) (hfsq : Integrable (fun z => f z ^ 2) ν)
    (hf0 : ∫ z, f z ∂ν = 0)
    (hfp : (∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν) ≠ ⊤)
    (B : ℝ) (hB : 0 < B) (hB2 : B ^ 2 = ∑ v ∈ S, w v ^ 2 * ∫ z, f z ^ 2 ∂ν)
    (t : ℝ) (ht : 0 < t) :
    RWRS.iidLaw V ν {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|}
      ≤ ENNReal.ofReal (Cp * (∑ v ∈ S, |w v| ^ p
          * (∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν).toReal) / t ^ p
        + 2 * Real.exp (-c * t ^ 2 / B ^ 2)) := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw (Fin S.card) ν) := instIsProbabilityMeasureIid ν
  set n : ℕ := S.card with hn
  set e : Fin n ≃ ((S : Set V) : Type _) := finsetEquiv S with he
  set m : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (|f y| ^ p) ∂ν with hm
  set Y : Fin n → (Fin n → ℝ) → ℝ := fun i z => w ((e i : (S : Set V)) : V) * f (z i) with hY
  have hindep : iIndepFun Y (RWRS.iidLaw (Fin n) ν) :=
    (iIndepFun_coord (V := Fin n) ν).comp
      (fun i (z : ℝ) => w ((e i : (S : Set V)) : V) * f z) (fun i => hf.const_mul _)
  have hint : ∀ i, Integrable (Y i) (RWRS.iidLaw (Fin n) ν) := fun i =>
    (integrable_coord ν i hfint).const_mul _
  have hzero : ∀ i, ∫ z, Y i z ∂(RWRS.iidLaw (Fin n) ν) = 0 := by
    intro i
    rw [hY, integral_const_mul, integral_coord ν i hfint.aestronglyMeasurable, hf0, mul_zero]
  have hmom : ∀ i, (∫⁻ z, ENNReal.ofReal (|Y i z| ^ p) ∂(RWRS.iidLaw (Fin n) ν))
      = ENNReal.ofReal (|w ((e i : (S : Set V)) : V)| ^ p) * m := fun i =>
    lintegral_abs_weighted_rpow _ p hf i
  have hmomfin : ∀ i, (∫⁻ z, ENNReal.ofReal (|Y i z| ^ p) ∂(RWRS.iidLaw (Fin n) ν)) ≠ ⊤ := by
    intro i
    rw [hmom i]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfp
  have hMp : (∑ v ∈ S, |w v| ^ p * m.toReal)
      = ∑ i, (∫⁻ z, ENNReal.ofReal (|Y i z| ^ p) ∂(RWRS.iidLaw (Fin n) ν)).toReal := by
    rw [sum_finset_eq_sum_fin e (fun v => |w v| ^ p * m.toReal)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmom i, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg (abs_nonneg _) p)]
  have hsq : ∀ i, ∫ z, Y i z ^ 2 ∂(RWRS.iidLaw (Fin n) ν)
      = w ((e i : (S : Set V)) : V) ^ 2 * ∫ y, f y ^ 2 ∂ν := by
    intro i
    have hpt : ∀ z : Fin n → ℝ, Y i z ^ 2
        = w ((e i : (S : Set V)) : V) ^ 2 * f (z i) ^ 2 := fun z => by rw [hY]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_coord ν i hfsq.aestronglyMeasurable]
  have hsqint : ∀ i, Integrable (fun z => Y i z ^ 2) (RWRS.iidLaw (Fin n) ν) := by
    intro i
    have hpt : (fun z : Fin n → ℝ => Y i z ^ 2)
        = fun z => w ((e i : (S : Set V)) : V) ^ 2 * f (z i) ^ 2 := by
      funext z; rw [hY]; ring
    rw [hpt]
    exact (integrable_coord ν i hfsq).const_mul _
  have hB2' : B ^ 2 = ∑ i, ∫ z, Y i z ^ 2 ∂(RWRS.iidLaw (Fin n) ν) := by
    rw [hB2, sum_finset_eq_sum_fin e (fun v => w v ^ 2 * ∫ y, f y ^ 2 ∂ν)]
    exact Finset.sum_congr rfl fun i _ => (hsq i).symm
  have hEmeas : MeasurableSet {z : Fin n → ℝ | t ≤ |∑ i, Y i z|} := by
    refine measurableSet_le measurable_const ?_
    have hsum : Measurable fun z : Fin n → ℝ => ∑ i, Y i z :=
      Finset.measurable_sum _ fun i _ => (hf.comp (measurable_pi_apply i)).const_mul _
    fun_prop
  have hset : {ξ : V → ℝ | t ≤ |∑ v ∈ S, w v * f (ξ v)|}
      = {ξ : V → ℝ | (fun j : Fin n => ξ ((e j : (S : Set V)) : V))
          ∈ {z : Fin n → ℝ | t ≤ |∑ i, Y i z|}} := by
    ext ξ
    simp only [Set.mem_setOf_eq, hY]
    rw [sum_finset_eq_sum_fin e (fun v => w v * f (ξ v))]
  rw [hset, meas_readAlong (S : Set V) e hEmeas, hMp]
  exact hFN (RWRS.iidLaw (Fin n) ν) inferInstance Y hindep hint hzero _ B rfl hmomfin hB hB2'
    hsqint t ht

end RWRS.Support
