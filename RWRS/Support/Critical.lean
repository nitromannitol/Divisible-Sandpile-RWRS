/-
The critical regime of `rwrs.tex`: the variance bound and the explosion bound
of `prop:critical`.

The mean payoff at a deterministic time is a finite sum `R_n = ∑_v g_n(o,v)ξ(v)`
of independent variables weighted by the finite-time Green function, so all of
Section 5.1 is finite-dimensional probability on the vertices reachable in `n`
steps.  Three ingredients are assembled here.

- The variance bound is the Efron--Stein inequality against the one-site
  sensitivity of `lem:sensitivity`: resampling one vertex moves the value by at
  most `g_n(o,v)` times the change, and the mean squared change of one
  coordinate of a centred field is twice its variance.
- The lower bound on the mean of the positive part is `lem:positive-part`
  applied to the field truncated at a level `M` chosen so that the truncation
  keeps most of the variance and loses little in `L²`; the no-dominance lemma
  supplies the hypothesis that no weight carries a positive fraction of the
  `ℓ²` mass.
- The two Paley--Zygmund steps turn a mean lower bound and a second-moment
  upper bound into a probability bound, once for the value and once for the
  mean payoff itself.
-/
import RWRS.Support.Sensitivity
import RWRS.Support.ClockRatio
import RWRS.Support.Measurability
import RWRS.Support.WeakLaw
import RWRS.Support.PaleyZygmund
import RWRS.Support.Explosion
import RWRS.Support.PositivePart
import RWRS.Support.Truncation
import RWRS.External.EfronStein
import RWRS.Support.Swap
import LatticeProb.Prob.HewittSavage

namespace RWRS.Support

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-! ### The second moment of an independent centred sum in `L²` -/

section SumTwo

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The second moment of an independent centred sum, under square
integrability alone. -/
theorem integral_sq_finsetSum_two (X : ι → Ω → ℝ) (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (h2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (s : Finset ι) :
    ∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂P = ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
      have hSmem : MemLp (fun ω => ∑ i ∈ s, X i ω) 2 P := by
        have hh := memLp_finsetSum' s (fun i _ => h2 i) (p := 2) (μ := P)
        have he : (∑ i ∈ s, X i) = fun ω => ∑ i ∈ s, X i ω := by
          funext ω; exact Finset.sum_apply ω s X
        rwa [he] at hh
      have hjint : Integrable (X j) P := (h2 j).integrable (by norm_num)
      have hSint : Integrable (fun ω => ∑ i ∈ s, X i ω) P := hSmem.integrable (by norm_num)
      have hj2 : Integrable (fun ω => X j ω ^ 2) P := (h2 j).integrable_sq
      have hS2 : Integrable (fun ω => (∑ i ∈ s, X i ω) ^ 2) P := hSmem.integrable_sq
      have hSj : IndepFun (X j) (fun ω => ∑ i ∈ s, X i ω) P := by
        have h := hindep.indepFun_finsetSum_of_notMem hmeas hj
        have he : (∑ i ∈ s, X i) = fun ω => ∑ i ∈ s, X i ω := by
          funext ω; exact Finset.sum_apply ω s X
        rw [he] at h
        exact h.symm
      have hcross : Integrable (fun ω => 2 * (X j ω * ∑ i ∈ s, X i ω)) P :=
        (hSj.integrable_mul hjint hSint).const_mul 2
      have hxc : ∫ ω, X j ω * (∑ i ∈ s, X i ω) ∂P = 0 := by
        rw [hSj.integral_fun_mul_eq_mul_integral (hmeas j).aestronglyMeasurable
          hSmem.aestronglyMeasurable, hmean j, zero_mul]
      have hrw : (fun ω => (∑ i ∈ insert j s, X i ω) ^ 2)
          = fun ω => X j ω ^ 2 + 2 * (X j ω * ∑ i ∈ s, X i ω) + (∑ i ∈ s, X i ω) ^ 2 := by
        funext ω; rw [Finset.sum_insert hj]; ring
      rw [hrw]
      rw [integral_add (f := fun ω => X j ω ^ 2 + 2 * (X j ω * ∑ i ∈ s, X i ω))
        (g := fun ω => (∑ i ∈ s, X i ω) ^ 2) (hj2.add hcross) hS2,
        integral_add (f := fun ω => X j ω ^ 2)
          (g := fun ω => 2 * (X j ω * ∑ i ∈ s, X i ω)) hj2 hcross,
        integral_const_mul, hxc, ih, Finset.sum_insert hj]
      ring

/-- The mean of the absolute value is at most the square root of the second
moment. -/
theorem integral_abs_le_sqrt (f : Ω → ℝ) (hf : MemLp f 2 P) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  have habs : MemLp (fun ω => |f ω|) 2 P := hf.abs
  have h2 : Integrable (fun ω => |f ω| ^ 2) P := habs.integrable_sq
  have hvar : 0 ≤ variance (fun ω => |f ω|) P := variance_nonneg _ _
  have heq : variance (fun ω => |f ω|) P
      = (∫ ω, |f ω| ^ 2 ∂P) - (∫ ω, |f ω| ∂P) ^ 2 := variance_eq_sub habs
  have hsq : ∀ ω, |f ω| ^ 2 = f ω ^ 2 := fun ω => sq_abs (f ω)
  rw [integral_congr_ae (Filter.Eventually.of_forall hsq)] at heq
  have hnn : (0 : ℝ) ≤ ∫ ω, |f ω| ∂P :=
    integral_nonneg fun ω => abs_nonneg _
  have hle : (∫ ω, |f ω| ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by linarith
  calc ∫ ω, |f ω| ∂P = Real.sqrt ((∫ ω, |f ω| ∂P) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) := Real.sqrt_le_sqrt hle

end SumTwo

/-! ### Weighted sums of a function of the field -/

section Weighted

variable {V : Type*} {ν : Measure ℝ} [IsProbabilityMeasure ν]

theorem iIndepFun_weighted (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    iIndepFun (fun (i : {x // x ∈ S}) (ξ : V → ℝ) => w i * f (ξ i)) (iidLaw V ν) := by
  have h := (iIndepFun_coord (V := V) ν).comp (fun v (z : ℝ) => w v * f z)
    (fun v => (hf.const_mul (w v)))
  exact h.precomp (g := ((↑) : {x // x ∈ S} → V)) Subtype.val_injective

theorem memLp_weighted (v : V) (c : ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2) ν) :
    MemLp (fun ξ : V → ℝ => c * f (ξ v)) 2 (iidLaw V ν) := by
  refine (memLp_two_iff_integrable_sq ?_).2 ?_
  · exact ((hf.comp (measurable_pi_apply v)).const_mul c).aestronglyMeasurable
  · have h : Integrable (fun ξ : V → ℝ => f (ξ v) ^ 2) (iidLaw V ν) :=
      integrable_coord ν v hf2
    have : (fun ξ : V → ℝ => (c * f (ξ v)) ^ 2)
        = fun ξ : V → ℝ => c ^ 2 * f (ξ v) ^ 2 := by funext ξ; ring
    rw [this]
    exact h.const_mul _

theorem integral_weighted_zero (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ}
    (hf : Integrable f ν) (hf0 : ∫ z, f z ∂ν = 0) :
    ∫ ξ, (∑ v ∈ S, w v * f (ξ v)) ∂(iidLaw V ν) = 0 := by
  rw [integral_finsetSum _ fun v _ => (integrable_coord ν v hf).const_mul (w v)]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [integral_const_mul, integral_coord ν v hf.aestronglyMeasurable, hf0, mul_zero]

theorem integral_weighted_sq (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2) ν) (hf0 : ∫ z, f z ∂ν = 0) :
    ∫ ξ, (∑ v ∈ S, w v * f (ξ v)) ^ 2 ∂(iidLaw V ν)
      = (∑ v ∈ S, w v ^ 2) * ∫ z, f z ^ 2 ∂ν := by
  classical
  have hfint : Integrable f ν :=
    ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 hf2).integrable (by norm_num)
  set X : {x // x ∈ S} → (V → ℝ) → ℝ := fun i ξ => w i * f (ξ i) with hX
  have hmeas : ∀ i, Measurable (X i) := fun i =>
    (hf.comp (measurable_pi_apply (i : V))).const_mul (w i)
  have hindep : iIndepFun X (iidLaw V ν) := iIndepFun_weighted S w hf
  have h2 : ∀ i, MemLp (X i) 2 (iidLaw V ν) := fun i => memLp_weighted (i : V) (w i) hf hf2
  have hmean : ∀ i, ∫ ξ, X i ξ ∂(iidLaw V ν) = 0 := by
    intro i
    rw [hX]
    simp only
    rw [integral_const_mul, integral_coord ν (i : V) hfint.aestronglyMeasurable, hf0, mul_zero]
  have hsum := integral_sq_finsetSum_two X hmeas hindep h2 hmean Finset.univ
  have hL : ∀ ξ : V → ℝ, ∑ i : {x // x ∈ S}, X i ξ = ∑ v ∈ S, w v * f (ξ v) := by
    intro ξ
    exact Finset.sum_coe_sort S (fun v => w v * f (ξ v))
  rw [funext fun ξ => congrArg (· ^ 2) (hL ξ)] at hsum
  rw [hsum]
  have hterm : ∀ i : {x // x ∈ S},
      ∫ ξ, X i ξ ^ 2 ∂(iidLaw V ν) = w i ^ 2 * ∫ z, f z ^ 2 ∂ν := by
    intro i
    rw [hX]
    simp only
    have hpt : ∀ ξ : V → ℝ, (w (i : V) * f (ξ (i : V))) ^ 2
        = w (i : V) ^ 2 * f (ξ (i : V)) ^ 2 := fun ξ => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_coord ν (i : V) hf2.aestronglyMeasurable]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul]
  congr 1
  exact Finset.sum_coe_sort S (fun v => w v ^ 2)

theorem memLp_weighted_sum (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2) ν) :
    MemLp (fun ξ : V → ℝ => ∑ v ∈ S, w v * f (ξ v)) 2 (iidLaw V ν) := by
  have hh := memLp_finsetSum' S (fun v (_ : v ∈ S) => memLp_weighted (ν := ν) v (w v) hf hf2)
    (p := 2) (μ := iidLaw V ν)
  have he : (∑ v ∈ S, fun ξ : V → ℝ => w v * f (ξ v))
      = fun ξ : V → ℝ => ∑ v ∈ S, w v * f (ξ v) := by
    funext ξ
    exact Finset.sum_apply ξ S (fun v => fun ξ : V → ℝ => w v * f (ξ v))
  rwa [he] at hh

end Weighted




/-! ### The Green weights at a finite horizon -/

section Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

open scoped Classical in
/-- The vertices carrying a nonzero Green weight at horizon `n`. -/
noncomputable def greenSupport (G : SimpleGraph V) [G.LocallyFinite] (n : ℕ) (o : V) : Finset V :=
  (reach G o n).filter (fun v => greenTime G n o v ≠ 0)

theorem greenTime_pos_of_mem_greenSupport {n : ℕ} {o v : V} (hv : v ∈ greenSupport G n o) :
    0 < greenTime G n o v := by
  classical
  rw [greenSupport, Finset.mem_filter] at hv
  exact lt_of_le_of_ne (greenTime_nonneg n o v) (Ne.symm hv.2)

theorem greenSupport_subset (n : ℕ) (o : V) : greenSupport G n o ⊆ reach G o n := by
  classical
  exact Finset.filter_subset _ _

theorem greenTime_eq_zero_of_notMem_greenSupport {n : ℕ} {o v : V} (hv : v ∈ reach G o n)
    (hnv : v ∉ greenSupport G n o) : greenTime G n o v = 0 := by
  classical
  by_contra h
  exact hnv (Finset.mem_filter.2 ⟨hv, h⟩)

theorem sumSq_eq_sum_greenSupport (n : ℕ) (o : V) :
    sumSq G n o = ∑ v ∈ greenSupport G n o, greenTime G n o v ^ 2 := by
  refine (Finset.sum_subset (greenSupport_subset n o) fun v hv hnv => ?_).symm
  rw [greenTime_eq_zero_of_notMem_greenSupport hv hnv]
  ring

theorem meanPayoff_eq_sum_greenSupport [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (n : ℕ)
    (o : V) :
    meanPayoff G ξ n o = ∑ v ∈ greenSupport G n o, greenTime G n o v * ξ v := by
  rw [meanPayoff_eq_green_sum hG]
  refine (Finset.sum_subset (greenSupport_subset n o) fun v hv hnv => ?_).symm
  rw [greenTime_eq_zero_of_notMem_greenSupport hv hnv, zero_mul]

theorem excess_add_one (ξ : V → ℝ) : excess (fun u => ξ u + 1) = ξ := by
  funext u; rw [excess]; ring

theorem measurable_shift : Measurable fun ξ : V → ℝ => (fun u => ξ u + 1) :=
  measurable_pi_lambda _ fun u => (measurable_pi_apply u).add_const 1

theorem measurable_value [Infinite V] (hG : G.Connected) (n : ℕ) (o : V) :
    Measurable fun ξ : V → ℝ => value G ξ n o := by
  have heq : (fun ξ : V → ℝ => value G ξ n o)
      = (fun σ : V → ℝ => odometer G σ n o) ∘ (fun ξ : V → ℝ => (fun u => ξ u + 1)) := by
    funext ξ
    have h := value_eq hG (fun u => ξ u + 1) n o
    rw [excess_add_one] at h
    exact h
  rw [heq]
  exact (measurable_odometer n o).comp measurable_shift

theorem measurable_meanPayoff' [Infinite V] (hG : G.Connected) (n : ℕ) (o : V) :
    Measurable fun ξ : V → ℝ => meanPayoff G ξ n o := by
  have heq : (fun ξ : V → ℝ => meanPayoff G ξ n o)
      = (fun σ : V → ℝ => meanPayoff G (excess σ) n o)
        ∘ (fun ξ : V → ℝ => (fun u => ξ u + 1)) := by
    funext ξ
    simp only [Function.comp_apply, excess_add_one]
  rw [heq]
  exact (measurable_meanPayoff hG n o).comp measurable_shift

theorem value_nonneg [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (o : V) :
    0 ≤ value G ξ n o :=
  (isLUB_value hG ξ n o).1 (zero_mem_stopValues hG ξ n o)

theorem meanPayoff_le_value [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (o : V) :
    meanPayoff G ξ n o ≤ value G ξ n o := by
  refine (isLUB_value hG ξ n o).1 ⟨fun _ => n, fun _ _ _ _ h => h, fun _ => le_rfl, rfl⟩

theorem max_meanPayoff_le_value [Infinite V] (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (o : V) :
    max (meanPayoff G ξ n o) 0 ≤ value G ξ n o :=
  max_le (meanPayoff_le_value hG ξ n o) (value_nonneg hG ξ n o)

end Graph

/-! ### The mean of the positive part of the payoff -/

section MeanBound

variable {V : Type*} {ν : Measure ℝ} [IsProbabilityMeasure ν]

theorem measurable_weighted_sum (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable fun ξ : V → ℝ => ∑ v ∈ S, w v * f (ξ v) :=
  Finset.measurable_sum _ fun v _ => (hf.comp (measurable_pi_apply v)).const_mul (w v)

theorem integrable_weighted_sum (S : Finset V) (w : V → ℝ) {f : ℝ → ℝ}
    (hf : Integrable f ν) :
    Integrable (fun ξ : V → ℝ => ∑ v ∈ S, w v * f (ξ v)) (iidLaw V ν) :=
  integrable_finsetSum _ fun v _ => (integrable_coord ν v hf).const_mul (w v)

theorem integrable_max_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ}
    (hg : Integrable g P) : Integrable (fun ω => max (g ω) 0) P := by
  refine Integrable.mono' hg.abs (hg.aestronglyMeasurable.sup aestronglyMeasurable_const)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem max_sub_max_le_abs (a b : ℝ) : max a 0 - max b 0 ≤ |a - b| := by
  have h1 : b - a ≤ |a - b| := by
    rw [abs_sub_comm]; exact le_abs_self _
  have h2 : a - b ≤ |a - b| := le_abs_self _
  have h3 : (0 : ℝ) ≤ |a - b| := abs_nonneg _
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [max_eq_right ha, max_eq_right hb]; linarith
  · rw [max_eq_right ha, max_eq_left hb]; linarith
  · rw [max_eq_left ha, max_eq_right hb]; linarith
  · rw [max_eq_left ha, max_eq_left hb]; linarith

end MeanBound

section MeanPayoffBound

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] [Infinite V]
  {ν : Measure ℝ} [IsProbabilityMeasure ν]

omit [Infinite V] in
theorem integral_coord_sq (v : V) (c : ℝ) {f : ℝ → ℝ} (_hf : Measurable f)
    (hf2 : Integrable (fun z => f z ^ 2) ν) :
    ∫ ξ, (c * f (ξ v)) ^ 2 ∂(iidLaw V ν) = c ^ 2 * ∫ z, f z ^ 2 ∂ν := by
  have hpt : ∀ ξ : V → ℝ, (c * f (ξ v)) ^ 2 = c ^ 2 * f (ξ v) ^ 2 := fun ξ => by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_coord ν v hf2.aestronglyMeasurable]

/-- The truncated payoff has a positive part of mean at least `c_* s_M √Σ_n`, as
soon as no single Green weight carries a positive fraction of the `ℓ²` mass. -/
theorem cStar_mul_le_integral_max_hhat (hG : G.Connected)
    (_h0 : extMean ν = 0) (_hsq : evar ν < ⊤) {M : ℝ} (hM : 0 < M) (n : ℕ) (o : V)
    (hdom : 4 * M ^ 2 * greenTime G n o o ^ 2 ≤ tVar ν M * sumSq G n o) :
    cStar * (Real.sqrt (tVar ν M) * Real.sqrt (sumSq G n o))
      ≤ ∫ ξ, max (∑ v ∈ greenSupport G n o, greenTime G n o v * hhat ν M (ξ v)) 0
        ∂(iidLaw V ν) := by
  classical
  have hMnn : (0 : ℝ) ≤ M := hM.le
  have hVar : (0 : ℝ) ≤ tVar ν M := tVar_nonneg hMnn
  have hSig : (0 : ℝ) ≤ sumSq G n o := by
    rw [sumSq_eq_sum_greenSupport]
    exact Finset.sum_nonneg fun v _ => sq_nonneg _
  set S : Finset V := greenSupport G n o with hS
  set w : V → ℝ := fun v => greenTime G n o v with hw
  set Z : {x // x ∈ S} → (V → ℝ) → ℝ := fun i ξ => w i * hhat ν M (ξ i) with hZ
  set b : {x // x ∈ S} → ℝ := fun i => w i * (2 * M) with hb
  set B : ℝ := Real.sqrt (tVar ν M) * Real.sqrt (sumSq G n o) with hB
  have hwpos : ∀ i : {x // x ∈ S}, 0 < w i := fun i =>
    greenTime_pos_of_mem_greenSupport i.2
  have hbpos : ∀ i, 0 < b i := fun i => mul_pos (hwpos i) (by linarith)
  have hmeas : ∀ i, Measurable (Z i) := fun i =>
    ((measurable_hhat M).comp (measurable_pi_apply (i : V))).const_mul (w i)
  have hindep : iIndepFun Z (iidLaw V ν) := iIndepFun_weighted S w (measurable_hhat M)
  have hint : ∀ i, Integrable (Z i) (iidLaw V ν) := fun i =>
    (integrable_coord ν (i : V) (integrable_hhat hMnn)).const_mul (w i)
  have hmean : ∀ i, ∫ ξ, Z i ξ ∂(iidLaw V ν) = 0 := by
    intro i
    rw [hZ]
    simp only
    rw [integral_const_mul, integral_coord ν (i : V) (integrable_hhat hMnn).aestronglyMeasurable,
      integral_hhat hMnn, mul_zero]
  have hbound : ∀ i, ∀ᵐ ξ ∂(iidLaw V ν), |Z i ξ| ≤ b i := by
    intro i
    filter_upwards with ξ
    rw [hZ, hb]
    simp only
    rw [abs_mul, abs_of_nonneg (hwpos i).le]
    exact mul_le_mul_of_nonneg_left (abs_hhat_le hMnn (ξ (i : V))) (hwpos i).le
  have hB0 : 0 ≤ B := by positivity
  have hBsq : B ^ 2 = tVar ν M * sumSq G n o := by
    rw [hB, mul_pow, Real.sq_sqrt hVar, Real.sq_sqrt hSig]
  have hvarZ : ∀ i, variance (Z i) (iidLaw V ν) = w i ^ 2 * tVar ν M := by
    intro i
    rw [variance_of_integral_eq_zero (hmeas i).aemeasurable (hmean i)]
    rw [hZ]
    simp only
    rw [integral_coord_sq (i : V) (w i) (measurable_hhat M) (integrable_hhat_sq hMnn),
      integral_hhat_sq hMnn]
  have hsumvar : ∑ i, variance (Z i) (iidLaw V ν) = tVar ν M * sumSq G n o := by
    rw [Finset.sum_congr rfl fun i _ => hvarZ i]
    rw [sumSq_eq_sum_greenSupport, ← hS]
    rw [Finset.mul_sum]
    rw [← Finset.sum_coe_sort S (fun v => tVar ν M * greenTime G n o v ^ 2)]
    exact Finset.sum_congr rfl fun i _ => by rw [hw]; ring
  have hbB : ∀ i, b i ^ 2 ≤ B ^ 2 := by
    intro i
    have hle : w i ≤ greenTime G n o o := greenTime_le_diag hG n o (i : V)
    have hnn : 0 ≤ w i := (hwpos i).le
    rw [hb, hBsq]
    simp only
    have hsq2 : w i ^ 2 ≤ greenTime G n o o ^ 2 := by nlinarith
    calc (w i * (2 * M)) ^ 2 = 4 * M ^ 2 * w i ^ 2 := by ring
      _ ≤ 4 * M ^ 2 * greenTime G n o o ^ 2 := by nlinarith [sq_nonneg M]
      _ ≤ tVar ν M * sumSq G n o := hdom
  have hmain := positivePart_bound (iidLaw V ν) (instIsProbabilityMeasureIid ν) Z b hbpos
    hindep hint hmean hbound B hB0 (hBsq.trans hsumvar.symm) hbB
  refine hmain.trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)))
  exact congrArg (fun t => max t 0) (Finset.sum_coe_sort S (fun v => w v * hhat ν M (ξ v)))

/-- The mean of the positive part of the payoff at a deterministic time is at
least `(c_* s_M - δ_M)√Σ_n`, which is `eq:mean-lb`. -/
theorem integral_max_meanPayoff_ge (hG : G.Connected)
    (h0 : extMean ν = 0) (hsq : evar ν < ⊤) {M : ℝ} (hM : 0 < M) (n : ℕ) (o : V)
    (hdom : 4 * M ^ 2 * greenTime G n o o ^ 2 ≤ tVar ν M * sumSq G n o) :
    (cStar * Real.sqrt (tVar ν M) - Real.sqrt (tTail ν M)) * Real.sqrt (sumSq G n o)
      ≤ ∫ ξ, max (meanPayoff G ξ n o) 0 ∂(iidLaw V ν) := by
  classical
  have hMnn : (0 : ℝ) ≤ M := hM.le
  have hint : Integrable (fun z : ℝ => z) ν := integrable_id_of_extMean_zero h0
  have hint2 : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evar h0 hsq
  have hz : ∫ z, z ∂ν = 0 := integral_id_zero h0
  have hSig : (0 : ℝ) ≤ sumSq G n o := by
    rw [sumSq_eq_sum_greenSupport]
    exact Finset.sum_nonneg fun v _ => sq_nonneg _
  set S : Finset V := greenSupport G n o with hS
  set w : V → ℝ := fun v => greenTime G n o v with hw
  set R : (V → ℝ) → ℝ := fun ξ => ∑ v ∈ S, w v * ξ v with hR
  set Rh : (V → ℝ) → ℝ := fun ξ => ∑ v ∈ S, w v * hhat ν M (ξ v) with hRh
  set D : (V → ℝ) → ℝ := fun ξ => ∑ v ∈ S, w v * krem ν M (ξ v) with hD
  have hsplit : ∀ ξ : V → ℝ, R ξ = Rh ξ + D ξ := by
    intro ξ
    rw [hR, hRh, hD]
    simp only
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by rw [← mul_add, hhat_add_krem]
  have hRint : Integrable R (iidLaw V ν) :=
    integrable_weighted_sum S w (f := fun z : ℝ => z) hint
  have hRhint : Integrable Rh (iidLaw V ν) :=
    integrable_weighted_sum S w (integrable_hhat hMnn)
  have hDint : Integrable D (iidLaw V ν) :=
    integrable_weighted_sum S w (integrable_krem hMnn hint)
  have hDmem : MemLp D 2 (iidLaw V ν) :=
    memLp_weighted_sum S w (measurable_krem M) (integrable_krem_sq hMnn hint2)
  have hD2 : ∫ ξ, D ξ ^ 2 ∂(iidLaw V ν)
      = (∑ v ∈ S, w v ^ 2) * ∫ z, krem ν M z ^ 2 ∂ν :=
    integral_weighted_sq S w (measurable_krem M) (integrable_krem_sq hMnn hint2)
      (integral_krem hMnn hint hz)
  have hDabs : ∫ ξ, |D ξ| ∂(iidLaw V ν)
      ≤ Real.sqrt (sumSq G n o) * Real.sqrt (tTail ν M) := by
    have h1 := integral_abs_le_sqrt D hDmem
    rw [hD2] at h1
    refine h1.trans ?_
    rw [← Real.sqrt_mul hSig]
    refine Real.sqrt_le_sqrt ?_
    have hkle := integral_krem_sq_le (ν := ν) hMnn hint hint2 hz
    have hSeq : ∑ v ∈ S, w v ^ 2 = sumSq G n o := (sumSq_eq_sum_greenSupport n o).symm
    rw [hSeq]
    exact mul_le_mul_of_nonneg_left hkle hSig
  have hptwise : ∀ ξ : V → ℝ, max (Rh ξ) 0 - |D ξ| ≤ max (R ξ) 0 := by
    intro ξ
    have h1 := max_sub_max_le_abs (Rh ξ) (R ξ)
    have h2 : |Rh ξ - R ξ| = |D ξ| := by
      rw [hsplit ξ]
      rw [show Rh ξ - (Rh ξ + D ξ) = -(D ξ) by ring, abs_neg]
    rw [h2] at h1
    linarith
  have hstep : (∫ ξ, max (Rh ξ) 0 ∂(iidLaw V ν)) - ∫ ξ, |D ξ| ∂(iidLaw V ν)
      ≤ ∫ ξ, max (R ξ) 0 ∂(iidLaw V ν) := by
    rw [← integral_sub (integrable_max_zero hRhint) hDint.abs]
    exact integral_mono ((integrable_max_zero hRhint).sub hDint.abs)
      (integrable_max_zero hRint) hptwise
  have hlow := cStar_mul_le_integral_max_hhat hG h0 hsq hM n o hdom
  have hgoal : ∫ ξ, max (meanPayoff G ξ n o) 0 ∂(iidLaw V ν)
      = ∫ ξ, max (R ξ) 0 ∂(iidLaw V ν) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
      congrArg (fun t => max t 0) (meanPayoff_eq_sum_greenSupport hG ξ n o))
  rw [hgoal]
  have hcomm : Real.sqrt (sumSq G n o) * Real.sqrt (tTail ν M)
      = Real.sqrt (tTail ν M) * Real.sqrt (sumSq G n o) := mul_comm _ _
  rw [hcomm] at hDabs
  nlinarith [hlow, hstep, hDabs]

/-! ### The variance bound -/

theorem abs_value_sub_resample (hG : G.Connected) (ξ : V → ℝ) (v : V) (t : ℝ) (n : ℕ)
    (o : V) :
    |value G ξ n o - value G (resample ξ v t) n o| ≤ greenTime G n o v * |ξ v - t| := by
  have h1 := value_le_resample hG ξ v t n o
  have h2 := value_le_resample hG (resample ξ v t) v (ξ v) n o
  rw [resample_resample, resample_self, abs_sub_comm t (ξ v)] at h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

theorem lintegral_sq_sub (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (s : ℝ) :
    ∫⁻ t, ENNReal.ofReal ((s - t) ^ 2) ∂ν
      = ENNReal.ofReal (s ^ 2 + ∫ z, z ^ 2 ∂ν) := by
  have hint : Integrable (fun z : ℝ => z) ν := integrable_id_of_extMean_zero h0
  have hint2 : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evar h0 hsq
  have hz : ∫ z, z ∂ν = 0 := integral_id_zero h0
  have hexp : ∀ t : ℝ, (s - t) ^ 2 = (s ^ 2 - 2 * s * t) + t ^ 2 := fun t => by ring
  have hi1 : Integrable (fun t : ℝ => s ^ 2 - 2 * s * t) ν :=
    (integrable_const _).sub (hint.const_mul (2 * s))
  have hval : ∫ t, (s - t) ^ 2 ∂ν = s ^ 2 + ∫ z, z ^ 2 ∂ν := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_add hi1 hint2,
      integral_sub (integrable_const (s ^ 2)) (hint.const_mul (2 * s)),
      integral_const_mul, hz, integral_const]
    simp
  have hnn : ∀ᵐ t ∂ν, 0 ≤ (s - t) ^ 2 := Filter.Eventually.of_forall fun t => sq_nonneg _
  have hi : Integrable (fun t : ℝ => (s - t) ^ 2) ν := by
    refine Integrable.congr (hi1.add hint2) (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    exact (hexp t).symm
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hi hnn]

omit [Infinite V] in
theorem lintegral_resample_energy (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (v : V) :
    ∫⁻ ξ, (∫⁻ t, ENNReal.ofReal ((ξ v - t) ^ 2) ∂ν) ∂(iidLaw V ν) = 2 * evar ν := by
  have hint2 : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evar h0 hsq
  have hφ : ∀ ξ : V → ℝ, (∫⁻ t, ENNReal.ofReal ((ξ v - t) ^ 2) ∂ν)
      = ENNReal.ofReal ((ξ v) ^ 2 + ∫ z, z ^ 2 ∂ν) :=
    fun ξ => lintegral_sq_sub h0 hsq (ξ v)
  rw [lintegral_congr hφ]
  have hm2nn : (0 : ℝ) ≤ ∫ z, z ^ 2 ∂ν :=
    integral_nonneg (μ := ν) (f := fun z : ℝ => z ^ 2) fun z => sq_nonneg z
  set m2 : ℝ := ∫ z, z ^ 2 ∂ν with hm2
  have hmeas : Measurable fun s : ℝ => ENNReal.ofReal (s ^ 2 + m2) :=
    ((measurable_id.pow_const 2).add_const _).ennreal_ofReal
  have hmap : ∫⁻ s, ENNReal.ofReal (s ^ 2 + m2) ∂ν
      = ∫⁻ ξ, ENNReal.ofReal ((ξ v) ^ 2 + m2) ∂(iidLaw V ν) := by
    conv_lhs => rw [← map_eval_iidLaw ν v]
    exact lintegral_map hmeas (measurable_pi_apply v)
  rw [← hmap]
  have hnn : ∀ᵐ s ∂ν, 0 ≤ s ^ 2 + m2 := by
    filter_upwards with s
    positivity
  have hi : Integrable (fun s : ℝ => s ^ 2 + m2) ν := hint2.add (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnn,
    integral_add hint2 (integrable_const _), integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  rw [show m2 + m2 = 2 * m2 by ring, ENNReal.ofReal_mul (by norm_num),
    evar_eq_ofReal h0 hsq, ← hm2]
  norm_num

/-! ### The value in `L²` -/

/-- The stopping value is bounded by the Green function against the absolute
value of the scenery.  A stopping time bounded by `n` reads the trajectory only
up to time `n`, so its expected payoff is at most the mean payoff of `|ξ|` at
time `n`, which is the Green sum. -/
theorem value_le_green_abs (hG : G.Connected) (ξ : V → ℝ) (n : ℕ) (o : V) :
    value G ξ n o ≤ ∑ v ∈ reach G o n, greenTime G n o v * |ξ v| := by
  refine (isLUB_value hG ξ n o).2 ?_
  rintro a ⟨τ, -, hle, rfl⟩
  refine (walkExp_payoff_le_green hG ξ n o hle).trans (Finset.sum_le_sum fun v _ => ?_)
  exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
    (greenTime_nonneg n o v)

omit [Infinite V] in
/-- The Green sum against the absolute value of the scenery is in `L²` as soon
as the marginal has a second moment. -/
theorem memLp_green_abs (hint2 : Integrable (fun z : ℝ => z ^ 2) ν) (n : ℕ) (o : V) :
    MemLp (fun ξ : V → ℝ => ∑ v ∈ reach G o n, greenTime G n o v * |ξ v|) 2 (iidLaw V ν) :=
  memLp_weighted_sum (reach G o n) (fun v => greenTime G n o v)
    (f := fun z : ℝ => |z|) (by fun_prop) (by simpa [sq_abs] using hint2)

/-- **The value is square integrable**, with no appeal to Efron--Stein: it lies
between `0` and the Green sum against `|ξ|`, which is in `L²`.  This is what
makes the Efron--Stein inequality applicable to it. -/
theorem integrable_value_sq (hG : G.Connected) (hint2 : Integrable (fun z : ℝ => z ^ 2) ν)
    (n : ℕ) (o : V) :
    Integrable (fun ξ : V → ℝ => value G ξ n o ^ 2) (iidLaw V ν) := by
  have hW := (memLp_green_abs (G := G) hint2 n o).integrable_sq
  refine Integrable.mono' hW ((measurable_value hG n o).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  have h0 := value_nonneg hG ξ n o
  have h1 := value_le_green_abs hG ξ n o
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [h0, h1]

omit [IsProbabilityMeasure ν] in
/-- **The variance bound of `prop:critical`(a).**  Efron--Stein against the
one-site sensitivity: resampling one vertex moves the value by at most the
Green weight of that vertex times the change, and the mean squared change of
one coordinate of a centred field is twice its variance. -/
theorem evariance_value_le (hES : RWRS.External.EfronStein V) (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (n : ℕ) (o : V) :
    evariance (fun ξ : V → ℝ => value G ξ n o) (iidLaw V ν) ≤ evar ν * fluct G n o := by
  classical
  haveI := hν
  refine (hES ν hν (fun ξ : V → ℝ => value G ξ n o) (measurable_value hG n o)
    (integrable_value_sq hG (integrable_sq_of_evar h0 hsq) n o)).trans ?_
  have hterm : ∀ v : V,
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal
            ((value G ξ n o - value G (resample ξ v t) n o) ^ 2) ∂ν ∂(iidLaw V ν))
        ≤ ENNReal.ofReal (greenTime G n o v ^ 2) * (2 * evar ν) := by
    intro v
    have hpt : ∀ (ξ : V → ℝ) (t : ℝ),
        ENNReal.ofReal ((value G ξ n o - value G (resample ξ v t) n o) ^ 2)
          ≤ ENNReal.ofReal (greenTime G n o v ^ 2) * ENNReal.ofReal ((ξ v - t) ^ 2) := by
      intro ξ t
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h := abs_value_sub_resample hG ξ v t n o
      have h1 : (0 : ℝ) ≤ |value G ξ n o - value G (resample ξ v t) n o| := abs_nonneg _
      have h2 : (0 : ℝ) ≤ greenTime G n o v * |ξ v - t| :=
        mul_nonneg (greenTime_nonneg n o v) (abs_nonneg _)
      calc (value G ξ n o - value G (resample ξ v t) n o) ^ 2
          = |value G ξ n o - value G (resample ξ v t) n o| ^ 2 := (sq_abs _).symm
        _ ≤ (greenTime G n o v * |ξ v - t|) ^ 2 := by nlinarith
        _ = greenTime G n o v ^ 2 * (ξ v - t) ^ 2 := by rw [mul_pow, sq_abs]
    calc (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal
            ((value G ξ n o - value G (resample ξ v t) n o) ^ 2) ∂ν ∂(iidLaw V ν))
        ≤ ∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (greenTime G n o v ^ 2)
            * ENNReal.ofReal ((ξ v - t) ^ 2) ∂ν ∂(iidLaw V ν) :=
          lintegral_mono fun ξ => lintegral_mono fun t => hpt ξ t
      _ = ENNReal.ofReal (greenTime G n o v ^ 2)
            * ∫⁻ ξ, ∫⁻ t, ENNReal.ofReal ((ξ v - t) ^ 2) ∂ν ∂(iidLaw V ν) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun ξ =>
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (greenTime G n o v ^ 2) * (2 * evar ν) := by
          rw [lintegral_resample_energy h0 hsq v]
  have htsum : (∑' v : V, ∫⁻ ξ, ∫⁻ t, ENNReal.ofReal
        ((value G ξ n o - value G (resample ξ v t) n o) ^ 2) ∂ν ∂(iidLaw V ν))
      ≤ fluct G n o * (2 * evar ν) := by
    refine (ENNReal.tsum_le_tsum hterm).trans (le_of_eq ?_)
    rw [ENNReal.tsum_mul_right, fluct]
  refine (ENNReal.div_le_div_right htsum 2).trans (le_of_eq ?_)
  rw [show fluct G n o * (2 * evar ν) = evar ν * fluct G n o * 2 by ring]
  exact ENNReal.mul_div_cancel_right two_ne_zero (by norm_num)

/-! ### The domination hypothesis, and the explosion event -/

theorem eventually_dom (hG : G.Connected) (o : V) {M t : ℝ} (hM : 0 < M) (ht : 0 < t)
    (hS : Tendsto (fun n : ℕ => sumSq G n o) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 4 * M ^ 2 * greenTime G n o o ^ 2 ≤ t * sumSq G n o := by
  have hq : (0 : ℝ) < t / (4 * M ^ 2) := by positivity
  filter_upwards [(tendsto_greenTime_sq_div_sumSq hG o hS).eventually (gt_mem_nhds hq),
    hS.eventually_gt_atTop 0] with n hn hpos
  rw [div_lt_iff₀ hpos] at hn
  have h4 : (0 : ℝ) < 4 * M ^ 2 := by positivity
  calc 4 * M ^ 2 * greenTime G n o o ^ 2
      ≤ 4 * M ^ 2 * (t / (4 * M ^ 2) * sumSq G n o) :=
        mul_le_mul_of_nonneg_left hn.le h4.le
    _ = t * sumSq G n o := by field_simp

omit [Infinite V] in
theorem supMeanPayoff_eq_top_of_unbounded (ξ : V → ℝ) (o : V)
    (h : ∀ C : ℝ, ∃ n : ℕ, C ≤ meanPayoff G ξ n o) : supMeanPayoff G ξ o = ⊤ := by
  rw [supMeanPayoff, iSup_eq_top]
  intro b hb
  obtain ⟨n, hn⟩ := h (b.toReal + 1)
  have hb0 : (0 : ℝ) ≤ b.toReal := ENNReal.toReal_nonneg
  refine ⟨n, ?_⟩
  calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb.ne).symm
    _ < ENNReal.ofReal (b.toReal + 1) :=
        ENNReal.ofReal_lt_ofReal_iff'.2 ⟨by linarith, by linarith⟩
    _ ≤ ENNReal.ofReal (meanPayoff G ξ n o) := ENNReal.ofReal_le_ofReal hn

omit [Infinite V] in
theorem ofReal_sqrt_sumSq (n : ℕ) (o : V) :
    fluct G n o ^ (2⁻¹ : ℝ) = ENNReal.ofReal (Real.sqrt (sumSq G n o)) := by
  have hSig : (0 : ℝ) ≤ sumSq G n o := by
    rw [sumSq_eq_sum_greenSupport]
    exact Finset.sum_nonneg fun v _ => sq_nonneg _
  rw [fluct_eq_ofReal_sumSq, Real.sqrt_eq_rpow,
    show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_rpow_of_nonneg hSig (by norm_num)]

theorem measurableSet_supMeanPayoff_top' (hG : G.Connected) (o : V) :
    MeasurableSet {ξ : V → ℝ | supMeanPayoff G ξ o = ⊤} := by
  have heq : {ξ : V → ℝ | supMeanPayoff G ξ o = ⊤}
      = (fun ξ : V → ℝ => (fun u => ξ u + 1)) ⁻¹'
        {σ : V → ℝ | supMeanPayoff G (excess σ) o = ⊤} := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, excess_add_one]
  rw [heq]
  exact measurable_shift (measurableSet_supMeanPayoff_top hG o)

theorem measure_supMeanPayoff_top_zero_or_one (hVF : RWRS.External.VoltageFunction G)
    (hG : G.Connected) (ν : Measure ℝ) [IsProbabilityMeasure ν] (o : V) :
    iidLaw V ν {ξ : V → ℝ | supMeanPayoff G ξ o = ⊤} = 0 ∨
      iidLaw V ν {ξ : V → ℝ | supMeanPayoff G ξ o = ⊤} = 1 := by
  classical
  refine LatticeProb.measure_zero_or_one_of_exchangeable ν
    (measurableSet_supMeanPayoff_top' hG o) fun π hπ => ?_
  ext ξ
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have h := supMeanPayoff_perm_iff hVF hG (fun u => ξ u + 1) π hπ o
  rw [excess_add_one (fun v => ξ (π v)), excess_add_one ξ] at h
  exact h

/-! ### The two Paley--Zygmund steps -/

theorem measureReal_ge_half_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Z : Ω → ℝ) (hZm : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZ : Integrable Z P) (hZ2 : Integrable (fun ω => Z ω ^ 2) P)
    {m K : ℝ} (hm : 0 < m) (hmean : m ≤ ∫ ω, Z ω ∂P) (hK : 0 < K)
    (hsecond : ∫ ω, Z ω ^ 2 ∂P ≤ K * (∫ ω, Z ω ∂P) ^ 2) :
    1 / (4 * K) ≤ (P {ω | m / 2 ≤ Z ω}).toReal := by
  have hE : (0 : ℝ) < ∫ ω, Z ω ∂P := lt_of_lt_of_le hm hmean
  have hA : MeasurableSet {ω | (1 / 2 : ℝ) * ∫ ω, Z ω ∂P ≤ Z ω} :=
    measurableSet_le measurable_const hZm
  have hpz := paley_zygmund Z hZ0 hZ hZ2 (1 / 2) (by norm_num) (by norm_num) hA
  have hsub : {ω | (1 / 2 : ℝ) * ∫ ω, Z ω ∂P ≤ Z ω} ⊆ {ω | m / 2 ≤ Z ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    linarith
  have hmono : (P {ω | (1 / 2 : ℝ) * ∫ ω, Z ω ∂P ≤ Z ω}).toReal
      ≤ (P {ω | m / 2 ≤ Z ω}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hp0 : (0 : ℝ) ≤ (P {ω | (1 / 2 : ℝ) * ∫ ω, Z ω ∂P ≤ Z ω}).toReal :=
    ENNReal.toReal_nonneg
  have hkey : (1 / 4 : ℝ) * (∫ ω, Z ω ∂P) ^ 2
      ≤ K * (∫ ω, Z ω ∂P) ^ 2
        * (P {ω | (1 / 2 : ℝ) * ∫ ω, Z ω ∂P ≤ Z ω}).toReal := by
    nlinarith [hpz, hsecond, hp0]
  have hE2 : (0 : ℝ) < (∫ ω, Z ω ∂P) ^ 2 := by positivity
  have hfinal : 1 / (4 * K)
      ≤ (P {ω | (1 / 2 : ℝ) * ∫ ω, Z ω ∂P ≤ Z ω}).toReal := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hkey, hE2, hK]
  linarith

/-! ### The value in `L²` -/

omit [Infinite V] in
theorem sumSq_nonneg (n : ℕ) (o : V) : 0 ≤ sumSq G n o := by
  rw [sumSq_eq_sum_greenSupport]
  exact Finset.sum_nonneg fun v _ => sq_nonneg _

omit [IsProbabilityMeasure ν] in
theorem memLp_value (hES : RWRS.External.EfronStein V) (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (n : ℕ) (o : V) :
    MemLp (fun ξ : V → ℝ => value G ξ n o) 2 (iidLaw V ν) := by
  haveI := hν
  refine (evariance_lt_top_iff_memLp (measurable_value hG n o).aestronglyMeasurable).1 ?_
  refine lt_of_le_of_lt (evariance_value_le hES hG hν h0 hsq n o) ?_
  exact ENNReal.mul_lt_top hsq (lt_top_iff_ne_top.2 (fluct_ne_top n o))

omit [IsProbabilityMeasure ν] in
theorem variance_value_le (hES : RWRS.External.EfronStein V) (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hsq : evar ν < ⊤) (n : ℕ) (o : V) :
    variance (fun ξ : V → ℝ => value G ξ n o) (iidLaw V ν)
      ≤ (∫ z, z ^ 2 ∂ν) * sumSq G n o := by
  haveI := hν
  have hm2 : (0 : ℝ) ≤ ∫ z, z ^ 2 ∂ν :=
    integral_nonneg (μ := ν) (f := fun z : ℝ => z ^ 2) fun z => sq_nonneg z
  have hSig : (0 : ℝ) ≤ sumSq G n o := sumSq_nonneg n o
  have h := evariance_value_le hES hG hν h0 hsq n o
  rw [evar_eq_ofReal h0 hsq, fluct_eq_ofReal_sumSq, ← ENNReal.ofReal_mul hm2] at h
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal (by positivity)] at h2
  exact h2

/-! ### The explosion bound -/

omit [Infinite V] in
theorem tendsto_sumSq_of_tendsto_fluct {o : V}
    (hSigma : Tendsto (fun n : ℕ => fluct G n o) atTop (𝓝 ⊤)) :
    Tendsto (fun n : ℕ => sumSq G n o) atTop atTop := by
  refine tendsto_atTop.2 fun C => ?_
  have hC : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  filter_upwards [ENNReal.tendsto_nhds_top_iff_nnreal.1 hSigma
    (Real.toNNReal (max C 0))] with n hn
  have hn' : ENNReal.ofReal (max C 0) < ENNReal.ofReal (sumSq G n o) := by
    rw [← fluct_eq_ofReal_sumSq]; exact hn
  exact ((le_max_left C 0).trans ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC).1 hn').le)

theorem integrable_meanPayoff (hG : G.Connected) (hint : Integrable (fun z : ℝ => z) ν)
    (n : ℕ) (o : V) :
    Integrable (fun ξ : V → ℝ => meanPayoff G ξ n o) (iidLaw V ν) := by
  refine (integrable_weighted_sum (greenSupport G n o) (fun v => greenTime G n o v)
    (f := fun z : ℝ => z) hint).congr (Filter.Eventually.of_forall fun ξ => ?_)
  exact (meanPayoff_eq_sum_greenSupport hG ξ n o).symm

omit [IsProbabilityMeasure ν] in
/-- **The explosion bound of `prop:critical`(b).**  The constants depend only on
the law of the scenery. -/
theorem exists_critical_constants (hES : RWRS.External.EfronStein V) (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hvar : 0 < evar ν)
    (hsq : evar ν < ⊤) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ o : V,
      Tendsto (fun n : ℕ => fluct G n o) atTop (𝓝 ⊤) →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ENNReal.ofReal c₂ ≤ iidLaw V ν
            {ξ : V → ℝ | ENNReal.ofReal c₁ * fluct G n o ^ (2⁻¹ : ℝ)
              ≤ ENNReal.ofReal (value G ξ n o)} := by
  classical
  haveI := hν
  have hint : Integrable (fun z : ℝ => z) ν := integrable_id_of_extMean_zero h0
  obtain ⟨M, hM, hMvar, hMlt⟩ := exists_good_trunc h0 hsq hvar
  set cM : ℝ := cStar * Real.sqrt (tVar ν M) - Real.sqrt (tTail ν M) with hcM
  have hcMpos : 0 < cM := by rw [hcM]; exact sub_pos.2 hMlt
  set m2 : ℝ := ∫ z, z ^ 2 ∂ν with hm2
  have hm2pos : 0 < m2 := integral_sq_pos h0 hsq hvar
  refine ⟨cM / 2, cM ^ 2 / (4 * (m2 + cM ^ 2)), by positivity, by positivity, ?_⟩
  intro o hSigma
  have hS := tendsto_sumSq_of_tendsto_fluct hSigma
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((eventually_dom hG o hM hMvar hS).and (hS.eventually_gt_atTop 0))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hdom, hSigpos⟩ := hN n hn
  have hsqrtpos : 0 < Real.sqrt (sumSq G n o) := Real.sqrt_pos.2 hSigpos
  have hmemV := memLp_value hES hG hν h0 hsq n o
  have hZint : Integrable (fun ξ : V → ℝ => value G ξ n o) (iidLaw V ν) :=
    hmemV.integrable (by norm_num)
  have hZ2 : Integrable (fun ξ : V → ℝ => value G ξ n o ^ 2) (iidLaw V ν) :=
    hmemV.integrable_sq
  have hmpint : Integrable (fun ξ : V → ℝ => max (meanPayoff G ξ n o) 0) (iidLaw V ν) :=
    integrable_max_zero (integrable_meanPayoff hG hint n o)
  have hmean : cM * Real.sqrt (sumSq G n o)
      ≤ ∫ ξ, value G ξ n o ∂(iidLaw V ν) := by
    refine le_trans ?_ (integral_mono hmpint hZint fun ξ => max_meanPayoff_le_value hG ξ n o)
    exact integral_max_meanPayoff_ge hG h0 hsq hM n o hdom
  have hmpos : 0 < cM * Real.sqrt (sumSq G n o) := by positivity
  have hEpos : 0 < ∫ ξ, value G ξ n o ∂(iidLaw V ν) := lt_of_lt_of_le hmpos hmean
  have hvarV := variance_value_le hES hG hν h0 hsq n o
  have hvarsub : variance (fun ξ : V → ℝ => value G ξ n o) (iidLaw V ν)
      = (∫ ξ, value G ξ n o ^ 2 ∂(iidLaw V ν))
        - (∫ ξ, value G ξ n o ∂(iidLaw V ν)) ^ 2 := by
    rw [variance_eq_sub hmemV]
    congr 1
  have hSle : cM ^ 2 * sumSq G n o ≤ (∫ ξ, value G ξ n o ∂(iidLaw V ν)) ^ 2 := by
    have hsq : cM ^ 2 * sumSq G n o = (cM * Real.sqrt (sumSq G n o)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (sumSq_nonneg (G := G) n o)]
    rw [hsq]
    exact pow_le_pow_left₀ hmpos.le hmean 2
  have hsecond : ∫ ξ, value G ξ n o ^ 2 ∂(iidLaw V ν)
      ≤ ((m2 + cM ^ 2) / cM ^ 2) * (∫ ξ, value G ξ n o ∂(iidLaw V ν)) ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h1 : m2 * (cM ^ 2 * sumSq G n o)
        ≤ m2 * (∫ ξ, value G ξ n o ∂(iidLaw V ν)) ^ 2 :=
      mul_le_mul_of_nonneg_left hSle hm2pos.le
    have h2 : variance (fun ξ : V → ℝ => value G ξ n o) (iidLaw V ν) * cM ^ 2
        ≤ (m2 * sumSq G n o) * cM ^ 2 :=
      mul_le_mul_of_nonneg_right hvarV (sq_nonneg cM)
    nlinarith [h1, h2, hvarsub]
  have hpz := measureReal_ge_half_mean (fun ξ : V → ℝ => value G ξ n o)
    (measurable_value hG n o) (fun ξ => value_nonneg hG ξ n o) hZint hZ2
    (m := cM * Real.sqrt (sumSq G n o)) (K := (m2 + cM ^ 2) / cM ^ 2) hmpos hmean
    (by positivity) hsecond
  have hKval : 1 / (4 * ((m2 + cM ^ 2) / cM ^ 2)) = cM ^ 2 / (4 * (m2 + cM ^ 2)) := by
    field_simp
  rw [hKval] at hpz
  -- transfer to the extended reals
  have hsubset : {ξ : V → ℝ | cM * Real.sqrt (sumSq G n o) / 2 ≤ value G ξ n o}
      ⊆ {ξ : V → ℝ | ENNReal.ofReal (cM / 2) * fluct G n o ^ (2⁻¹ : ℝ)
          ≤ ENNReal.ofReal (value G ξ n o)} := by
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    rw [ofReal_sqrt_sumSq, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc cM / 2 * Real.sqrt (sumSq G n o) = cM * Real.sqrt (sumSq G n o) / 2 := by ring
      _ ≤ value G ξ n o := hξ
  refine le_trans ?_ (measure_mono hsubset)
  have hfin : iidLaw V ν {ξ : V → ℝ | cM * Real.sqrt (sumSq G n o) / 2 ≤ value G ξ n o} ≠ ⊤ :=
    measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hpz

omit [IsProbabilityMeasure ν] in
/-- **Almost sure explosion in the critical regime.**  A positive probability of
explosion is upgraded by the zero-one law. -/
theorem ae_supMeanPayoff_top_critical
    (hVF : RWRS.External.VoltageFunction G) (hG : G.Connected)
    (hν : IsProbabilityMeasure ν) (h0 : extMean ν = 0) (hvar : 0 < evar ν)
    (hsq : evar ν < ⊤) (o : V)
    (hSigma : Tendsto (fun n : ℕ => fluct G n o) atTop (𝓝 ⊤)) :
    ∀ᵐ ξ ∂(iidLaw V ν), supMeanPayoff G ξ o = ⊤ := by
  classical
  haveI := hν
  have hint : Integrable (fun z : ℝ => z) ν := integrable_id_of_extMean_zero h0
  have hint2 : Integrable (fun z : ℝ => z ^ 2) ν := integrable_sq_of_evar h0 hsq
  have hz : ∫ z, z ∂ν = 0 := integral_id_zero h0
  obtain ⟨M, hM, hMvar, hMlt⟩ := exists_good_trunc h0 hsq hvar
  set cM : ℝ := cStar * Real.sqrt (tVar ν M) - Real.sqrt (tTail ν M) with hcM
  have hcMpos : 0 < cM := by rw [hcM]; exact sub_pos.2 hMlt
  set m2 : ℝ := ∫ z, z ^ 2 ∂ν with hm2
  have hm2pos : 0 < m2 := integral_sq_pos h0 hsq hvar
  set c₃ : ℝ := cM ^ 2 / (4 * m2) with hc₃
  have hc₃pos : 0 < c₃ := by rw [hc₃]; positivity
  have hS := tendsto_sumSq_of_tendsto_fluct hSigma
  set A : ℕ → Set (V → ℝ) :=
    fun n => {ξ : V → ℝ | cM * Real.sqrt (sumSq G n o) / 2 ≤ meanPayoff G ξ n o} with hA
  have hAmeas : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le measurable_const (measurable_meanPayoff' hG n o)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((eventually_dom hG o hM hMvar hS).and (hS.eventually_gt_atTop 0))
  have hAbound : ∀ n : ℕ, N₀ ≤ n → ENNReal.ofReal c₃ ≤ iidLaw V ν (A n) := by
    intro n hn
    obtain ⟨hdom, hSigpos⟩ := hN₀ n hn
    have hsqrtpos : 0 < Real.sqrt (sumSq G n o) := Real.sqrt_pos.2 hSigpos
    have hmpos : 0 < cM * Real.sqrt (sumSq G n o) := by positivity
    have hmaxsq : ∀ r : ℝ, max r 0 ^ 2 ≤ r ^ 2 := by
      intro r
      rcases le_total r 0 with h | h
      · rw [max_eq_right h]; simpa using sq_nonneg r
      · rw [max_eq_left h]
    have hRint : Integrable (fun ξ : V → ℝ => meanPayoff G ξ n o) (iidLaw V ν) :=
      integrable_meanPayoff hG hint n o
    have hZint : Integrable (fun ξ : V → ℝ => max (meanPayoff G ξ n o) 0) (iidLaw V ν) :=
      integrable_max_zero hRint
    have hRmem : MemLp (fun ξ : V → ℝ => meanPayoff G ξ n o) 2 (iidLaw V ν) := by
      refine (memLp_congr_ae (Filter.Eventually.of_forall fun ξ =>
        (meanPayoff_eq_sum_greenSupport hG ξ n o))).2 ?_
      exact memLp_weighted_sum (greenSupport G n o) (fun v => greenTime G n o v)
        (f := fun z : ℝ => z) measurable_id hint2
    have hR2 : Integrable (fun ξ : V → ℝ => meanPayoff G ξ n o ^ 2) (iidLaw V ν) :=
      hRmem.integrable_sq
    have hZ2 : Integrable (fun ξ : V → ℝ => max (meanPayoff G ξ n o) 0 ^ 2) (iidLaw V ν) := by
      refine Integrable.mono' hR2 ((hRint.aestronglyMeasurable.sup
        aestronglyMeasurable_const).pow 2) (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hmaxsq _
    have hmeanZ : cM * Real.sqrt (sumSq G n o)
        ≤ ∫ ξ, max (meanPayoff G ξ n o) 0 ∂(iidLaw V ν) :=
      integral_max_meanPayoff_ge hG h0 hsq hM n o hdom
    have hR2val : ∫ ξ, meanPayoff G ξ n o ^ 2 ∂(iidLaw V ν) = sumSq G n o * m2 := by
      have h := integral_weighted_sq (ν := ν) (greenSupport G n o)
        (fun v => greenTime G n o v) (f := fun z : ℝ => z) measurable_id hint2 hz
      rw [← sumSq_eq_sum_greenSupport] at h
      rw [← h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ξ =>
        congrArg (· ^ 2) (meanPayoff_eq_sum_greenSupport hG ξ n o))
    have hZ2le : ∫ ξ, max (meanPayoff G ξ n o) 0 ^ 2 ∂(iidLaw V ν) ≤ sumSq G n o * m2 := by
      rw [← hR2val]
      exact integral_mono hZ2 hR2 fun ξ => hmaxsq _
    have hSle : cM ^ 2 * sumSq G n o
        ≤ (∫ ξ, max (meanPayoff G ξ n o) 0 ∂(iidLaw V ν)) ^ 2 := by
      have hsq2 : cM ^ 2 * sumSq G n o = (cM * Real.sqrt (sumSq G n o)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (sumSq_nonneg (G := G) n o)]
      rw [hsq2]
      exact pow_le_pow_left₀ hmpos.le hmeanZ 2
    have hsecond : ∫ ξ, max (meanPayoff G ξ n o) 0 ^ 2 ∂(iidLaw V ν)
        ≤ (m2 / cM ^ 2) * (∫ ξ, max (meanPayoff G ξ n o) 0 ∂(iidLaw V ν)) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [hZ2le, mul_le_mul_of_nonneg_left hSle hm2pos.le]
    have hpz := measureReal_ge_half_mean (fun ξ : V → ℝ => max (meanPayoff G ξ n o) 0)
      ((measurable_meanPayoff' hG n o).max measurable_const)
      (fun ξ => le_max_right _ _) hZint hZ2
      (m := cM * Real.sqrt (sumSq G n o)) (K := m2 / cM ^ 2) hmpos hmeanZ
      (by positivity) hsecond
    have hKval : 1 / (4 * (m2 / cM ^ 2)) = c₃ := by rw [hc₃]; field_simp
    rw [hKval] at hpz
    have hsub : {ξ : V → ℝ | cM * Real.sqrt (sumSq G n o) / 2
        ≤ max (meanPayoff G ξ n o) 0} ⊆ A n := by
      intro ξ hξ
      simp only [Set.mem_setOf_eq, hA] at hξ ⊢
      rcases le_total (meanPayoff G ξ n o) 0 with h | h
      · rw [max_eq_right h] at hξ; linarith
      · rwa [max_eq_left h] at hξ
    refine le_trans ?_ (measure_mono hsub)
    rw [← ENNReal.ofReal_toReal (measure_ne_top (iidLaw V ν)
      {ξ : V → ℝ | cM * Real.sqrt (sumSq G n o) / 2 ≤ max (meanPayoff G ξ n o) 0})]
    exact ENNReal.ofReal_le_ofReal hpz
  -- the limit superior of the events
  set B : ℕ → Set (V → ℝ) := fun N => ⋃ n, ⋃ (_ : N ≤ n), A n with hB
  have hBanti : Antitone B := by
    intro N₁ N₂ hle
    refine Set.iUnion_mono fun n => ?_
    exact Set.iUnion_mono' fun h => ⟨le_trans hle h, le_rfl⟩
  have hBmeas : ∀ N, MeasurableSet (B N) := fun N =>
    MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => hAmeas n
  have hBbound : ∀ N, ENNReal.ofReal c₃ ≤ iidLaw V ν (B N) := by
    intro N
    refine le_trans (hAbound (max N N₀) (le_max_right _ _)) (measure_mono ?_)
    exact Set.subset_iUnion_of_subset (max N N₀)
      (Set.subset_iUnion_of_subset (le_max_left _ _) (subset_refl _))
  have hlim : Tendsto (fun N => iidLaw V ν (B N)) atTop (𝓝 (iidLaw V ν (⋂ N, B N))) :=
    tendsto_measure_iInter_atTop (fun N => (hBmeas N).nullMeasurableSet) hBanti
      ⟨0, measure_ne_top _ _⟩
  have hIpos : ENNReal.ofReal c₃ ≤ iidLaw V ν (⋂ N, B N) :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hBbound)
  -- the intersection forces explosion
  have hgrow : Tendsto (fun n : ℕ => cM * Real.sqrt (sumSq G n o) / 2) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => Real.sqrt (sumSq G n o)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hS
    exact (h1.const_mul_atTop hcMpos).atTop_div_const two_pos
  have hincl : (⋂ N, B N) ⊆ {ξ : V → ℝ | supMeanPayoff G ξ o = ⊤} := by
    intro ξ hξ
    refine supMeanPayoff_eq_top_of_unbounded ξ o fun C => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hgrow.eventually_ge_atTop C)
    have hmem := Set.mem_iInter.1 hξ N
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hmem
    obtain ⟨hNn, hAn⟩ := Set.mem_iUnion.1 hn
    exact ⟨n, le_trans (hN n hNn) hAn⟩
  have hpos : iidLaw V ν {ξ : V → ℝ | supMeanPayoff G ξ o = ⊤} ≠ 0 := by
    intro hzero
    have := le_trans hIpos (measure_mono hincl)
    rw [hzero, le_zero_iff, ENNReal.ofReal_eq_zero] at this
    linarith
  rcases measure_supMeanPayoff_top_zero_or_one hVF hG ν o with h | h
  · exact absurd h hpos
  · rw [ae_iff]
    have hcompl : {ξ : V → ℝ | ¬ supMeanPayoff G ξ o = ⊤}
        = {ξ : V → ℝ | supMeanPayoff G ξ o = ⊤}ᶜ := rfl
    rw [hcompl, measure_compl (measurableSet_supMeanPayoff_top' hG o)
      (measure_ne_top _ _), h]
    simp

end MeanPayoffBound

end RWRS.Support
