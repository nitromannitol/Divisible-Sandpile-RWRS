/-
The reroot average and its iterates.

The proof of `lem:ergodic-marked-stationary` runs the simple random walk from
the root for `n` steps.  Iterating the one-step average `rerootAvg` of
`def:stationary-graph` is that walk: the `n`-th iterate at a network is the
average of the test function over the network rerooted at the walk's position at
time `n`, and the stationarity identity says that the iterate has the same
integral as the function itself.  On the indicator of a single vertex the
iterate is the heat kernel, which is how the walk is made to leave a ball.
-/
import RWRS.Support.ErgBall
import RWRS.Support.HeatBasic
import RWRS.External.HeatKernelVanishing

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal

variable {m : ℕ}

/-- Rerooting a good net at any vertex `y` keeps it good, since `NetGood` does not depend on
the choice of root. -/
theorem netGood_netReroot {N : RWRS.Net m} (hN : RWRS.NetGood N) (y : ℕ) :
    RWRS.NetGood (RWRS.netReroot N y) := hN

/-- On a good net the root has positive degree in the underlying graph. -/
theorem degree_netRoot_pos {N : RWRS.Net m} (hN : RWRS.NetGood N) :
    0 < (RWRS.netGraph N).degree (RWRS.netRoot N) := degree_pos hN _

/-- `rerootAvg` is monotone: a pointwise bound `h ≤ h'` gives `rerootAvg h ≤ rerootAvg h'`. -/
theorem rerootAvg_mono {h h' : RWRS.Net m → ℝ≥0∞} (hle : ∀ N, h N ≤ h' N) (N : RWRS.Net m) :
    rerootAvg h N ≤ rerootAvg h' N := by
  refine ENNReal.div_le_div_right (Finset.sum_le_sum fun y _ => hle _) _

/-- `rerootAvg` commutes with pointwise addition of the two test functions. -/
theorem rerootAvg_add (h h' : RWRS.Net m → ℝ≥0∞) (N : RWRS.Net m) :
    rerootAvg (fun M => h M + h' M) N = rerootAvg h N + rerootAvg h' N := by
  simp only [rerootAvg, Finset.sum_add_distrib, ENNReal.add_div]

/-- On a good net, `rerootAvg` of a constant function returns that same constant, since the
neighbor-average of a constant over the (positive, finite) degree is unchanged. -/
theorem rerootAvg_const (c : ℝ≥0∞) {N : RWRS.Net m} (hN : RWRS.NetGood N) :
    rerootAvg (fun _ => c) N = c := by
  have hd : ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) ≠ 0 := by
    simpa using (degree_netRoot_pos hN).ne'
  have hdt : ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp only [rerootAvg, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul]
  rw [mul_comm, mul_div_assoc, ENNReal.div_self hd hdt, mul_one]

/-- If `h` is bounded by `1` everywhere, its `rerootAvg` at a good net is also at most `1`,
by combining `rerootAvg_mono` with `rerootAvg_const`. -/
theorem rerootAvg_le_one {h : RWRS.Net m → ℝ≥0∞} (hle : ∀ N, h N ≤ 1) {N : RWRS.Net m}
    (hN : RWRS.NetGood N) : rerootAvg h N ≤ 1 := by
  refine le_trans (rerootAvg_mono (h' := fun _ => (1 : ℝ≥0∞)) hle N) ?_
  exact le_of_eq (rerootAvg_const 1 hN)

/-- If `h` agrees with its own value after rerooting at every neighbor of the root, then
`rerootAvg h` at a good net equals `h` at that net, since every term of the average equals `h N`. -/
theorem rerootAvg_eq_of_reroot {h : RWRS.Net m → ℝ≥0∞}
    (hre : ∀ (N : RWRS.Net m) (y : ℕ), (RWRS.netGraph N).Adj (RWRS.netRoot N) y →
      h N = h (RWRS.netReroot N y)) {N : RWRS.Net m} (hN : RWRS.NetGood N) :
    rerootAvg h N = h N := by
  have hc : ∀ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
      h (RWRS.netReroot N y) = h N :=
    fun y hy => (hre N y ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)).symm
  have : rerootAvg h N = rerootAvg (fun _ => h N) N := by
    simp only [rerootAvg]
    rw [Finset.sum_congr rfl hc]
  rw [this, rerootAvg_const _ hN]

/-- `rerootAvg` preserves `NetInvariant`: the one-step average of a reroot-invariant function is
itself reroot-invariant, since a network isomorphism carries the neighbor sum over the root to
the neighbor sum over the corresponding root. -/
theorem netInvariant_rerootAvg {h : RWRS.Net m → ℝ≥0∞} (hinv : RWRS.NetInvariant h) :
    RWRS.NetInvariant (rerootAvg h) := by
  rintro N N' ⟨φ, hadj, hroot, hmark⟩
  have hnb : (RWRS.netGraph N').neighborFinset (RWRS.netRoot N')
      = ((RWRS.netGraph N).neighborFinset (RWRS.netRoot N)).image φ := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image]
    constructor
    · intro hz
      refine ⟨φ.symm z, ?_, by simp⟩
      have h2 := hadj (RWRS.netRoot N) (φ.symm z)
      rw [hroot, Equiv.apply_symm_apply] at h2
      exact h2.2 hz
    · rintro ⟨y, hy, rfl⟩
      have h2 := hadj (RWRS.netRoot N) y
      rw [hroot] at h2
      exact h2.1 hy
  have hval : ∀ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
      h (RWRS.netReroot N' (φ y)) = h (RWRS.netReroot N y) := by
    intro y _
    refine (hinv _ _ ⟨φ, ?_, ?_, ?_⟩).symm
    · intro i j; exact hadj i j
    · rfl
    · intro i; exact hmark i
  simp only [rerootAvg]
  rw [hnb, Finset.sum_image (fun x _ y _ hxy => φ.injective hxy),
    Finset.sum_congr rfl hval, SimpleGraph.degree, SimpleGraph.degree, hnb,
    Finset.card_image_of_injective _ φ.injective]

/-- The `n`-th iterate of `rerootAvg` applied to the indicator of `netRoot = v` computes the
`n`-step simple random walk heat kernel `RWRS.heat` from the root to `v`. -/
theorem rerootIter_rootIndicator (v : ℕ) :
    ∀ (n : ℕ) (N : RWRS.Net m), RWRS.NetGood N →
      (rerootAvg^[n] fun M : RWRS.Net m => if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0) N
        = ENNReal.ofReal (RWRS.heat (RWRS.netGraph N) n (RWRS.netRoot N) v) := by
  intro n
  induction n with
  | zero =>
      intro N _
      simp only [Function.iterate_zero, id_eq, RWRS.heat]
      by_cases hv : RWRS.netRoot N = v
      · simp [hv]
      · simp [hv]
  | succ n ih =>
      intro N hN
      have hstep : (rerootAvg^[n + 1] fun M : RWRS.Net m =>
            if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0)
          = rerootAvg (rerootAvg^[n] fun M : RWRS.Net m =>
            if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0) := by
        rw [Function.iterate_succ']
        rfl
      rw [hstep, rerootAvg]
      have hsum : (∑ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
            (rerootAvg^[n] fun M : RWRS.Net m => if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0)
              (RWRS.netReroot N y))
          = ∑ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
              ENNReal.ofReal (RWRS.heat (RWRS.netGraph N) n y v) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        exact ih (RWRS.netReroot N y) hN
      rw [hsum]
      rw [show RWRS.heat (RWRS.netGraph N) (n + 1) (RWRS.netRoot N) v
          = (∑ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
              RWRS.heat (RWRS.netGraph N) n y v)
            / ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ) from rfl]
      rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast degree_netRoot_pos hN)]
      congr 1
      · rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => heat_nonneg n y v)]
      · simp

/-- For a stationary net law `P`, the integral of any iterate of `rerootAvg` applied to a
measurable, reroot-invariant `h` equals the integral of `h` itself, by repeated use of
`hstat` together with `netInvariant_rerootAvg`. -/
theorem lintegral_rerootIter {P : Measure (RWRS.Net m)} (hstat : RWRS.IsStationaryNet P) :
    ∀ (n : ℕ) (h : RWRS.Net m → ℝ≥0∞), Measurable h → RWRS.NetInvariant h →
      ∫⁻ N, (rerootAvg^[n] h) N ∂P = ∫⁻ N, h N ∂P := by
  intro n
  induction n with
  | zero => intro h _ _; simp
  | succ n ih =>
      intro h hm hinv
      have hstep : rerootAvg^[n + 1] h = rerootAvg^[n] (rerootAvg h) := by
        rw [Function.iterate_succ]; rfl
      rw [hstep, ih (rerootAvg h) (measurable_rerootAvg hm) (netInvariant_rerootAvg hinv)]
      exact (hstat h hm hinv).symm

/-- Monotonicity of `rerootAvg` iterates: a pointwise bound `h ≤ h'` propagates to
`rerootAvg^[n] h ≤ rerootAvg^[n] h'` for every `n`. -/
theorem rerootIter_mono : ∀ (n : ℕ) {h h' : RWRS.Net m → ℝ≥0∞}, (∀ N, h N ≤ h' N) →
    ∀ N : RWRS.Net m, (rerootAvg^[n] h) N ≤ (rerootAvg^[n] h') N := by
  intro n
  induction n with
  | zero => intro h h' hle N; simpa using hle N
  | succ n ih =>
      intro h h' hle N
      have hstep : ∀ g : RWRS.Net m → ℝ≥0∞, rerootAvg^[n + 1] g = rerootAvg^[n] (rerootAvg g) := by
        intro g; rw [Function.iterate_succ]; rfl
      rw [hstep h, hstep h']
      exact ih (fun M => rerootAvg_mono hle M) N

/-- `rerootAvg` of the identically-zero function is zero. -/
theorem rerootAvg_zero (N : RWRS.Net m) : rerootAvg (fun _ : RWRS.Net m => (0 : ℝ≥0∞)) N = 0 := by
  simp [rerootAvg]

/-- `rerootAvg` commutes with a finite sum over an index set `s`: averaging term by term agrees
with averaging the sum, proved by induction on `s` using `rerootAvg_add`. -/
theorem rerootAvg_finsetSum (s : Finset ℕ) (f : ℕ → RWRS.Net m → ℝ≥0∞) (N : RWRS.Net m) :
    rerootAvg (fun M => ∑ v ∈ s, f v M) N = ∑ v ∈ s, rerootAvg (f v) N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rerootAvg]
  | insert a t ha iht =>
      simp only [Finset.sum_insert ha]
      rw [rerootAvg_add (f a) (fun M => ∑ v ∈ t, f v M) N, iht]

/-- Iterating `rerootAvg`, like the one-step average `rerootAvg_finsetSum`, commutes with a
finite sum over an index set `s`. -/
theorem rerootIter_finsetSum (s : Finset ℕ) :
    ∀ (n : ℕ) (f : ℕ → RWRS.Net m → ℝ≥0∞) (N : RWRS.Net m),
      (rerootAvg^[n] fun M => ∑ v ∈ s, f v M) N = ∑ v ∈ s, (rerootAvg^[n] (f v)) N := by
  intro n
  induction n with
  | zero => intro f N; simp
  | succ n ih =>
      intro f N
      have hstep : ∀ g : RWRS.Net m → ℝ≥0∞, rerootAvg^[n + 1] g = rerootAvg^[n] (rerootAvg g) := by
        intro g; rw [Function.iterate_succ]; rfl
      rw [hstep]
      have hcomm : (rerootAvg fun M => ∑ v ∈ s, f v M) = fun M => ∑ v ∈ s, rerootAvg (f v) M :=
        funext fun M => rerootAvg_finsetSum s f M
      rw [hcomm]
      simpa using ih (fun v => rerootAvg (f v)) N

/-- If `h ≤ 1` everywhere, every iterate `rerootAvg^[n] h` stays bounded by `1` on a good net. -/
theorem rerootIter_le_one {h : RWRS.Net m → ℝ≥0∞} (hle : ∀ N, h N ≤ 1) :
    ∀ (n : ℕ) (N : RWRS.Net m), RWRS.NetGood N → (rerootAvg^[n] h) N ≤ 1 := by
  intro n
  induction n with
  | zero => intro N _; simpa using hle N
  | succ n ih =>
      intro N hN
      have hstep : rerootAvg^[n + 1] h = rerootAvg (rerootAvg^[n] h) := by
        rw [Function.iterate_succ']; rfl
      rw [hstep, rerootAvg]
      have hbound : ∀ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
          (rerootAvg^[n] h) (RWRS.netReroot N y) ≤ 1 := fun y _ => ih (RWRS.netReroot N y) hN
      have hd : ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) ≠ 0 := by
        simpa using (degree_netRoot_pos hN).ne'
      have hdt : ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      calc (∑ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
              (rerootAvg^[n] h) (RWRS.netReroot N y))
              / ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞)
          ≤ (∑ _y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N), (1 : ℝ≥0∞))
              / ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) :=
            ENNReal.div_le_div_right (Finset.sum_le_sum hbound) _
        _ = 1 := by
            rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul,
              mul_one, ENNReal.div_self hd hdt]

open scoped Classical in
/-- **The walk leaves every ball.**  On an infinite connected graph the walk's
`n`-step average of the indicator of a fixed ball tends to zero. -/
theorem tendsto_rerootIter_closedBall {N : RWRS.Net m} (hN : RWRS.NetGood N)
    (hHKV : RWRS.External.HeatKernelVanishing (RWRS.netGraph N)) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ => (rerootAvg^[n] fun M : RWRS.Net m =>
        if RWRS.netRoot M ∈ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) k then
          (1 : ℝ≥0∞) else 0) N)
      Filter.atTop (nhds 0) := by
  classical
  set F : Finset ℕ := (finite_closedBall (G := RWRS.netGraph N) (RWRS.netRoot N) k).toFinset
    with hF
  have hle : ∀ n : ℕ, (rerootAvg^[n] fun M : RWRS.Net m =>
        if RWRS.netRoot M ∈ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) k then
          (1 : ℝ≥0∞) else 0) N
      ≤ ∑ v ∈ F, ENNReal.ofReal (RWRS.heat (RWRS.netGraph N) n (RWRS.netRoot N) v) := by
    intro n
    have hpt : ∀ M : RWRS.Net m,
        (if RWRS.netRoot M ∈ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) k then
          (1 : ℝ≥0∞) else 0)
          ≤ ∑ v ∈ F, (if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0) := by
      intro M
      by_cases hM : RWRS.netRoot M ∈ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) k
      · rw [if_pos hM]
        have hmem : RWRS.netRoot M ∈ F := by
          simpa [hF, Set.Finite.mem_toFinset] using hM
        refine le_trans (le_of_eq ?_)
          (Finset.single_le_sum (f := fun v => if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0)
            (fun v _ => by positivity) hmem)
        simp
      · rw [if_neg hM]; exact bot_le
    refine le_trans (rerootIter_mono n hpt N) ?_
    rw [rerootIter_finsetSum F n (fun v M => if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0) N]
    exact le_of_eq (Finset.sum_congr rfl fun v _ => rerootIter_rootIndicator v n N hN)
  have hsum : Filter.Tendsto
      (fun n : ℕ => ∑ v ∈ F, ENNReal.ofReal (RWRS.heat (RWRS.netGraph N) n (RWRS.netRoot N) v))
      Filter.atTop (nhds 0) := by
    have h0 : ∀ v ∈ F, Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal (RWRS.heat (RWRS.netGraph N) n (RWRS.netRoot N) v))
        Filter.atTop (nhds 0) := by
      intro v _
      have := (ENNReal.tendsto_ofReal (hHKV (RWRS.netRoot N) v))
      simpa using this
    have := tendsto_finsetSum F h0
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) hle

end RWRS.Support
