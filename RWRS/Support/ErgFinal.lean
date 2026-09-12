/-
The ergodicity of the i.i.d. marking.
-/
import RWRS.Support.ErgDecor
import RWRS.Support.ErgMarking

namespace RWRS.Support

open MeasureTheory
open scoped ENNReal NNReal

/-! ### Moving the root of an invariant event -/

/-- A rerooting-invariant event is unchanged by moving the root anywhere in the
ball, hence anywhere in the component of the root. -/
theorem mem_iff_netReroot {A : Set (RWRS.Net 1)} (hre : RWRS.RerootInvariant A) :
    ∀ (n : ℕ) (M : RWRS.Net 1) (v : ℕ), v ∈ netBallSet M n →
      (M ∈ A ↔ RWRS.netReroot M v ∈ A) := by
  intro n
  induction n with
  | zero =>
      intro M v hv
      have hvr : v = RWRS.netRoot M := hv
      subst hvr
      rw [show RWRS.netReroot M (RWRS.netRoot M) = M from rfl]
  | succ n ih =>
      intro M v hv
      rcases hv with hv | ⟨w, hw, hadj⟩
      · exact ih M v hv
      · have h1 : M ∈ A ↔ RWRS.netReroot M w ∈ A := ih M w hw
        have h2 : RWRS.netReroot M w ∈ A ↔ RWRS.netReroot (RWRS.netReroot M w) v ∈ A :=
          hre (RWRS.netReroot M w) v hadj
        rw [h1, h2, show RWRS.netReroot (RWRS.netReroot M w) v = RWRS.netReroot M v from rfl]

theorem mem_iff_netReroot_of_good {A : Set (RWRS.Net 1)} (hre : RWRS.RerootInvariant A)
    {M : RWRS.Net 1} (hM : RWRS.NetGood M) (v : ℕ) : M ∈ A ↔ RWRS.netReroot M v ∈ A := by
  obtain ⟨n, hn⟩ := exists_mem_netBallSet hM v
  exact mem_iff_netReroot hre n M v hn

/-! ### The ball is carried by an isomorphism -/

theorem mem_netBallSet_iso {m : ℕ} {N N' : RWRS.Net m} {φ : ℕ ≃ ℕ}
    (hadj : ∀ i j, (RWRS.netGraph N).Adj i j ↔ (RWRS.netGraph N').Adj (φ i) (φ j))
    (hroot : φ (RWRS.netRoot N) = RWRS.netRoot N') :
    ∀ (r i : ℕ), (i ∈ netBallSet N r ↔ φ i ∈ netBallSet N' r) := by
  intro r
  induction r with
  | zero =>
      intro i
      constructor
      · intro hi
        have : i = RWRS.netRoot N := hi
        subst this
        exact hroot
      · intro hi
        have : φ i = RWRS.netRoot N' := hi
        exact φ.injective (by rw [this, ← hroot])
  | succ r ih =>
      intro i
      constructor
      · rintro (hi | ⟨w, hw, hwi⟩)
        · exact Or.inl ((ih i).1 hi)
        · exact Or.inr ⟨φ w, (ih w).1 hw, (hadj w i).1 hwi⟩
      · rintro (hi | ⟨w', hw', hwi⟩)
        · exact Or.inl ((ih i).2 hi)
        · refine Or.inr ⟨φ.symm w', ?_, ?_⟩
          · exact (ih (φ.symm w')).2 (by rwa [Equiv.apply_symm_apply])
          · have := (hadj (φ.symm w') i).2
            rw [Equiv.apply_symm_apply] at this
            exact this hwi

theorem mem_netBallX_iso {m : ℕ} {N N' : RWRS.Net m} {φ : ℕ ≃ ℕ}
    (hadj : ∀ i j, (RWRS.netGraph N).Adj i j ↔ (RWRS.netGraph N').Adj (φ i) (φ j))
    (hroot : φ (RWRS.netRoot N) = RWRS.netRoot N') :
    ∀ (r i : ℕ), (i ∈ netBallX N r ↔ φ i ∈ netBallX N' r) := by
  intro r i
  constructor
  · rintro (hi | ⟨hr, hi⟩)
    · exact Or.inl ((mem_netBallSet_iso hadj hroot r i).1 hi)
    · exact Or.inr ⟨hr, fun s hs => hi s ((mem_netBallSet_iso hadj hroot s i).2 hs)⟩
  · rintro (hi | ⟨hr, hi⟩)
    · exact Or.inl ((mem_netBallSet_iso hadj hroot r i).2 hi)
    · exact Or.inr ⟨hr, fun s hs => hi s ((mem_netBallSet_iso hadj hroot s i).1 hs)⟩

/-! ### The algebra of the iterated reroot average -/

variable {m : ℕ}

theorem rerootAvg_const_mul (c : ℝ≥0∞) (Φ : RWRS.Net m → ℝ≥0∞) (N : RWRS.Net m) :
    rerootAvg (fun M => c * Φ M) N = c * rerootAvg Φ N := by
  simp only [rerootAvg, ← Finset.mul_sum, div_eq_mul_inv, mul_assoc]

theorem rerootIter_const_mul (c : ℝ≥0∞) :
    ∀ (n : ℕ) (Φ : RWRS.Net m → ℝ≥0∞) (N : RWRS.Net m),
      (rerootAvg^[n] fun M => c * Φ M) N = c * (rerootAvg^[n] Φ) N := by
  intro n
  induction n with
  | zero => intro Φ N; simp
  | succ n ih =>
      intro Φ N
      have hstep : ∀ g : RWRS.Net m → ℝ≥0∞, rerootAvg^[n + 1] g = rerootAvg^[n] (rerootAvg g) := by
        intro g; rw [Function.iterate_succ]; rfl
      rw [hstep, hstep]
      have : (rerootAvg fun M => c * Φ M) = fun M => c * rerootAvg Φ M :=
        funext fun M => rerootAvg_const_mul c Φ M
      rw [this, ih]

theorem rerootIter_add :
    ∀ (n : ℕ) (Φ Ψ : RWRS.Net m → ℝ≥0∞) (N : RWRS.Net m),
      (rerootAvg^[n] fun M => Φ M + Ψ M) N = (rerootAvg^[n] Φ) N + (rerootAvg^[n] Ψ) N := by
  intro n
  induction n with
  | zero => intro Φ Ψ N; simp
  | succ n ih =>
      intro Φ Ψ N
      have hstep : ∀ g : RWRS.Net m → ℝ≥0∞, rerootAvg^[n + 1] g = rerootAvg^[n] (rerootAvg g) := by
        intro g; rw [Function.iterate_succ]; rfl
      rw [hstep, hstep, hstep]
      have : (rerootAvg fun M => Φ M + Ψ M) = fun M => rerootAvg Φ M + rerootAvg Ψ M :=
        funext fun M => rerootAvg_add Φ Ψ M
      rw [this, ih]

theorem rerootIter_const (c : ℝ≥0∞) :
    ∀ (n : ℕ) (N : RWRS.Net m), RWRS.NetGood N → (rerootAvg^[n] fun _ => c) N = c := by
  intro n
  induction n with
  | zero => intro N _; simp
  | succ n ih =>
      intro N hN
      have hstep : rerootAvg^[n + 1] (fun _ : RWRS.Net m => c) = rerootAvg (rerootAvg^[n]
          fun _ : RWRS.Net m => c) := by
        rw [Function.iterate_succ']; rfl
      rw [hstep, rerootAvg]
      have hc : ∀ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
          (rerootAvg^[n] fun _ : RWRS.Net m => c) (RWRS.netReroot N y) = c :=
        fun y _ => ih (RWRS.netReroot N y) hN
      rw [Finset.sum_congr rfl hc]
      have hd : ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) ≠ 0 := by
        simpa using (degree_netRoot_pos hN).ne'
      have hdt : ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_comm,
        mul_div_assoc, ENNReal.div_self hd hdt, mul_one]

theorem rerootIter_congr_reroot_le {Φ Ψ : RWRS.Net m → ℝ≥0∞} :
    ∀ (n : ℕ) (N : RWRS.Net m),
      (∀ v : ℕ, Φ (RWRS.netReroot N v) ≤ Ψ (RWRS.netReroot N v)) →
      (rerootAvg^[n] Φ) N ≤ (rerootAvg^[n] Ψ) N := by
  intro n
  induction n with
  | zero =>
      intro N hN
      have hb := hN (RWRS.netRoot N)
      rw [show RWRS.netReroot N (RWRS.netRoot N) = N from rfl] at hb
      simpa using hb
  | succ n ih =>
      intro N hN
      have hstep : ∀ g : RWRS.Net m → ℝ≥0∞, rerootAvg^[n + 1] g = rerootAvg (rerootAvg^[n] g) := by
        intro g; rw [Function.iterate_succ']; rfl
      rw [hstep Φ, hstep Ψ, rerootAvg, rerootAvg]
      refine ENNReal.div_le_div_right (Finset.sum_le_sum fun y _ => ?_) _
      exact ih (RWRS.netReroot N y) (fun v => hN v)

theorem rerootIter_eq_of_reroot {Φ : RWRS.Net m → ℝ≥0∞} :
    ∀ (n : ℕ) (N : RWRS.Net m), RWRS.NetGood N → (∀ v : ℕ, Φ (RWRS.netReroot N v) = Φ N) →
      (rerootAvg^[n] Φ) N = Φ N := by
  intro n
  induction n with
  | zero => intro N _ _; simp
  | succ n ih =>
      intro N hN hΦ
      have hstep : rerootAvg^[n + 1] Φ = rerootAvg (rerootAvg^[n] Φ) := by
        rw [Function.iterate_succ']; rfl
      rw [hstep, rerootAvg]
      have hc : ∀ y ∈ (RWRS.netGraph N).neighborFinset (RWRS.netRoot N),
          (rerootAvg^[n] Φ) (RWRS.netReroot N y) = Φ N := by
        intro y _
        rw [ih (RWRS.netReroot N y) hN (fun v => by
          rw [show RWRS.netReroot (RWRS.netReroot N y) v = RWRS.netReroot N v from rfl,
            hΦ v, ← hΦ y])]
        exact hΦ y
      rw [Finset.sum_congr rfl hc]
      have hd : ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) ≠ 0 := by
        simpa using (degree_netRoot_pos hN).ne'
      have hdt : ((RWRS.netGraph N).degree (RWRS.netRoot N) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_comm,
        mul_div_assoc, ENNReal.div_self hd hdt, mul_one]

theorem esub_rerootIter_le {Φ Ψ : RWRS.Net m → ℝ≥0∞} (n : ℕ) (N : RWRS.Net m) :
    esub ((rerootAvg^[n] Φ) N) ((rerootAvg^[n] Ψ) N)
      ≤ (rerootAvg^[n] fun M => esub (Φ M) (Ψ M)) N := by
  refine esub_le_of_le_add ?_ ?_
  · calc (rerootAvg^[n] Φ) N
        ≤ (rerootAvg^[n] fun M => Ψ M + esub (Φ M) (Ψ M)) N :=
          rerootIter_mono n (fun M => le_add_esub (Φ M) (Ψ M)) N
      _ = (rerootAvg^[n] Ψ) N + (rerootAvg^[n] fun M => esub (Φ M) (Ψ M)) N :=
          rerootIter_add n Ψ (fun M => esub (Φ M) (Ψ M)) N
  · calc (rerootAvg^[n] Ψ) N
        ≤ (rerootAvg^[n] fun M => Φ M + esub (Φ M) (Ψ M)) N := by
          refine rerootIter_mono n (fun M => ?_) N
          rw [esub_comm (Φ M) (Ψ M)]
          exact le_add_esub (Ψ M) (Φ M)
      _ = (rerootAvg^[n] Φ) N + (rerootAvg^[n] fun M => esub (Φ M) (Ψ M)) N :=
          rerootIter_add n Φ (fun M => esub (Φ M) (Ψ M)) N

theorem lintegral_rerootIter_exchange {P : Measure (ℕ → ℝ)} [SFinite P] :
    ∀ (n : ℕ) (Ψ : RWRS.Net m → (ℕ → ℝ) → ℝ≥0∞), (∀ M, Measurable (Ψ M)) →
      ∀ N : RWRS.Net m,
        ∫⁻ ξ, (rerootAvg^[n] fun M => Ψ M ξ) N ∂P = (rerootAvg^[n] fun M => ∫⁻ ξ, Ψ M ξ ∂P) N := by
  intro n
  induction n with
  | zero => intro Ψ _ N; simp
  | succ n ih =>
      intro Ψ hΨ N
      have hstep : ∀ g : RWRS.Net m → ℝ≥0∞, rerootAvg^[n + 1] g = rerootAvg^[n] (rerootAvg g) := by
        intro g; rw [Function.iterate_succ]; rfl
      have hmeas : ∀ M : RWRS.Net m, Measurable fun ξ => rerootAvg (fun M' => Ψ M' ξ) M := by
        intro M
        simp only [rerootAvg, div_eq_mul_inv]
        exact (Finset.measurable_sum _ fun y _ => hΨ (RWRS.netReroot M y)).mul_const _
      have h1 : ∫⁻ ξ, (rerootAvg^[n + 1] fun M => Ψ M ξ) N ∂P
          = ∫⁻ ξ, (rerootAvg^[n] fun M => rerootAvg (fun M' => Ψ M' ξ) M) N ∂P := by
        refine lintegral_congr fun ξ => ?_
        rw [hstep]
      rw [h1, ih (fun M ξ => rerootAvg (fun M' => Ψ M' ξ) M) hmeas N, hstep]
      have hfun : (fun M : RWRS.Net m => ∫⁻ ξ, rerootAvg (fun M' => Ψ M' ξ) M ∂P)
          = rerootAvg fun M : RWRS.Net m => ∫⁻ ξ, Ψ M ξ ∂P :=
        funext fun M => lintegral_rerootAvg_exchange Ψ hΨ M
      rw [hfun]

/-! ### The approximation error as a test function -/

/-- The mark average of the distance between the indicator of `A` and its splice
average of radius `r`. -/
noncomputable def approxError (ν : Measure ℝ) (r : ℕ) (A : Set (RWRS.Net 1)) (N : RWRS.Net 0) :
    ℝ≥0∞ :=
  ∫⁻ ξ, esub (A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ)))
    (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ) ∂(RWRS.iidLaw ℕ ν)

theorem netInvariant_indicator {A : Set (RWRS.Net 1)} (hiso : RWRS.NetInvariantSet A) :
    RWRS.NetInvariant (A.indicator (fun _ => (1 : ℝ≥0∞))) := by
  intro M M' hM
  by_cases hmem : M ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hiso M M' hM).1 hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun hc => hmem ((hiso M M' hM).2 hc))]

theorem measurable_approxError (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ)
    {A : Set (RWRS.Net 1)} (hA : MeasurableSet A) : Measurable (approxError ν r A) := by

  have h1 : Measurable fun p : RWRS.Net 0 × (ℕ → ℝ) =>
      A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap p) :=
    (measurable_const.indicator hA).comp measurable_markMap
  have h2 : Measurable fun p : RWRS.Net 0 × (ℕ → ℝ) =>
      ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) p.1 p.2 :=
    measurable_ballAvg ν r (measurable_const.indicator hA)
  have huc : Measurable (Function.uncurry fun (N : RWRS.Net 0) (ξ : ℕ → ℝ) =>
      esub (A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ)))
        (ballAvg ν r (A.indicator (fun _ => (1 : ℝ≥0∞))) N ξ)) := measurable_esub h1 h2
  exact huc.lintegral_prod_right'

theorem netInvariant_approxError (ν : Measure ℝ) [IsProbabilityMeasure ν] (r : ℕ)
    {A : Set (RWRS.Net 1)} (hA : MeasurableSet A) (hiso : RWRS.NetInvariantSet A) :
    RWRS.NetInvariant (approxError ν r A) := by

  set u : RWRS.Net 1 → ℝ≥0∞ := A.indicator (fun _ => (1 : ℝ≥0∞)) with hu
  have huinv : RWRS.NetInvariant u := netInvariant_indicator hiso
  have humeas : Measurable u := measurable_const.indicator hA
  rintro N N' ⟨φ, hadj, hroot, hmark⟩
  have hmp : MeasurePreserving (LatticeProb.coordShift (X := ℝ) (⇑φ))
      (RWRS.iidLaw ℕ ν) (RWRS.iidLaw ℕ ν) :=
    LatticeProb.measurePreserving_coordShift (fun _ : ℕ => ν) φ.injective fun _ => rfl
  have hint : Measurable fun ξ : ℕ → ℝ =>
      esub (u (markMap (N', ξ))) (ballAvg ν r u N' ξ) :=
    measurable_esub ((humeas.comp measurable_markMap).comp
        ((measurable_const (a := N')).prodMk measurable_id))
      ((measurable_ballAvg ν r humeas).comp ((measurable_const (a := N')).prodMk measurable_id))
  have hpt : ∀ ξ : ℕ → ℝ,
      esub (u (markMap (N, LatticeProb.coordShift (⇑φ) ξ)))
          (ballAvg ν r u N (LatticeProb.coordShift (⇑φ) ξ))
        = esub (u (markMap (N', ξ))) (ballAvg ν r u N' ξ) := by
    intro ξ
    have hiso1 : u (markMap (N, LatticeProb.coordShift (⇑φ) ξ)) = u (markMap (N', ξ)) :=
      huinv _ _ ⟨φ, hadj, hroot, fun i => rfl⟩
    have hiso2 : ballAvg ν r u N (LatticeProb.coordShift (⇑φ) ξ) = ballAvg ν r u N' ξ := by
      have hswap : ballAvg ν r u N (LatticeProb.coordShift (⇑φ) ξ)
          = ∫⁻ η, u (markMap (N, netComb N r (LatticeProb.coordShift (⇑φ) ξ)
              (LatticeProb.coordShift (⇑φ) η))) ∂(RWRS.iidLaw ℕ ν) :=
        (hmp.lintegral_comp ((humeas.comp measurable_markMap).comp
          ((measurable_const (a := N)).prodMk
            ((measurable_netComb r).comp ((measurable_const (a := N)).prodMk
              ((measurable_const (a := LatticeProb.coordShift (⇑φ) ξ)).prodMk
                measurable_id)))))).symm
      rw [hswap, ballAvg]
      refine lintegral_congr fun η => ?_
      have hcomb : netComb N r (LatticeProb.coordShift (⇑φ) ξ) (LatticeProb.coordShift (⇑φ) η)
          = LatticeProb.coordShift (⇑φ) (netComb N' r ξ η) := by
        funext i
        by_cases hi : i ∈ netBallX N r
        · rw [netComb_of_mem hi]
          have hi' : φ i ∈ netBallX N' r := (mem_netBallX_iso hadj hroot r i).1 hi
          simp only [LatticeProb.coordShift_apply, netComb_of_mem hi']
        · rw [netComb_of_notMem hi]
          have hi' : φ i ∉ netBallX N' r := fun hc => hi ((mem_netBallX_iso hadj hroot r i).2 hc)
          simp only [LatticeProb.coordShift_apply, netComb_of_notMem hi']
      rw [hcomb]
      exact huinv _ _ ⟨φ, hadj, hroot, fun i => rfl⟩
    rw [hiso1, hiso2]
  calc approxError ν r A N
      = ∫⁻ ξ, esub (u (markMap (N, LatticeProb.coordShift (⇑φ) ξ)))
          (ballAvg ν r u N (LatticeProb.coordShift (⇑φ) ξ)) ∂(RWRS.iidLaw ℕ ν) := by
        exact (hmp.lintegral_comp (measurable_esub
          ((humeas.comp measurable_markMap).comp
            ((measurable_const (a := N)).prodMk measurable_id))
          ((measurable_ballAvg ν r humeas).comp
            ((measurable_const (a := N)).prodMk measurable_id)))).symm
    _ = ∫⁻ ξ, esub (u (markMap (N', ξ))) (ballAvg ν r u N' ξ) ∂(RWRS.iidLaw ℕ ν) :=
        lintegral_congr hpt
    _ = approxError ν r A N' := rfl

/-! ### The near and far parts of the walk average -/

theorem esub_mul_le {x y x' y' : ℝ≥0∞} (hx : x ≤ 1) (hy : y ≤ 1) (hx' : x' ≤ 1) (hy' : y' ≤ 1) :
    esub (x * x') (y * y') ≤ esub x y + esub x' y' := by
  refine esub_le_of_le_add ?_ ?_
  · calc x * x' ≤ (y + esub x y) * x' := by gcongr; exact le_add_esub x y
      _ = y * x' + esub x y * x' := by ring
      _ ≤ y * (y' + esub x' y') + esub x y * 1 := by
          gcongr
          · exact le_add_esub x' y'
      _ = y * y' + (esub x y + y * esub x' y') := by ring
      _ ≤ y * y' + (esub x y + esub x' y') := by
          gcongr
          calc y * esub x' y' ≤ 1 * esub x' y' := by gcongr
            _ = esub x' y' := one_mul _
  · calc y * y' ≤ (x + esub y x) * y' := by gcongr; exact le_add_esub y x
      _ = x * y' + esub y x * y' := by ring
      _ ≤ x * (x' + esub y' x') + esub y x * 1 := by
          gcongr
          · exact le_add_esub y' x'
      _ = x * x' + (esub y x + x * esub y' x') := by ring
      _ ≤ x * x' + (esub x y + esub x' y') := by
          rw [esub_comm y x, esub_comm y' x']
          gcongr
          calc x * esub x' y' ≤ 1 * esub x' y' := by gcongr
            _ = esub x' y' := one_mul _

theorem measurable_rerootIter_apply :
    ∀ (n : ℕ) (Ψ : RWRS.Net m → (ℕ → ℝ) → ℝ≥0∞), (∀ M, Measurable (Ψ M)) →
      ∀ N : RWRS.Net m, Measurable fun ξ => (rerootAvg^[n] fun M => Ψ M ξ) N := by
  intro n
  induction n with
  | zero => intro Ψ hΨ N; simpa using hΨ N
  | succ n ih =>
      intro Ψ hΨ N
      have hmeas : ∀ M : RWRS.Net m, Measurable fun ξ => rerootAvg (fun M' => Ψ M' ξ) M := by
        intro M
        simp only [rerootAvg, div_eq_mul_inv]
        exact (Finset.measurable_sum _ fun y _ => hΨ (RWRS.netReroot M y)).mul_const _
      have hfun : (fun ξ => (rerootAvg^[n + 1] fun M => Ψ M ξ) N)
          = fun ξ => (rerootAvg^[n] fun M => rerootAvg (fun M' => Ψ M' ξ) M) N := by
        funext ξ
        rw [Function.iterate_succ]
        rfl
      rw [hfun]
      exact ih (fun M ξ => rerootAvg (fun M' => Ψ M' ξ) M) hmeas N

open scoped Classical in
/-- The indicator of the networks whose ball meets the ball of `N`. -/
noncomputable def nearInd (N : RWRS.Net 0) (r : ℕ) : RWRS.Net 0 → ℝ≥0∞ :=
  fun M => if Disjoint (netBallX N r) (netBallX M r) then 0 else 1

open scoped Classical in
/-- The indicator of the networks whose ball misses the ball of `N`. -/
noncomputable def farInd (N : RWRS.Net 0) (r : ℕ) : RWRS.Net 0 → ℝ≥0∞ :=
  fun M => if Disjoint (netBallX N r) (netBallX M r) then 1 else 0

theorem farInd_add_nearInd (N : RWRS.Net 0) (r : ℕ) (M : RWRS.Net 0) :
    farInd N r M + nearInd N r M = 1 := by
  classical
  by_cases h : Disjoint (netBallX N r) (netBallX M r) <;> simp [farInd, nearInd, h]

theorem nearInd_le_one (N : RWRS.Net 0) (r : ℕ) (M : RWRS.Net 0) : nearInd N r M ≤ 1 := by
  classical
  by_cases h : Disjoint (netBallX N r) (netBallX M r) <;> simp [nearInd, h]

theorem mul_farInd_le (N : RWRS.Net 0) (r : ℕ) (M : RWRS.Net 0) (x : ℝ≥0∞) :
    farInd N r M * x ≤ x := by
  classical
  by_cases h : Disjoint (netBallX N r) (netBallX M r) <;> simp [farInd, h]

theorem le_mul_farInd_add (N : RWRS.Net 0) (r : ℕ) (M : RWRS.Net 0) {x : ℝ≥0∞} (hx : x ≤ 1) :
    x ≤ farInd N r M * x + nearInd N r M := by
  classical
  by_cases h : Disjoint (netBallX N r) (netBallX M r) <;> simp [farInd, nearInd, h, hx]

/-- **The walk leaves the ball of the starting network.** -/
theorem tendsto_nearIter {N : RWRS.Net 0} (hN : RWRS.NetGood N)
    (hHKV : RWRS.External.HeatKernelVanishing (RWRS.netGraph N)) (r : ℕ) :
    Filter.Tendsto (fun n : ℕ => (rerootAvg^[n] (nearInd N r)) N) Filter.atTop (nhds 0) := by
  classical
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_rerootIter_closedBall hN hHKV (2 * r)) (fun _ => bot_le) (fun n => ?_)
  refine rerootIter_congr_reroot_le n N fun v => ?_
  by_cases h : Disjoint (netBallX N r) (netBallX (RWRS.netReroot N v) r)
  · simp [nearInd, h]
  · have hv : v ∈ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) (2 * r) :=
      mem_closedBall_of_not_disjoint_netBallX hN v r h
    rw [if_pos (show RWRS.netRoot (RWRS.netReroot N v)
      ∈ RWRS.closedBall (RWRS.netGraph N) (RWRS.netRoot N) (2 * r) from hv)]
    simp [nearInd, h]

/-! ### A measurable majorant for the near average -/

theorem measurable_rerootIter : ∀ (n : ℕ) {Φ : RWRS.Net m → ℝ≥0∞}, Measurable Φ →
    Measurable (rerootAvg^[n] Φ) := by
  intro n
  induction n with
  | zero => intro Φ hΦ; simpa using hΦ
  | succ n ih =>
      intro Φ hΦ
      have hstep : rerootAvg^[n + 1] Φ = rerootAvg^[n] (rerootAvg Φ) := by
        rw [Function.iterate_succ]; rfl
      rw [hstep]
      exact ih (measurable_rerootAvg hΦ)

theorem measurable_rootIndicator (v : ℕ) :
    Measurable fun M : RWRS.Net m => if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0 :=
  Measurable.ite (measurable_netRoot (measurableSet_singleton v)) measurable_const
    measurable_const

open scoped Classical in
/-- The walk average of the indicator of the ball of radius `2r` around the
root: a measurable majorant for the average of the near indicator. -/
noncomputable def nearBound (r n : ℕ) (N : RWRS.Net 0) : ℝ≥0∞ :=
  ∑' v : ℕ, if v ∈ netBallSet N (2 * r) then
    (rerootAvg^[n] fun M : RWRS.Net 0 => if RWRS.netRoot M = v then (1 : ℝ≥0∞) else 0) N else 0

open scoped Classical in
theorem measurable_nearBound (r n : ℕ) : Measurable (nearBound r n) := by
  classical
  refine Measurable.tsum fun v => ?_
  exact Measurable.ite (measurableSet_mem_netBallSet v (2 * r))
    (measurable_rerootIter n (measurable_rootIndicator v)) measurable_const

open scoped Classical in
theorem nearIter_le_nearBound {N : RWRS.Net 0} (hN : RWRS.NetGood N) (r n : ℕ) :
    (rerootAvg^[n] (nearInd N r)) N ≤ nearBound r n N := by
  classical
  set F : Finset ℕ := (finite_netBallSet N (2 * r)).toFinset with hF
  have hmemF : ∀ w : ℕ, w ∈ F ↔ w ∈ netBallSet N (2 * r) := by
    intro w; rw [hF, Set.Finite.mem_toFinset]
  have hle : (rerootAvg^[n] (nearInd N r)) N
      ≤ (rerootAvg^[n] fun M : RWRS.Net 0 =>
          ∑ w ∈ F, if RWRS.netRoot M = w then (1 : ℝ≥0∞) else 0) N := by
    refine rerootIter_congr_reroot_le n N fun v => ?_
    by_cases h : Disjoint (netBallX N r) (netBallX (RWRS.netReroot N v) r)
    · simp [nearInd, h]
    · have hv : v ∈ netBallSet N (2 * r) := by
        rw [netBallSet_eq_closedBall]
        exact mem_closedBall_of_not_disjoint_netBallX hN v r h
      have hvF : v ∈ F := (hmemF v).2 hv
      have hone : (1 : ℝ≥0∞)
          ≤ ∑ w ∈ F, if RWRS.netRoot (RWRS.netReroot N v) = w then (1 : ℝ≥0∞) else 0 := by
        refine le_trans (le_of_eq ?_)
          (Finset.single_le_sum
            (f := fun w => if RWRS.netRoot (RWRS.netReroot N v) = w then (1 : ℝ≥0∞) else 0)
            (fun w _ => bot_le) hvF)
        rw [show RWRS.netRoot (RWRS.netReroot N v) = v from rfl, if_pos rfl]
      simpa [nearInd, h] using hone
  refine le_trans hle ?_
  rw [rerootIter_finsetSum F n (fun w M => if RWRS.netRoot M = w then (1 : ℝ≥0∞) else 0) N]
  calc (∑ w ∈ F, (rerootAvg^[n] fun M : RWRS.Net 0 =>
          if RWRS.netRoot M = w then (1 : ℝ≥0∞) else 0) N)
      = ∑ w ∈ F, if w ∈ netBallSet N (2 * r) then
          (rerootAvg^[n] fun M : RWRS.Net 0 =>
            if RWRS.netRoot M = w then (1 : ℝ≥0∞) else 0) N else 0 :=
        Finset.sum_congr rfl fun w hw => (if_pos ((hmemF w).1 hw)).symm
    _ ≤ nearBound r n N := ENNReal.sum_le_tsum F

open scoped Classical in
theorem tendsto_nearBound {N : RWRS.Net 0} (hN : RWRS.NetGood N)
    (hHKV : RWRS.External.HeatKernelVanishing (RWRS.netGraph N)) (r : ℕ) :
    Filter.Tendsto (fun n : ℕ => nearBound r n N) Filter.atTop (nhds 0) := by
  classical
  set F : Finset ℕ := (finite_netBallSet N (2 * r)).toFinset with hF
  have hmemF : ∀ w : ℕ, w ∈ F ↔ w ∈ netBallSet N (2 * r) := by
    intro w; rw [hF, Set.Finite.mem_toFinset]
  have heq : (fun n : ℕ => nearBound r n N)
      = fun n : ℕ => ∑ v ∈ F, ENNReal.ofReal
          (RWRS.heat (RWRS.netGraph N) n (RWRS.netRoot N) v) := by
    funext n
    rw [nearBound, tsum_eq_sum (s := F) (fun v hv => if_neg (fun hc => hv ((hmemF v).2 hc)))]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [if_pos ((hmemF v).1 hv), rerootIter_rootIndicator v n N hN]
  rw [heq]
  have h0 : ∀ v ∈ F, Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (RWRS.heat (RWRS.netGraph N) n (RWRS.netRoot N) v))
      Filter.atTop (nhds 0) := by
    intro v _
    simpa using ENNReal.tendsto_ofReal (hHKV (RWRS.netRoot N) v)
  simpa using tendsto_finsetSum F h0

open scoped Classical in
theorem nearBound_le_one {N : RWRS.Net 0} (hN : RWRS.NetGood N) (r n : ℕ) :
    nearBound r n N ≤ 1 := by
  classical
  set F : Finset ℕ := (finite_netBallSet N (2 * r)).toFinset with hF
  have hmemF : ∀ w : ℕ, w ∈ F ↔ w ∈ netBallSet N (2 * r) := by
    intro w; rw [hF, Set.Finite.mem_toFinset]
  have heq : nearBound r n N
      = (rerootAvg^[n] fun M : RWRS.Net 0 =>
          ∑ w ∈ F, if RWRS.netRoot M = w then (1 : ℝ≥0∞) else 0) N := by
    rw [rerootIter_finsetSum F n (fun w M => if RWRS.netRoot M = w then (1 : ℝ≥0∞) else 0) N,
      nearBound, tsum_eq_sum (s := F) (fun v hv => if_neg (fun hc => hv ((hmemF v).2 hc)))]
    exact Finset.sum_congr rfl fun w hw => if_pos ((hmemF w).1 hw)
  rw [heq]
  refine le_trans (rerootIter_mono n (h' := fun _ => (1 : ℝ≥0∞)) (fun M => ?_) N)
    (le_of_eq (rerootIter_const 1 n N hN))
  rw [Finset.sum_ite_eq F (RWRS.netRoot M) (fun _ => (1 : ℝ≥0∞))]
  by_cases h : RWRS.netRoot M ∈ F <;> simp [h]


/-! ### The ergodicity of the marked law -/

theorem markAvg_reroot {A : Set (RWRS.Net 1)} (hre : RWRS.RerootInvariant A) (ν : Measure ℝ)
    {N : RWRS.Net 0} (hN : RWRS.NetGood N) (v : ℕ) :
    markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) (RWRS.netReroot N v)
      = markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N := by
  refine lintegral_congr fun ξ => ?_
  have hg : RWRS.NetGood (markMap (N, ξ)) := hN
  have hmm : markMap (RWRS.netReroot N v, ξ) = RWRS.netReroot (markMap (N, ξ)) v := rfl
  rw [hmm]
  by_cases h : markMap (N, ξ) ∈ A
  · rw [Set.indicator_of_mem ((mem_iff_netReroot_of_good hre hg v).1 h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hc => h ((mem_iff_netReroot_of_good hre hg v).2 hc)),
      Set.indicator_of_notMem h]

theorem indicator_markMap_reroot {A : Set (RWRS.Net 1)} (hre : RWRS.RerootInvariant A)
    {N : RWRS.Net 0} (hN : RWRS.NetGood N) (v : ℕ) (ξ : ℕ → ℝ) :
    A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (RWRS.netReroot N v, ξ))
      = A.indicator (fun _ => (1 : ℝ≥0∞)) (markMap (N, ξ)) := by
  have hg : RWRS.NetGood (markMap (N, ξ)) := hN
  have hmm : markMap (RWRS.netReroot N v, ξ) = RWRS.netReroot (markMap (N, ξ)) v := rfl
  rw [hmm]
  by_cases h : markMap (N, ξ) ∈ A
  · rw [Set.indicator_of_mem ((mem_iff_netReroot_of_good hre hg v).1 h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun hc => h ((mem_iff_netReroot_of_good hre hg v).2 hc)),
      Set.indicator_of_notMem h]

/-- **The probability of an invariant event of the marked network is a square.**
This is the estimate of `rwrs.tex:319-325`. -/
theorem markAvg_mul_self
    (hHKV : ∀ N : RWRS.Net 0, RWRS.NetGood N →
      RWRS.External.HeatKernelVanishing (RWRS.netGraph N))
    (Q : Measure (RWRS.Net 0)) [IsProbabilityMeasure Q] (hgood : ∀ᵐ N ∂Q, RWRS.NetGood N)
    (hstat : RWRS.IsStationaryNet Q) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {A : Set (RWRS.Net 1)} (hA : MeasurableSet A) (hiso : RWRS.NetInvariantSet A)
    (hre : RWRS.RerootInvariant A) {C : ℝ≥0∞} (hC1 : C ≤ 1)
    (hCae : ∀ᵐ N ∂Q, markAvg ν (A.indicator (fun _ => (1 : ℝ≥0∞))) N = C) :
    C = C * C := by
  classical
  haveI : IsProbabilityMeasure (RWRS.iidLaw ℕ ν) := instIsProbabilityMeasureIidLaw ν
  set u : RWRS.Net 1 → ℝ≥0∞ := A.indicator (fun _ => (1 : ℝ≥0∞)) with hu
  have humeas : Measurable u := measurable_const.indicator hA
  have hu1 : ∀ M, u M ≤ 1 := fun M =>
    Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => bot_le)
  have huu : ∀ M, u M * u M = u M := by
    intro M
    by_cases h : M ∈ A
    · rw [hu, Set.indicator_of_mem h, mul_one]
    · rw [hu, Set.indicator_of_notMem h, mul_zero]
  have hCval : ∫⁻ N, markAvg ν u N ∂Q = C := by
    rw [lintegral_congr_ae hCae, lintegral_const, measure_univ, mul_one]
  have hCC1 : C * C ≤ 1 := by
    calc C * C ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  -- the estimate at a fixed accuracy
  have hmain : ∀ ε : ℝ≥0∞, 0 < ε → C ≤ C * C + 2 * ε ∧ C * C ≤ C + 2 * ε := by
    intro ε hε
    obtain ⟨r, hr⟩ := exists_ballAvg_approx Q ν hA hε
    set g : RWRS.Net 0 → ℝ≥0∞ := approxError ν r A with hg
    have hgmeas : Measurable g := measurable_approxError ν r hA
    have hginv : RWRS.NetInvariant g := netInvariant_approxError ν r hA hiso
    have hgint : ∫⁻ N, g N ∂Q < ε := hr
    set f : RWRS.Net 0 → (ℕ → ℝ) → ℝ≥0∞ := fun M ξ => ballAvg ν r u M ξ with hf
    have hf1 : ∀ M ξ, f M ξ ≤ 1 := fun M ξ => ballAvg_le_one ν r hu1 M ξ
    have hfmeas : ∀ M, Measurable (f M) := fun M => measurable_ballAvg_fixed ν r humeas M
    have hfint : ∀ M, ∫⁻ ξ, f M ξ ∂(RWRS.iidLaw ℕ ν) = markAvg ν u M := fun M =>
      lintegral_ballAvg ν r humeas M
    set a : RWRS.Net 0 → (ℕ → ℝ) → ℝ≥0∞ := fun M ξ => u (markMap (M, ξ)) with ha
    have hameas : ∀ M, Measurable (a M) := fun M =>
      (humeas.comp measurable_markMap).comp ((measurable_const (a := M)).prodMk measurable_id)
    have hgdef : ∀ M, g M = ∫⁻ ξ, esub (a M ξ) (f M ξ) ∂(RWRS.iidLaw ℕ ν) := fun M => rfl
    -- the pointwise estimate
    have hpt : ∀ᵐ N ∂Q, ∀ n : ℕ,
        markAvg ν u N ≤ C * C + (nearBound r n N + (g N + (rerootAvg^[n] g) N))
        ∧ C * C ≤ markAvg ν u N + (nearBound r n N + (g N + (rerootAvg^[n] g) N)) := by
      filter_upwards [hgood, hCae] with N hN hCN
      intro n
      set near : ℝ≥0∞ := (rerootAvg^[n] (nearInd N r)) N with hnear
      set b : ℝ≥0∞ := g N + (rerootAvg^[n] g) N with hb
      -- the three averages
      set I1 : ℝ≥0∞ := ∫⁻ ξ, a N ξ * (rerootAvg^[n] fun M => a M ξ) N ∂(RWRS.iidLaw ℕ ν) with hI1
      set I2 : ℝ≥0∞ := ∫⁻ ξ, f N ξ * (rerootAvg^[n] fun M => f M ξ) N ∂(RWRS.iidLaw ℕ ν) with hI2
      set I3 : ℝ≥0∞ := ∫⁻ ξ, f N ξ * (rerootAvg^[n] fun M => farInd N r M * f M ξ) N
        ∂(RWRS.iidLaw ℕ ν) with hI3
      have hI1eq : I1 = markAvg ν u N := by
        rw [hI1]
        have hstep : ∀ ξ : ℕ → ℝ, a N ξ * (rerootAvg^[n] fun M => a M ξ) N = a N ξ := by
          intro ξ
          rw [rerootIter_eq_of_reroot n N hN (fun v => indicator_markMap_reroot hre hN v ξ), huu]
        rw [lintegral_congr hstep]
        rfl
      have hI12 : I1 ≤ I2 + b ∧ I2 ≤ I1 + b := by
        have hmeas2 : Measurable fun ξ => f N ξ * (rerootAvg^[n] fun M => f M ξ) N :=
          (hfmeas N).mul (measurable_rerootIter_apply n f hfmeas N)
        have hmeas1 : Measurable fun ξ => a N ξ * (rerootAvg^[n] fun M => a M ξ) N :=
          (hameas N).mul (measurable_rerootIter_apply n a hameas N)
        have hmease : Measurable fun ξ => esub (a N ξ) (f N ξ) :=
          measurable_esub (hameas N) (hfmeas N)
        have hexch : ∫⁻ ξ, (rerootAvg^[n] fun M => esub (a M ξ) (f M ξ)) N ∂(RWRS.iidLaw ℕ ν)
            = (rerootAvg^[n] g) N := by
          rw [lintegral_rerootIter_exchange n (fun M ξ => esub (a M ξ) (f M ξ))
            (fun M => measurable_esub (hameas M) (hfmeas M)) N]
          rfl
        have hbound : ∀ ξ : ℕ → ℝ,
            esub (a N ξ * (rerootAvg^[n] fun M => a M ξ) N)
                (f N ξ * (rerootAvg^[n] fun M => f M ξ) N)
              ≤ esub (a N ξ) (f N ξ) + (rerootAvg^[n] fun M => esub (a M ξ) (f M ξ)) N := by
          intro ξ
          refine le_trans (esub_mul_le (hu1 _) (hf1 N ξ)
            (rerootIter_le_one (fun M => hu1 _) n N hN)
            (rerootIter_le_one (fun M => hf1 M ξ) n N hN)) ?_
          exact add_le_add le_rfl
            (esub_rerootIter_le (Φ := fun M => a M ξ) (Ψ := fun M => f M ξ) n N)
        have hE : ∫⁻ ξ, esub (a N ξ) (f N ξ) ∂(RWRS.iidLaw ℕ ν) = g N := rfl
        constructor
        · have hmid : ∀ ξ : ℕ → ℝ,
              a N ξ * (rerootAvg^[n] fun M => a M ξ) N
                ≤ f N ξ * (rerootAvg^[n] fun M => f M ξ) N
                  + (esub (a N ξ) (f N ξ) + (rerootAvg^[n] fun M => esub (a M ξ) (f M ξ)) N) :=
            fun ξ => le_trans (le_add_esub _ _) (add_le_add le_rfl (hbound ξ))
          have hval : ∫⁻ ξ, (f N ξ * (rerootAvg^[n] fun M => f M ξ) N
                  + (esub (a N ξ) (f N ξ) + (rerootAvg^[n] fun M => esub (a M ξ) (f M ξ)) N))
                  ∂(RWRS.iidLaw ℕ ν) = I2 + b := by
            rw [lintegral_add_left hmeas2, lintegral_add_left hmease, hexch, hE, ← hI2, ← hb]
          rw [hI1, ← hval]
          exact lintegral_mono hmid
        · have hmid : ∀ ξ : ℕ → ℝ,
              f N ξ * (rerootAvg^[n] fun M => f M ξ) N
                ≤ a N ξ * (rerootAvg^[n] fun M => a M ξ) N
                  + (esub (a N ξ) (f N ξ) + (rerootAvg^[n] fun M => esub (a M ξ) (f M ξ)) N) := by
            intro ξ
            refine le_trans (le_add_esub _ _) (add_le_add le_rfl ?_)
            rw [esub_comm]
            exact hbound ξ
          have hval : ∫⁻ ξ, (a N ξ * (rerootAvg^[n] fun M => a M ξ) N
                  + (esub (a N ξ) (f N ξ) + (rerootAvg^[n] fun M => esub (a M ξ) (f M ξ)) N))
                  ∂(RWRS.iidLaw ℕ ν) = I1 + b := by
            rw [lintegral_add_left hmeas1, lintegral_add_left hmease, hexch, hE, ← hI1, ← hb]
          rw [hI2, ← hval]
          exact lintegral_mono hmid
      have hI23 : I2 ≤ I3 + near ∧ I3 ≤ I2 := by
        constructor
        · have hstep : ∀ ξ : ℕ → ℝ,
              f N ξ * (rerootAvg^[n] fun M => f M ξ) N
                ≤ f N ξ * (rerootAvg^[n] fun M => farInd N r M * f M ξ) N + near := by
            intro ξ
            have h1 : (rerootAvg^[n] fun M => f M ξ) N
                ≤ (rerootAvg^[n] fun M => farInd N r M * f M ξ + nearInd N r M) N :=
              rerootIter_mono n (fun M => le_mul_farInd_add N r M (hf1 M ξ)) N
            have h2 : (rerootAvg^[n] fun M => farInd N r M * f M ξ + nearInd N r M) N
                = (rerootAvg^[n] fun M => farInd N r M * f M ξ) N + near :=
              rerootIter_add n (fun M => farInd N r M * f M ξ) (nearInd N r) N
            calc f N ξ * (rerootAvg^[n] fun M => f M ξ) N
                ≤ f N ξ * ((rerootAvg^[n] fun M => farInd N r M * f M ξ) N + near) := by
                  gcongr
                  rw [← h2]; exact h1
              _ = f N ξ * (rerootAvg^[n] fun M => farInd N r M * f M ξ) N + f N ξ * near := by
                  ring
              _ ≤ f N ξ * (rerootAvg^[n] fun M => farInd N r M * f M ξ) N + near := by
                  gcongr
                  calc f N ξ * near ≤ 1 * near := by gcongr; exact hf1 N ξ
                    _ = near := one_mul _
          refine le_trans (lintegral_mono hstep) ?_
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        · refine lintegral_mono fun ξ => ?_
          gcongr
          exact rerootIter_mono n (fun M => mul_farInd_le N r M (f M ξ)) N
      have hI3eq : I3 + C * C * near = C * C := by
        have hkey : ∀ v : ℕ,
            (fun M => ∫⁻ ξ, f N ξ * (farInd N r M * f M ξ) ∂(RWRS.iidLaw ℕ ν))
                (RWRS.netReroot N v)
              = (fun M => farInd N r M * (C * C)) (RWRS.netReroot N v) := by
          intro v
          simp only []
          by_cases hd : Disjoint (netBallX N r) (netBallX (RWRS.netReroot N v) r)
          · have hfar : farInd N r (RWRS.netReroot N v) = 1 := by simp [farInd, hd]
            rw [hfar, one_mul]
            have hpull : ∀ ξ : ℕ → ℝ,
                f N ξ * (1 * f (RWRS.netReroot N v) ξ) = f N ξ * f (RWRS.netReroot N v) ξ := by
              intro ξ; rw [one_mul]
            rw [lintegral_congr hpull]
            rw [lintegral_ballAvg_mul ν r humeas N v hd, hfint N, hfint (RWRS.netReroot N v),
              markAvg_reroot hre ν hN v, hCN]
          · have hfar : farInd N r (RWRS.netReroot N v) = 0 := by simp [farInd, hd]
            rw [hfar, zero_mul]
            have hz : ∀ ξ : ℕ → ℝ, f N ξ * (0 * f (RWRS.netReroot N v) ξ) = 0 := by
              intro ξ; rw [zero_mul, mul_zero]
            rw [lintegral_congr hz, lintegral_zero]
        have hI3' : I3 = (rerootAvg^[n] fun M => farInd N r M * (C * C)) N := by
          rw [hI3]
          have hconst : ∀ ξ : ℕ → ℝ,
              f N ξ * (rerootAvg^[n] fun M => farInd N r M * f M ξ) N
                = (rerootAvg^[n] fun M => f N ξ * (farInd N r M * f M ξ)) N := by
            intro ξ
            rw [rerootIter_const_mul (f N ξ) n (fun M => farInd N r M * f M ξ) N]
          rw [lintegral_congr hconst,
            lintegral_rerootIter_exchange n (fun M ξ => f N ξ * (farInd N r M * f M ξ))
              (fun M => (hfmeas N).mul (measurable_const.mul (hfmeas M))) N]
          exact rerootIter_congr_reroot n N hkey
        have hsum : (rerootAvg^[n] fun M => farInd N r M * (C * C)) N
            + (rerootAvg^[n] fun M => nearInd N r M * (C * C)) N = C * C := by
          rw [← rerootIter_add n (fun M => farInd N r M * (C * C))
            (fun M => nearInd N r M * (C * C)) N]
          have hone : ∀ M : RWRS.Net 0,
              farInd N r M * (C * C) + nearInd N r M * (C * C) = C * C := by
            intro M
            rw [← add_mul, farInd_add_nearInd, one_mul]
          rw [show (fun M : RWRS.Net 0 => farInd N r M * (C * C) + nearInd N r M * (C * C))
              = fun _ : RWRS.Net 0 => C * C from funext hone]
          exact rerootIter_const (C * C) n N hN
        rw [hI3']
        have hnearmul : (rerootAvg^[n] fun M => nearInd N r M * (C * C)) N = C * C * near := by
          have : (fun M : RWRS.Net 0 => nearInd N r M * (C * C))
              = fun M => C * C * nearInd N r M := funext fun M => mul_comm _ _
          rw [this, rerootIter_const_mul (C * C) n (nearInd N r) N, hnear]
        rw [← hnearmul]
        exact hsum
      have hI3le : I3 ≤ C * C := by
        rw [← hI3eq]; exact le_self_add
      have hCCle : C * C ≤ I3 + near := by
        rw [← hI3eq]
        gcongr
        calc C * C * near ≤ 1 * near := by gcongr
          _ = near := one_mul _
      have hnb : near ≤ nearBound r n N := nearIter_le_nearBound hN r n
      constructor
      · calc markAvg ν u N = I1 := hI1eq.symm
          _ ≤ I2 + b := hI12.1
          _ ≤ (I3 + near) + b := by gcongr; exact hI23.1
          _ ≤ (C * C + near) + b := by gcongr
          _ = C * C + (near + b) := by ring
          _ ≤ C * C + (nearBound r n N + b) := by gcongr
      · calc C * C ≤ I3 + near := hCCle
          _ ≤ I2 + near := by gcongr; exact hI23.2
          _ ≤ (I1 + b) + near := by gcongr; exact hI12.2
          _ = I1 + (near + b) := by ring
          _ = markAvg ν u N + (near + b) := by rw [hI1eq]
          _ ≤ markAvg ν u N + (nearBound r n N + b) := by gcongr
    -- integrate the pointwise estimate
    have hgIter : ∀ n : ℕ, ∫⁻ N, (rerootAvg^[n] g) N ∂Q = ∫⁻ N, g N ∂Q := fun n =>
      lintegral_rerootIter hstat n g hgmeas hginv
    have hstep : ∀ n : ℕ,
        ∫⁻ N, (nearBound r n N + (g N + (rerootAvg^[n] g) N)) ∂Q
          = (∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q := by
      intro n
      rw [lintegral_add_left (measurable_nearBound r n),
        lintegral_add_left hgmeas, hgIter n, two_mul]
    have hupper : ∀ n : ℕ, C ≤ C * C + ((∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q) := by
      intro n
      calc C = ∫⁻ N, markAvg ν u N ∂Q := hCval.symm
        _ ≤ ∫⁻ N, (C * C + (nearBound r n N + (g N + (rerootAvg^[n] g) N))) ∂Q := by
            refine lintegral_mono_ae ?_
            filter_upwards [hpt] with N hN using (hN n).1
        _ = C * C + ∫⁻ N, (nearBound r n N + (g N + (rerootAvg^[n] g) N)) ∂Q := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        _ = C * C + ((∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q) := by rw [hstep n]
    have hlower : ∀ n : ℕ, C * C ≤ C + ((∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q) := by
      intro n
      calc C * C = ∫⁻ _N : RWRS.Net 0, C * C ∂Q := by
            rw [lintegral_const, measure_univ, mul_one]
        _ ≤ ∫⁻ N, (markAvg ν u N + (nearBound r n N + (g N + (rerootAvg^[n] g) N))) ∂Q := by
            refine lintegral_mono_ae ?_
            filter_upwards [hpt] with N hN using (hN n).2
        _ = C + ((∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q) := by
            rw [lintegral_add_left (measurable_markAvg ν humeas), hCval, hstep n]
    -- the near part vanishes along the walk
    have hnear0 : Filter.Tendsto (fun n : ℕ => ∫⁻ N, nearBound r n N ∂Q) Filter.atTop (nhds 0) := by
      have hbound : ∀ n : ℕ, ∀ᵐ N ∂Q, nearBound r n N ≤ 1 := by
        intro n
        filter_upwards [hgood] with N hN
        exact nearBound_le_one hN r n
      have hlim : ∀ᵐ N ∂Q, Filter.Tendsto (fun n : ℕ => nearBound r n N) Filter.atTop (nhds 0) := by
        filter_upwards [hgood] with N hN
        exact tendsto_nearBound hN (hHKV N hN) r
      have := MeasureTheory.tendsto_lintegral_of_dominated_convergence
        (bound := fun _ : RWRS.Net 0 => (1 : ℝ≥0∞))
        (fun n => measurable_nearBound r n) hbound
        (by rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.one_ne_top) hlim
      simpa using this
    have hlimU : Filter.Tendsto
        (fun n : ℕ => C * C + ((∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q))
        Filter.atTop (nhds (C * C + 2 * ∫⁻ N, g N ∂Q)) := by
      have h1 : Filter.Tendsto
          (fun n : ℕ => (∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q)
          Filter.atTop (nhds (2 * ∫⁻ N, g N ∂Q)) := by
        simpa using hnear0.add (tendsto_const_nhds (x := 2 * ∫⁻ N, g N ∂Q))
      simpa using (tendsto_const_nhds (x := C * C)).add h1
    have hlimL : Filter.Tendsto
        (fun n : ℕ => C + ((∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q))
        Filter.atTop (nhds (C + 2 * ∫⁻ N, g N ∂Q)) := by
      have h1 : Filter.Tendsto
          (fun n : ℕ => (∫⁻ N, nearBound r n N ∂Q) + 2 * ∫⁻ N, g N ∂Q)
          Filter.atTop (nhds (2 * ∫⁻ N, g N ∂Q)) := by
        simpa using hnear0.add (tendsto_const_nhds (x := 2 * ∫⁻ N, g N ∂Q))
      simpa using (tendsto_const_nhds (x := C)).add h1
    have h2g : 2 * ∫⁻ N, g N ∂Q ≤ 2 * ε := by gcongr
    constructor
    · calc C ≤ C * C + 2 * ∫⁻ N, g N ∂Q := ge_of_tendsto' hlimU hupper
        _ ≤ C * C + 2 * ε := by gcongr
    · calc C * C ≤ C + 2 * ∫⁻ N, g N ∂Q := ge_of_tendsto' hlimL hlower
        _ ≤ C + 2 * ε := by gcongr
  -- let the accuracy go to zero
  have hhalf : ∀ δ : ℝ≥0, 0 < δ → (2 : ℝ≥0∞) * ((δ : ℝ≥0∞) / 2) = (δ : ℝ≥0∞) := by
    intro δ _
    rw [mul_comm, ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]
  refine le_antisymm ?_ ?_
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have h := (hmain ((δ : ℝ≥0∞) / 2)
      (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hδ.ne'))).1
    rwa [hhalf δ hδ] at h
  · refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have h := (hmain ((δ : ℝ≥0∞) / 2)
      (ENNReal.half_pos (ENNReal.coe_ne_zero.mpr hδ.ne'))).2
    rwa [hhalf δ hδ] at h

end RWRS.Support
