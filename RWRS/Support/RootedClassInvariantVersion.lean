import RWRS.Support.RootedClassReach

/-!
# Invariant versions of class observables

An observable that is constant across every edge outside a stationary null set
has an almost-everywhere equal rerooting-invariant measurable version.
-/

namespace RWRS.Support

open MeasureTheory ProbabilityTheory

/-- Rerooting at the existing root leaves a connected network unchanged. -/
theorem goodNetReroot_root (N : GoodNet) : goodNetReroot N (netRoot N.1) = N := by
  apply Subtype.ext
  cases N with
  | mk N hN => cases N with | mk a b => cases b; rfl

/-- Every class event is contained in its rerooting saturation. -/
theorem subset_rootedClassSaturation (D : Set RootedBallClass) :
    D ⊆ rootedClassSaturation D := by
  intro c hc
  let N := goodNetClassRepresentative c
  have h : goodNetClass N ∈ rootedClassSaturation D := by
    apply (mem_rootedClassSaturation_iff D N).2
    exact ⟨netRoot N.1, by rw [goodNetReroot_root, goodNetClass_representative]; exact hc⟩
  rwa [goodNetClass_representative] at h

/-- A measurable class observable unchanged by rerooting is invariant-sigma measurable. -/
theorem measurable_rootedClassInvariantSigma {f : RootedBallClass → ℝ}
    (hf : Measurable f)
    (hre : ∀ (N : GoodNet) (y : ℕ), f (goodNetClass N) = f (goodNetClass (goodNetReroot N y))) :
    Measurable[rootedClassInvariantSigma] f := by
  intro S hS
  refine ⟨hf hS, ?_⟩
  intro N y
  change f (goodNetClass N) ∈ S ↔ f (goodNetClass (goodNetReroot N y)) ∈ S
  rw [hre N y]

/-- A measurable observable constant across edges off a null set has an invariant version. -/
theorem exists_invariant_version_of_ae_edge_eq (ν : Measure RootedBallClass)
    (hstat : classRerootKernel ∘ₘ ν = ν) {f : RootedBallClass → ℝ}
    (hf : Measurable f) {E : Set RootedBallClass} (hE : MeasurableSet E) (hzero : ν E = 0)
    (hedge : ∀ (N : GoodNet), goodNetClass N ∉ E → ∀ y,
      (netGraph N.1).Adj (netRoot N.1) y →
      f (goodNetClass N) = f (goodNetClass (goodNetReroot N y))) :
    ∃ g : RootedBallClass → ℝ, Measurable[rootedClassInvariantSigma] g ∧ f =ᵐ[ν] g := by
  classical
  let S := rootedClassSaturation E
  let g : RootedBallClass → ℝ := S.indicator (fun _ => 0) + Sᶜ.indicator f
  have hS : MeasurableSet[rootedClassInvariantSigma] S :=
    measurableSet_rootedClassSaturation_invariantSigma hE
  have hnull : ν S = 0 := measure_rootedClassSaturation_eq_zero ν hstat hE hzero
  have hg (c : RootedBallClass) : g c = if c ∈ S then 0 else f c := by
    by_cases hc : c ∈ S <;> simp [g, hc]
  have hmeas : Measurable g := (measurable_const.indicator hS.1).add (hf.indicator hS.1.compl)
  have hre : ∀ (N : GoodNet) (y : ℕ), g (goodNetClass N) = g (goodNetClass (goodNetReroot N y)) := by
    intro N y
    have hs : goodNetClass N ∈ S ↔ goodNetClass (goodNetReroot N y) ∈ S := hS.2 N y
    by_cases hN : goodNetClass N ∈ S
    · rw [hg, hg, if_pos hN, if_pos (hs.1 hN)]
    · have hn (v : ℕ) : goodNetClass (goodNetReroot N v) ∉ S :=
        fun hv => hN ((hS.2 N v).2 hv)
      have hwalk : ∀ {u v : ℕ} (p : (netGraph N.1).Walk u v),
          f (goodNetClass (goodNetReroot N u)) = f (goodNetClass (goodNetReroot N v)) := by
        intro u v p
        induction p with
        | nil => rfl
        | @cons u w v huw p ih =>
            have he : goodNetClass (goodNetReroot N u) ∉ E :=
              fun he => hn u (subset_rootedClassSaturation E he)
            exact (hedge (goodNetReroot N u) he w huw).trans ih
      obtain ⟨p⟩ := N.2.preconnected (netRoot N.1) y
      have h := hwalk p
      rw [goodNetReroot_root] at h
      rw [hg, hg, if_neg hN, if_neg (fun h => hN (hs.2 h))]
      exact h
  refine ⟨g, measurable_rootedClassInvariantSigma hmeas hre, ?_⟩
  have hae : ∀ᵐ c ∂ν, c ∉ S := measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with c hc
  rw [hg, if_neg hc]

end RWRS.Support
