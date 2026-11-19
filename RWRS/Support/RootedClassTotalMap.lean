import RWRS.Support.RootedClassLaw

/-!
# A total class map

Choosing a connected network supplies a measurable total map from all network
codes to rooted classes. On a law supported on connected codes, its pushforward
is the rooted-class law.
-/

namespace RWRS.Support

open MeasureTheory Function

/-- Map connected codes to their rooted class and all other codes to a fixed class. -/
noncomputable def goodNetClassTotal (N₀ : GoodNet) : Net 0 → RootedBallClass :=
  Function.extend (Subtype.val : GoodNet → Net 0) goodNetClass (fun _ => goodNetClass N₀)

/-- The total class map agrees with the class map on connected codes. -/
theorem goodNetClassTotal_of_good (N₀ N : GoodNet) :
    goodNetClassTotal N₀ N.1 = goodNetClass N := by
  exact Subtype.val_injective.extend_apply goodNetClass (fun _ => goodNetClass N₀) N

/-- The total class map is measurable. -/
theorem measurable_goodNetClassTotal (N₀ : GoodNet) : Measurable (goodNetClassTotal N₀) :=
  (MeasurableEmbedding.subtype_coe measurableSet_netGood).measurable_extend
    measurable_goodNetClass measurable_const

/-- A supported network law pushes forward along the total map to its class law. -/
theorem goodNetClassLaw_eq_map_total (N₀ : GoodNet) (Q : Measure (Net 0))
    (hgood : ∀ᵐ N ∂Q, NetGood N) : goodNetClassLaw Q = Q.map (goodNetClassTotal N₀) := by
  have hQ : Q.restrict {N : Net 0 | NetGood N} = Q := Measure.restrict_eq_self_of_ae_mem hgood
  unfold goodNetClassLaw
  conv_rhs => rw [← hQ, ← map_comap_subtype_coe measurableSet_netGood,
    Measure.map_map (measurable_goodNetClassTotal N₀) measurable_subtype_coe]
  congr 1
  funext N
  exact (goodNetClassTotal_of_good N₀ N).symm

end RWRS.Support
