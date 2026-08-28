import Wikipedia.NoExoticSixSphere.SingularSmallSubcomplex

/-!
# Restricting actual singular subcomplexes to a subspace

Pullback of geometric simplex support is geometric support in the actual
subspace. A subcomplex contained in the range of a monomorphism is
isomorphic to its preimage, by the original preimage map.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.SimplicialCoefficients

/-- The original preimage map is an isomorphism when the subcomplex lies in a monic map's range. -/
theorem fromPreimage_isIso {X Y : SSet.{0}} (B : X.Subcomplex) (f : Y ⟶ X) [Mono f]
    (hB : B ≤ SSet.Subcomplex.range f) : IsIso (B.fromPreimage f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  have hf : Function.Injective (f.app n) := (mono_iff_injective _).mp inferInstance
  constructor
  · intro s t hst
    apply Subtype.ext
    apply hf
    exact congrArg Subtype.val hst
  · intro s
    obtain ⟨t, ht⟩ := hB n s.property
    have htB : t ∈ (B.preimage f).obj n := by
      change f.app n t ∈ B.obj n
      exact ht.symm ▸ s.property
    exact ⟨⟨t, htB⟩, Subtype.ext ht⟩

end NoExoticSixSphere.SimplicialCoefficients

namespace NoExoticSixSphere.SingularSubcomplex

variable {X : Type} [TopologicalSpace X]

/-- Geometric support pulls back to the actual support in the original subspace. -/
theorem support_preimage (U W : Set X) :
    (support U).preimage (inclusion W) = support (Subtype.val ⁻¹' U : Set W) := by
  apply Subfunctor.ext
  funext n
  ext s
  change (inclusion W).app n s ∈ (support U).obj n ↔
    s ∈ (support (Subtype.val ⁻¹' U : Set W)).obj n
  rw [mem_support_iff, mem_support_iff, simplexMap_naturality]
  constructor
  · intro h z hz
    obtain ⟨p, rfl⟩ := hz
    exact h ⟨p, rfl⟩
  · intro h z hz
    obtain ⟨p, rfl⟩ := hz
    exact h ⟨p, rfl⟩

theorem small_preimage (U V W : Set X) :
    (support U ⊔ support V).preimage (inclusion W) =
      support (Subtype.val ⁻¹' U : Set W) ⊔ support (Subtype.val ⁻¹' V : Set W) := by
  rw [SSet.Subcomplex.preimage_max, support_preimage, support_preimage]

/-- The inclusion of the small-simplex subcomplex into the singular range of the union. -/
theorem small_le_union (U V : Set X) : support U ⊔ support V ≤ support (U ∪ V) :=
  sup_le (support_mono Set.subset_union_left) (support_mono Set.subset_union_right)

/-- The actual small-simplex map into the singular set of the topological union. -/
def smallToUnion (U V : Set X) : Small U V ⟶ singular (U ∪ V : Set X) :=
  SSet.Subcomplex.homOfLE (small_le_union U V) ≫ (supportIso (U ∪ V)).inv

@[reassoc]
theorem smallToUnion_inclusion (U V : Set X) :
    smallToUnion U V ≫ inclusion (U ∪ V) = smallInclusion U V := by
  change (SSet.Subcomplex.homOfLE (small_le_union U V) ≫ (supportIso (U ∪ V)).inv) ≫ _ = _
  rw [Category.assoc, ← supportIso_hom_inclusion (U ∪ V), Iso.inv_hom_id_assoc,
    SSet.Subcomplex.homOfLE_ι]

/-- The canonical identification of small simplices formed inside or outside the actual union. -/
def smallUnionIso (U V : Set X) :
    Small (Subtype.val ⁻¹' U : Set (U ∪ V : Set X))
      (Subtype.val ⁻¹' V : Set (U ∪ V : Set X)) ≅ Small U V := by
  let B := support U ⊔ support V
  let f := inclusion (U ∪ V)
  have : IsIso (B.fromPreimage f) :=
    SimplicialCoefficients.fromPreimage_isIso B f (small_le_union U V)
  exact SSet.Subcomplex.eqToIso (small_preimage U V (U ∪ V)).symm ≪≫ asIso (B.fromPreimage f)

@[reassoc]
theorem smallUnionIso_inclusion (U V : Set X) :
    (smallUnionIso U V).hom ≫ smallInclusion U V =
      smallInclusion (Subtype.val ⁻¹' U : Set (U ∪ V : Set X))
        (Subtype.val ⁻¹' V : Set (U ∪ V : Set X)) ≫
        inclusion (U ∪ V) := rfl

/-- Before the ambient inclusion, the original union comparison is already the same map. -/
theorem smallUnionIso_toUnion (U V : Set X) :
    (smallUnionIso U V).hom ≫ smallToUnion U V =
      smallInclusion (Subtype.val ⁻¹' U : Set (U ∪ V : Set X))
        (Subtype.val ⁻¹' V : Set (U ∪ V : Set X)) := by
  apply (cancel_mono (inclusion (U ∪ V))).mp
  rw [Category.assoc, smallToUnion_inclusion, smallUnionIso_inclusion]

end NoExoticSixSphere.SingularSubcomplex
