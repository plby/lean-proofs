import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardComparison
import Mathlib.Topology.Sheaves.Over
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Actual extension from an open subspace preserves monomorphisms

The left Kan extension along the actual inclusion of open sets has two
literal cases: on an open contained in the subspace it is the original
presheaf value, and otherwise its indexing category is empty. In abelian
groups the latter value is zero. This proves preservation of
monomorphisms before sheafification, without a sheaf-cohomology premise.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenRestriction

variable {X : TopCat.{0}} (U : Opens X)

/-- The actual open-subspace inclusion. -/
def inclusion : TopCat.of U ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem inclusion_isOpenEmbedding : Topology.IsOpenEmbedding (inclusion U) :=
  U.isOpenEmbedding

instance inclusion_mono : Mono (inclusion U) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- Direct images of actual open sets along the open inclusion. -/
abbrev openImage : Opens U ⥤ Opens X := (inclusion_isOpenEmbedding U).functor

instance openImage_full : (openImage U).Full :=
  @IsOpenMap.functorFullOfMono (TopCat.of U) X (inclusion U)
    (inclusion_isOpenEmbedding U).isOpenMap (inclusion_mono U)

/-- Actual preimages of ambient open sets. -/
abbrev preimageOpen (V : Opens X) : Opens U := (Opens.map (inclusion U)).obj V

theorem openImage_obj_le (V : Opens U) : (openImage U).obj V ≤ U := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

theorem openImage_preimage {V : Opens X} (hV : V ≤ U) :
    (openImage U).obj (preimageOpen U V) = V := by
  apply Opens.ext
  change (inclusion U) '' ((inclusion U) ⁻¹' (V : Set X)) = (V : Set X)
  apply Set.image_preimage_eq_of_subset
  intro x hx
  exact ⟨⟨x, hV hx⟩, rfl⟩

/-- Outside the actual open subspace, the pointwise extension diagram
is genuinely empty. -/
theorem costructuredArrow_isEmpty (V : Opens X) (hV : ¬ V ≤ U) :
    IsEmpty (CostructuredArrow (openImage U).op (op V)) :=
  ⟨fun a => hV (a.hom.unop.le.trans (openImage_obj_le U a.left.unop))⟩

/-- The actual left Kan extension is zero off the opens contained in U. -/
theorem lan_obj_isZero_of_not_le (F : (Opens U)ᵒᵖ ⥤ AddCommGrpCat)
    (V : Opens X) (hV : ¬ V ≤ U) :
    IsZero (((openImage U).op.lan.obj F).obj (op V)) := by
  let := costructuredArrow_isEmpty U V hV
  let D := CostructuredArrow.proj (openImage U).op (op V) ⋙ F
  have hz : IsZero (colimit D) :=
    ((isColimitEquivIsInitialOfIsEmpty AddCommGrpCat (colimit.cocone D))
      (colimit.isColimit D)).isZero
  exact hz.of_iso ((openImage U).op.leftKanExtensionObjIsoColimit F (op V))

/-- Actual open extension of presheaves of abelian groups preserves
monomorphisms: on the image this follows from the genuine Kan unit
isomorphism, and off the image from the zero calculation above. -/
instance lan_preservesMonomorphisms :
    ((openImage U).op.lan : ((Opens U)ᵒᵖ ⥤ AddCommGrpCat) ⥤
      ((Opens X)ᵒᵖ ⥤ AddCommGrpCat)).PreservesMonomorphisms where
  preserves {F G} f _ := by
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro V
    by_cases hV : V.unop ≤ U
    · let W := op (preimageOpen U V.unop)
      have hv : (openImage U).op.obj W = V :=
        congrArg op (openImage_preimage U hV)
      rw [← hv]
      let ηF := ((openImage U).op.lanUnit.app F).app W
      let ηG := ((openImage U).op.lanUnit.app G).app W
      have : IsIso ηF := by dsimp [ηF]; infer_instance
      have : IsIso ηG := by dsimp [ηG]; infer_instance
      have he : ((openImage U).op.lan.map f).app ((openImage U).op.obj W) =
          inv ηF ≫ f.app W ≫ ηG := by
        apply (cancel_epi ηF).mp
        rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
        exact (NatTrans.congr_app ((openImage U).op.lanUnit.naturality f) W).symm
      rw [he]
      infer_instance
    · exact (lan_obj_isZero_of_not_le U F V.unop hV).mono _

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenRestriction
