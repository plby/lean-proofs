import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafRaw
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalPatchBasic

/-!
# Native global-cochain compatibility and pullback functoriality

Raw presheaf pullback commutes with restriction of the original global
singular cochains. Identity and composition use the actual continuous
preimage maps and Mathlib's original presheaf pushforward identifications.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

open FirstHurewicz

variable {X Y Z : TopCat.{0}} (f : X ⟶ Y)

/-- Including the image of the preimage-to-open map in the ambient space
recovers the original continuous map after the original open inclusion. -/
theorem preimageMap_inclusion (U : Opens Y) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, Y)).comp (preimageMap f U) =
      f.hom.comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C((Opens.map f).obj U, X)) := by
  ext x
  rfl

variable (A : AddCommGrpCat.{0}) (n : ℕ)

/-- Restricting an original global cochain and then applying the raw
presheaf pullback is the restriction of its native singular pullback. -/
theorem rawPullback_restrictGlobal (φ : Cochains Y A n) (U : Opens Y) :
    (rawPullback f A n).app (op U) (restrictGlobalCochain A n φ U) =
      restrictGlobalCochain A n ((singularPullback A f.hom).f n φ)
        ((Opens.map f).obj U) := by
  have h :
      singularPullback A (⟨Subtype.val, continuous_subtype_val⟩ : C(U, Y)) ≫
          singularPullback A (preimageMap f U) =
        singularPullback A f.hom ≫
          singularPullback A
            (⟨Subtype.val, continuous_subtype_val⟩ : C((Opens.map f).obj U, X)) :=
    (singularPullback_comp A (preimageMap f U)
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, Y))).symm.trans
      ((congrArg (singularPullback A) (preimageMap_inclusion f U)).trans
        (singularPullback_comp A
          (⟨Subtype.val, continuous_subtype_val⟩ : C((Opens.map f).obj U, X)) f.hom))
  exact congrArg
    (fun g : singularCochainComplex Y A ⟶
        singularCochainComplex ((Opens.map f).obj U) A => (g.f n).hom φ) h

/-- The same compatibility on the genuine top open sets. The actual
preimage of the top open set is definitionally the top open set. -/
theorem rawPullback_restrictGlobal_top (φ : Cochains Y A n) :
    (rawPullback f A n).app (op ⊤) (restrictGlobalCochain A n φ ⊤) =
      restrictGlobalCochain A n ((singularPullback A f.hom).f n φ) (⊤ : Opens X) :=
  rawPullback_restrictGlobal f A n φ ⊤

/-- The actual preimage-to-open map for the identity is the identity
of the original open subspace. -/
@[simp] theorem preimageMap_id (U : Opens X) :
    preimageMap (𝟙 X) U = ContinuousMap.id U := by
  ext x
  rfl

/-- Native raw pullback by the identity is the identity natural
transformation, under the original definitional pushforward identification. -/
@[simp] theorem rawPullback_id :
    rawPullback (𝟙 X) A n = 𝟙 (cochainPresheaf X A n) := by
  apply NatTrans.ext
  funext U
  exact congrArg (fun k => k.f n)
    ((congrArg (singularPullback A) (preimageMap_id U.unop)).trans
      (singularPullback_id A U.unop))

/-- The actual preimage-to-open map for a composite is the composite
of the two actual preimage-to-open maps. -/
@[simp] theorem preimageMap_comp (g : Y ⟶ Z) (U : Opens Z) :
    preimageMap (f ≫ g) U =
      (preimageMap g U).comp (preimageMap f ((Opens.map g).obj U)) := by
  ext x
  rfl

/-- Native raw presheaf pullbacks compose contravariantly. Mathlib's
actual composite-pushforward identification is definitionally the identity. -/
theorem rawPullback_comp (g : Y ⟶ Z) :
    rawPullback (f ≫ g) A n =
      rawPullback g A n ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map (rawPullback f A n) := by
  apply NatTrans.ext
  funext U
  exact congrArg (fun k => k.f n)
    ((congrArg (singularPullback A) (preimageMap_comp f g U.unop)).trans
      (singularPullback_comp A (preimageMap f ((Opens.map g).obj U.unop))
        (preimageMap g U.unop)))

/-- The identity law also holds with Mathlib's explicit native
identity-pushforward isomorphism. -/
theorem rawPullback_id_iso :
    rawPullback (𝟙 X) A n =
      (TopCat.Presheaf.Pushforward.id (cochainPresheaf X A n)).inv :=
  rawPullback_id A n

/-- Composition with the homomorphism of Mathlib's actual
composite-pushforward isomorphism gives the same pullback composite. -/
theorem rawPullback_comp_iso (g : Y ⟶ Z) :
    rawPullback (f ≫ g) A n ≫
        (TopCat.Presheaf.Pushforward.comp f g (cochainPresheaf X A n)).hom =
      rawPullback g A n ≫
        (TopCat.Presheaf.pushforward AddCommGrpCat.{0} g).map (rawPullback f A n) := by
  change rawPullback (f ≫ g) A n ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact rawPullback_comp f A n g

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
