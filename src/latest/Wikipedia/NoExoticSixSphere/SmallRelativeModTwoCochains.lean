import Wikipedia.NoExoticSixSphere.RelativeModTwoConnectingAbsolute

/-!
# Absolute cochains from the actual small-relative quotient

The original small-relative cochain restricts to an actual relative
cochain for each piece. Both have the same absolute cochain, which
therefore vanishes on both original subspace-chain images. All maps
are precomposition with the original quotient and comparison maps.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SmallRelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (A B : Set X)

abbrev complex := (RelativeModTwoMayerVietoris.smallSequence A B).X₁

abbrev Cochain (p : ℕ) := (complex A B).X p

/-- Precomposition by the original small-relative quotient. -/
def toAbsoluteMap : complex A B ⟶ ModTwoCapProduct.cochainComplex X :=
  ModTwoDualComplex.map (RelativeCoefficients.smallRelativeProjection (ModuleCat.of ℤ ℤ) A B)

abbrev toAbsolute (p : ℕ) : Cochain A B p →ₗ[ℤ] ModTwoCapProduct.Cochain X p :=
  ((toAbsoluteMap A B).f p).hom

abbrev coboundary {p : ℕ} (α : Cochain A B p) : Cochain A B (p + 1) :=
  ((complex A B).d p (p + 1)).hom α

theorem toAbsolute_coboundary (p : ℕ) (α : Cochain A B p) :
    toAbsolute A B (p + 1) (coboundary A B α) =
      ModTwoCapProduct.coboundary (toAbsolute A B p α) :=
  (congrArg (fun m => m.hom α) ((toAbsoluteMap A B).comm p (p + 1))).symm

/-- Restriction to the left quotient preserves the original absolute cochain. -/
theorem toAbsolute_left (p : ℕ) (α : Cochain A B p) :
    RelativeModTwoCochains.toAbsolute A p
        (((RelativeModTwoMayerVietoris.smallRestrictionLeft A B).f p).hom α) =
      toAbsolute A B p α := by
  have he : RelativeModTwoMayerVietoris.smallRestrictionLeft A B ≫
      RelativeModTwoCochains.toAbsoluteMap A = toAbsoluteMap A B :=
    (ModTwoDualComplex.map_comp (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) A)
      (RelativeMayerVietoris.toSmallLeft (ModuleCat.of ℤ ℤ) A B)).symm.trans
        (congrArg ModTwoDualComplex.map (RelativeMayerVietoris.projection_toSmallLeft _ A B))
  exact congrArg (fun m => (m.f p).hom α) he

/-- Restriction to the right quotient preserves the same original absolute cochain. -/
theorem toAbsolute_right (p : ℕ) (α : Cochain A B p) :
    RelativeModTwoCochains.toAbsolute B p
        (((RelativeModTwoMayerVietoris.smallRestrictionRight A B).f p).hom α) =
      toAbsolute A B p α := by
  have he : RelativeModTwoMayerVietoris.smallRestrictionRight A B ≫
      RelativeModTwoCochains.toAbsoluteMap B = toAbsoluteMap A B :=
    (ModTwoDualComplex.map_comp (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) B)
      (RelativeMayerVietoris.toSmallRight (ModuleCat.of ℤ ℤ) A B)).symm.trans
        (congrArg ModTwoDualComplex.map (RelativeMayerVietoris.projection_toSmallRight _ A B))
  exact congrArg (fun m => (m.f p).hom α) he

theorem pullback_toAbsolute_left (p : ℕ) (α : Cochain A B p) :
    ModTwoCapProduct.pullback (subtypeInclusion A) p (toAbsolute A B p α) = 0 :=
  (congrArg (ModTwoCapProduct.pullback (subtypeInclusion A) p)
    (toAbsolute_left A B p α).symm).trans (RelativeModTwoCochains.pullback_toAbsolute A p _)

theorem pullback_toAbsolute_right (p : ℕ) (α : Cochain A B p) :
    ModTwoCapProduct.pullback (subtypeInclusion B) p (toAbsolute A B p α) = 0 :=
  (congrArg (ModTwoCapProduct.pullback (subtypeInclusion B) p)
    (toAbsolute_right A B p α).symm).trans (RelativeModTwoCochains.pullback_toAbsolute B p _)

/-- Pullback from the actual union-relative quotient retains the original absolute cochain. -/
theorem toAbsolute_union (p : ℕ) (α : RelativeModTwoCochains.Cochain (A ∪ B) p) :
    toAbsolute A B p (((ModTwoDualComplex.map
      (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)).f p).hom α) =
        RelativeModTwoCochains.toAbsolute (A ∪ B) p α := by
  have he : ModTwoDualComplex.map
      (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B) ≫ toAbsoluteMap A B =
        RelativeModTwoCochains.toAbsoluteMap (A ∪ B) :=
    (ModTwoDualComplex.map_comp
      (RelativeCoefficients.smallRelativeProjection (ModuleCat.of ℤ ℤ) A B)
      (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)).symm.trans
        (congrArg ModTwoDualComplex.map
          (RelativeCoefficients.projection_smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B))
  exact congrArg (fun m => (m.f p).hom α) he

end NoExoticSixSphere.SmallRelativeModTwoCochains
