import Wikipedia.HopfProblem.DegreeCollapseIntegralConnectingAbsolute

/-!
# Original absolute integral cochains from the small-relative quotient

The original small-relative cochain restricts to a relative cochain on
each piece. Both have exactly the same absolute integral cochain, so
that cochain vanishes on both original subspace-chain images. All maps
are precomposition by the actual quotient and comparison maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.SmallRelativeIntegralCochains

open SingularMayerVietoris SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] (A B : Set X)

abbrev complex := (IntegralRelativeCohomologyMayerVietoris.smallSequence A B).X₁

abbrev Cochain (p : ℕ) := (complex A B).X p

def toAbsoluteMap : complex A B ⟶ singularCochainComplex X :=
  dualMap (RelativeCoefficients.smallRelativeProjection (ModuleCat.of ℤ ℤ) A B)

abbrev toAbsolute (p : ℕ) : Cochain A B p →ₗ[ℤ] SingularCohomologyCup.Cochain X p :=
  ((toAbsoluteMap A B).f p).hom

abbrev coboundary {p : ℕ} (α : Cochain A B p) : Cochain A B (p + 1) :=
  ((complex A B).d p (p + 1)).hom α

theorem toAbsolute_coboundary (p : ℕ) (α : Cochain A B p) :
    toAbsolute A B (p + 1) (coboundary A B α) =
      SingularCohomologyCup.coboundary (toAbsolute A B p α) :=
  (congrArg (fun m => m.hom α) ((toAbsoluteMap A B).comm p (p + 1))).symm

theorem toAbsolute_left (p : ℕ) (α : Cochain A B p) :
    RelativeIntegralCap.toAbsolute A p
        (((IntegralRelativeCohomologyMayerVietoris.smallRestrictionLeft A B).f p).hom α) =
      toAbsolute A B p α := by
  have he : IntegralRelativeCohomologyMayerVietoris.smallRestrictionLeft A B ≫
      RelativeIntegralCap.toAbsoluteMap A = toAbsoluteMap A B :=
    (dualMap_comp (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) A)
      (RelativeMayerVietoris.toSmallLeft (ModuleCat.of ℤ ℤ) A B)).symm.trans
        (congrArg dualMap (RelativeMayerVietoris.projection_toSmallLeft _ A B))
  exact congrArg (fun m => (m.f p).hom α) he

theorem toAbsolute_right (p : ℕ) (α : Cochain A B p) :
    RelativeIntegralCap.toAbsolute B p
        (((IntegralRelativeCohomologyMayerVietoris.smallRestrictionRight A B).f p).hom α) =
      toAbsolute A B p α := by
  have he : IntegralRelativeCohomologyMayerVietoris.smallRestrictionRight A B ≫
      RelativeIntegralCap.toAbsoluteMap B = toAbsoluteMap A B :=
    (dualMap_comp (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) B)
      (RelativeMayerVietoris.toSmallRight (ModuleCat.of ℤ ℤ) A B)).symm.trans
        (congrArg dualMap (RelativeMayerVietoris.projection_toSmallRight _ A B))
  exact congrArg (fun m => (m.f p).hom α) he

theorem pullback_toAbsolute_left (p : ℕ) (α : Cochain A B p) :
    SingularCohomologyCup.pullback (subtypeInclusion A) p (toAbsolute A B p α) = 0 :=
  (congrArg (SingularCohomologyCup.pullback (subtypeInclusion A) p)
    (toAbsolute_left A B p α).symm).trans (RelativeIntegralCap.pullback_toAbsolute A p _)

theorem pullback_toAbsolute_right (p : ℕ) (α : Cochain A B p) :
    SingularCohomologyCup.pullback (subtypeInclusion B) p (toAbsolute A B p α) = 0 :=
  (congrArg (SingularCohomologyCup.pullback (subtypeInclusion B) p)
    (toAbsolute_right A B p α).symm).trans (RelativeIntegralCap.pullback_toAbsolute B p _)

/-- The original union-relative pullback retains its exact absolute integral cochain. -/
theorem toAbsolute_union (p : ℕ) (α : RelativeIntegralCap.Cochain (A ∪ B) p) :
    toAbsolute A B p (((dualMap
      (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)).f p).hom α) =
        RelativeIntegralCap.toAbsolute (A ∪ B) p α := by
  have he : dualMap
      (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B) ≫ toAbsoluteMap A B =
        RelativeIntegralCap.toAbsoluteMap (A ∪ B) :=
    (dualMap_comp (RelativeCoefficients.smallRelativeProjection (ModuleCat.of ℤ ℤ) A B)
      (RelativeCoefficients.smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B)).symm.trans
        (congrArg dualMap
          (RelativeCoefficients.projection_smallToUnionQuotient (ModuleCat.of ℤ ℤ) A B))
  exact congrArg (fun m => (m.f p).hom α) he

end Wikipedia.HopfProblem.DegreeCollapse.SmallRelativeIntegralCochains
