import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsSpecial
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticRestrictionHolomorphic

/-!
# Restricting the genuine elliptic canonical sections

The constructed full-filling section restricts to the actual small open
piece by differential pullback.  Holomorphicity is proved using the
already constructed biholomorphism of the original canonical bundle
total spaces.  Its zero set is unchanged by this genuine fibre equivalence.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

/-- The actual restricted ambient canonical section. -/
def smallSection (j : Kind) (x : SpecialEllipticPiece j) : (Elliptic.bundle j).Fiber x :=
  Elliptic.restriction j x (fullSection j x.val)

def smallSectionMap (j : Kind) (x : SpecialEllipticPiece j) : (Elliptic.bundle j).TotalSpace :=
  ⟨x, smallSection j x⟩

@[simp] theorem smallSectionMap_proj (j : Kind) (x : SpecialEllipticPiece j) :
    (smallSectionMap j x).proj = x := rfl

/-- The full section lies in the literal natural restriction of the
original full bundle, with the original open-submanifold atlas. -/
def fullSectionOnPiece (j : Kind) (x : SpecialEllipticPiece j) :
    Elliptic.fullBundleRestriction j := ⟨fullSectionMap j x.val, x.property⟩

@[simp] theorem fullSectionOnPiece_val (j : Kind) (x : SpecialEllipticPiece j) :
    (fullSectionOnPiece j x : (Elliptic.fullBundle j).TotalSpace) =
      fullSectionMap j x.val := rfl

theorem fullSectionOnPiece_holomorphic (j : Kind) :
    ContMDiff IF Iᴷ ω (fullSectionOnPiece j) := by
  have h : ContMDiff IF Iᴷ ω (fun x : SpecialEllipticPiece j => fullSectionMap j x.val) :=
    (fullSectionMap_holomorphic j).comp (Elliptic.pieceInclusion_holomorphic j)
  intro x
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (fullSectionOnPiece j) Set.univ x).mp (h x)

/-- The restriction agrees with the explicit inverse bundle comparison. -/
theorem smallSectionMap_eq_restriction (j : Kind) :
    smallSectionMap j = Elliptic.restrictionTotalPullback j ∘ fullSectionOnPiece j := rfl

theorem smallSectionMap_holomorphic (j : Kind) :
    ContMDiff IF Iᴷ ω (smallSectionMap j) := by
  rw [smallSectionMap_eq_restriction]
  exact (Elliptic.restrictionTotalPullback_holomorphic j).comp
    (fullSectionOnPiece_holomorphic j)

def smallHolomorphicSection (j : Kind) :
    ContMDiffSection IF ℂ ω (Elliptic.bundle j).Fiber where
  toFun := smallSection j
  contMDiff_toFun := smallSectionMap_holomorphic j

@[simp] theorem smallHolomorphicSection_apply (j : Kind) (x : SpecialEllipticPiece j) :
    smallHolomorphicSection j x = smallSection j x := rfl

/-- Exact compatibility with the actual full-to-small bundle biholomorphism. -/
theorem restrictionBundleBiholomorph_smallSection (j : Kind) (x : SpecialEllipticPiece j) :
    Elliptic.restrictionBundleBiholomorph j (smallSectionMap j x) = fullSectionOnPiece j x := by
  apply Subtype.ext
  change (⟨x.val, (Elliptic.restriction j x).symm
    (Elliptic.restriction j x (fullSection j x.val))⟩ : (Elliptic.fullBundle j).TotalSpace) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-- The restriction is actual pullback on intrinsic ambient three-covectors. -/
theorem smallSection_intrinsic (j : Kind) (x : SpecialEllipticPiece j) :
    Elliptic.intrinsicEquiv j x (smallSection j x) =
      (Elliptic.fullIntrinsicEquiv j x.val (fullSection j x.val)).compContinuousLinearMap
        (mfderiv IF IF (Elliptic.pieceInclusion j) x) :=
  Elliptic.intrinsic_restriction j x (fullSection j x.val)

theorem smallSection_inCoordinates (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    Elliptic.inCoordinates j (achart Model a) x (smallSection j x) =
      Elliptic.fullInCoordinates j (achart Model a.val) x.val (fullSection j x.val) :=
  Elliptic.restriction_inCoordinates_native j a x hx (fullSection j x.val)

theorem smallSection_eq_zero_iff_full (j : Kind) (x : SpecialEllipticPiece j) :
    smallSection j x = 0 ↔ fullSection j x.val = 0 :=
  (Elliptic.restriction j x).map_eq_zero_iff

theorem smallSection_eq_zero_iff (j : Kind) (x : SpecialEllipticPiece j) :
    smallSection j x = 0 ↔ SectionsUnit.vanishingOrder j ≠ 0 ∧
      specialFullFillingProjection j x.val = Wikipedia.HopfProblem.Elliptic.discZero :=
  (smallSection_eq_zero_iff_full j x).trans (fullSection_eq_zero_iff j x.val)

theorem smallSection_ne_zero_iff (j : Kind) (x : SpecialEllipticPiece j) :
    smallSection j x ≠ 0 ↔ SectionsUnit.vanishingOrder j = 0 ∨
      specialFullFillingProjection j x.val ≠ Wikipedia.HopfProblem.Elliptic.discZero :=
  (not_congr (smallSection_eq_zero_iff_full j x)).trans (fullSection_ne_zero_iff j x.val)

theorem smallSection_three_ne_zero (x : SpecialEllipticPiece .three) :
    smallSection .three x ≠ 0 :=
  (smallSection_ne_zero_iff .three x).mpr (Or.inl rfl)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
