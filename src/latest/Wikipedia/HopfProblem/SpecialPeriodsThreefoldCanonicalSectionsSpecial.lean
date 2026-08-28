import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsFiniteQuotient
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalElliptic

/-!
# Canonical sections on the actual special elliptic fillings

The unconditional special period map and the specified main twists
instantiate the actual finite-quotient construction.  The resulting
sections belong to the original ambient canonical bundles of the full
elliptic fillings, with their native quotient charts.  Their genuine
differential pullbacks recover the explicitly corrected upstairs volume.
The first section is nowhere zero; the second vanishes precisely on the
central surface.  Vanishing orders are addressed separately.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical
open Wikipedia.HopfProblem.Elliptic.Equivariant.Data

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace

local instance specialUpstairsChartedSpace (j : Kind) :
    ChartedSpace Model (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalChartedSpace

local instance specialUpstairsManifold (j : Kind) :
    IsManifold I₃ ω (specialLocalData j).TotalSpace :=
  (specialLocalData j).periods.totalSpace_isManifold

local instance specialFullManifold (j : Kind) : IsManifold I₃ ω (SpecialFullFilling j) :=
  (specialFullFilling_construction j).2.2.1

/-- The actual quotient map for the special periods and their prescribed twists. -/
def fullQuotient (j : Kind) : (specialLocalData j).TotalSpace → SpecialFullFilling j :=
  (specialLocalData j).quotient j.twist (mainTwist_admissible j)

theorem fullQuotient_isLocalDiffeomorph (j : Kind) :
    IsLocalDiffeomorph I₃ I₃ ω (fullQuotient j) :=
  CanonicalQuotientCharts.quotient_isLocalDiffeomorph
    (specialLocalData j) j.twist (mainTwist_admissible j)

theorem fullQuotient_surjective (j : Kind) : Function.Surjective (fullQuotient j) :=
  (specialLocalData j).quotient_surjective j.twist (mainTwist_admissible j)

/-- The canonical section in the already constructed native ambient bundle. -/
def fullSection (j : Kind) (y : SpecialFullFilling j) : (Elliptic.fullBundle j).Fiber y :=
  CanonicalSections.quotientSection (specialLocalData j) j.twist (mainTwist_admissible j) y

/-- Its actual section map into the original canonical-bundle total space. -/
def fullSectionMap (j : Kind) (y : SpecialFullFilling j) : (Elliptic.fullBundle j).TotalSpace :=
  ⟨y, fullSection j y⟩

@[simp] theorem fullSectionMap_proj (j : Kind) (y : SpecialFullFilling j) :
    (fullSectionMap j y).proj = y := rfl

theorem fullSectionMap_holomorphic (j : Kind) :
    ContMDiff I₃ ((I₃).prod I₁) ω (fullSectionMap j) :=
  CanonicalSections.quotientSectionMap_holomorphic
    (specialLocalData j) j.twist (mainTwist_admissible j)

/-- The bundled holomorphic section of the actual full filling's canonical bundle. -/
def fullHolomorphicSection (j : Kind) :
    ContMDiffSection I₃ ℂ ω (Elliptic.fullBundle j).Fiber where
  toFun := fullSection j
  contMDiff_toFun := fullSectionMap_holomorphic j

@[simp] theorem fullHolomorphicSection_apply (j : Kind) (y : SpecialFullFilling j) :
    fullHolomorphicSection j y = fullSection j y := rfl

/-- Exact recovery by the genuine differential of the actual quotient map. -/
theorem fullSection_pullback (j : Kind) (x : (specialLocalData j).TotalSpace) :
    Pullback.pullbackEquiv (fullQuotient_isLocalDiffeomorph j) x
      (fullSection j (fullQuotient j x)) =
        SectionsUnit.specialCoefficient j x.1 •
          familyCanonicalVolume (specialLocalData j).periods x :=
  CanonicalSections.quotientSection_pullback
    (specialLocalData j) j.twist (mainTwist_admissible j) x

/-- The intrinsic three-covector statement uses the actual manifold derivative. -/
theorem fullSection_intrinsic_pullback (j : Kind) (x : (specialLocalData j).TotalSpace) :
    (Elliptic.fullIntrinsicEquiv j (fullQuotient j x)
      (fullSection j (fullQuotient j x))).compContinuousLinearMap
        (mfderiv I₃ I₃ (fullQuotient j) x) =
          SectionsUnit.specialCoefficient j x.1 • volume := by
  have h := congrArg (Atlas.intrinsicEquiv (specialLocalData j).TotalSpace x)
    (fullSection_pullback j x)
  rw [Pullback.intrinsic_pullbackEquiv, map_smul] at h
  simp only [familyCanonicalVolume, Atlas.intrinsicEquiv_unitFrame] at h
  exact h

/-- The full native section has no zeros away from the prescribed central support. -/
theorem fullSection_eq_zero_iff (j : Kind) (y : SpecialFullFilling j) :
    fullSection j y = 0 ↔ SectionsUnit.vanishingOrder j ≠ 0 ∧
      specialFullFillingProjection j y = Wikipedia.HopfProblem.Elliptic.discZero :=
  CanonicalSections.quotientSection_eq_zero_iff
    (specialLocalData j) j.twist (mainTwist_admissible j) y

theorem fullSection_ne_zero_iff (j : Kind) (y : SpecialFullFilling j) :
    fullSection j y ≠ 0 ↔ SectionsUnit.vanishingOrder j = 0 ∨
      specialFullFillingProjection j y ≠ Wikipedia.HopfProblem.Elliptic.discZero :=
  CanonicalSections.quotientSection_ne_zero_iff
    (specialLocalData j) j.twist (mainTwist_admissible j) y

/-- The order-three filling has a nowhere-zero genuine ambient canonical section. -/
theorem fullSection_three_ne_zero (y : SpecialFullFilling .three) :
    fullSection .three y ≠ 0 :=
  (fullSection_ne_zero_iff .three y).mpr (Or.inl rfl)

/-- In the order-four filling its exact zero set is the central surface. -/
theorem fullSection_four_eq_zero_iff (y : SpecialFullFilling .four) :
    fullSection .four y = 0 ↔
      specialFullFillingProjection .four y = Wikipedia.HopfProblem.Elliptic.discZero := by
  simpa only [SectionsUnit.vanishingOrder, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    true_and] using fullSection_eq_zero_iff .four y

theorem fullSection_four_ne_zero_iff (y : SpecialFullFilling .four) :
    fullSection .four y ≠ 0 ↔
      specialFullFillingProjection .four y ≠ Wikipedia.HopfProblem.Elliptic.discZero :=
  (fullSection_four_eq_zero_iff y).not

theorem fullSection_four_zeroSet :
    {y : SpecialFullFilling .four | fullSection .four y = 0} =
      specialFullFillingProjection .four ⁻¹' {Wikipedia.HopfProblem.Elliptic.discZero} := by
  ext y
  exact fullSection_four_eq_zero_iff y

/-- The genuine differential recovery identity uniquely determines the section. -/
theorem fullSection_unique (j : Kind)
    (t : ∀ y : SpecialFullFilling j, (Elliptic.fullBundle j).Fiber y)
    (ht : ∀ x, Pullback.pullbackEquiv (fullQuotient_isLocalDiffeomorph j) x
      (t (fullQuotient j x)) = SectionsUnit.specialCoefficient j x.1 •
        familyCanonicalVolume (specialLocalData j).periods x) :
    t = fullSection j :=
  CanonicalSections.quotientSection_unique
    (specialLocalData j) j.twist (mainTwist_admissible j) t ht

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
