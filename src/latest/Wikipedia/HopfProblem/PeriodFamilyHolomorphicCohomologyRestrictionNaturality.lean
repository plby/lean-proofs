import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRestrictionBiholomorph

/-!
# Naturality under inclusions of original base opens

For nested base opens, the original restricted families map by the literal
subtype inclusion and the unchanged real torus coordinate.  The maps are
holomorphic for the actual quotient atlases, through the native restriction
biholomorphisms and the inherited open-submanifold inclusion. They satisfy
identity and composition laws and preserve the original covering squares.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The actual map of restricted families induced by a nested base open. -/
def restrictionInclusion (P : HolomorphicPeriodMap V B) {U W : Opens B} (h : U ≤ W) :
    (restrictedPeriods P U).TotalSpace → (restrictedPeriods P W).TotalSpace :=
  fun x => (Opens.inclusion h x.1, x.2)

@[simp] theorem restrictionInclusion_apply (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (x : (restrictedPeriods P U).TotalSpace) :
    restrictionInclusion P h x = (Opens.inclusion h x.1, x.2) := rfl

@[simp] theorem restrictionInclusion_refl (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : (restrictedPeriods P U).TotalSpace) :
    restrictionInclusion P (le_refl U) x = x := rfl

/-- Nesting two base-open inclusions is the original composite inclusion. -/
@[simp] theorem restrictionInclusion_trans (P : HolomorphicPeriodMap V B)
    {U W Z : Opens B} (hUW : U ≤ W) (hWZ : W ≤ Z)
    (x : (restrictedPeriods P U).TotalSpace) :
    restrictionInclusion P hWZ (restrictionInclusion P hUW x) =
      restrictionInclusion P (hUW.trans hWZ) x := rfl

/-- The full-preimage comparison square commutes literally. -/
@[simp] theorem toPreimage_restrictionInclusion (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (x : (restrictedPeriods P U).TotalSpace) :
    toPreimage P W (restrictionInclusion P h x) =
      Opens.inclusion (Zero.basePreimage_mono P h) (toPreimage P U x) := rfl

@[simp] theorem fromPreimage_inclusion (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (x : Zero.basePreimage P U) :
    fromPreimage P W (Opens.inclusion (Zero.basePreimage_mono P h) x) =
      restrictionInclusion P h (fromPreimage P U x) := rfl

/-- The covering maps retain their original complex-vector coordinates. -/
@[simp] theorem restrictionInclusion_quotientMap (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (x : U × ComplexPlane₂) :
    restrictionInclusion P h ((restrictedPeriods P U).quotientMap x) =
      (restrictedPeriods P W).quotientMap (Opens.inclusion h x.1, x.2) := rfl

@[simp] theorem restrictionInclusion_projection (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (x : (restrictedPeriods P U).TotalSpace) :
    (restrictedPeriods P W).projection (restrictionInclusion P h x) =
      Opens.inclusion h ((restrictedPeriods P U).projection x) := rfl

@[simp] theorem restrictionInclusion_zeroSection (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (b : U) :
    restrictionInclusion P h ((restrictedPeriods P U).zeroSection b) =
      (restrictedPeriods P W).zeroSection (Opens.inclusion h b) := rfl

/-- Each actual complex period torus maps by precisely the original inclusion. -/
@[simp] theorem restrictionInclusion_fibreInclusion (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (b : U) (z : (P.point b).Torus) :
    restrictionInclusion P h ((restrictedPeriods P U).fibreInclusion b z) =
      (restrictedPeriods P W).fibreInclusion (Opens.inclusion h b) z := rfl

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual inclusion of restricted families is holomorphic in both native atlases. -/
theorem restrictionInclusion_holomorphic (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) :
    letI := (restrictedPeriods P U).totalChartedSpace
    letI := (restrictedPeriods P W).totalChartedSpace
    ContMDiff IT IT ω (restrictionInclusion P h) := by
  let := (restrictedPeriods P U).totalChartedSpace
  let := (restrictedPeriods P W).totalChartedSpace
  let := P.totalChartedSpace
  have hmid : ContMDiff IT IT ω
      (Opens.inclusion (Zero.basePreimage_mono P h) :
        Zero.basePreimage P U → Zero.basePreimage P W) := contMDiff_inclusion _
  exact ((fromPreimage_holomorphic P W).comp
    (hmid.comp (toPreimage_holomorphic P U))).congr (fun _ => rfl)

/-- The native biholomorphisms are natural in the original base open. -/
@[simp] theorem restrictionBiholomorph_naturality (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (x : (restrictedPeriods P U).TotalSpace) :
    restrictionBiholomorph P W (restrictionInclusion P h x) =
      Opens.inclusion (Zero.basePreimage_mono P h) (restrictionBiholomorph P U x) := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction
