import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicCoverCoordinates

/-!
# Native holomorphic sections and fractions in regular-cover coordinates

The original coordinate map is bundled as a holomorphic open map.  The
analytic representatives of native holomorphic sections define genuine
holomorphic sections on the actual coordinate image.  Their categorical
stalk pullbacks recover the original germs by literal section restriction.
Consequently genuine local meromorphic fractions are preserved, including
points where denominator values vanish but their germs are nonzero.
-/

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover HolomorphicMeromorphic

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] coverChartedSpace cover_isManifold

/-- The actual coordinate embedding, with its proved native holomorphicity. -/
def coordMap : ContMDiffMap IF IF Cover Model ω := ⟨coord, coord_contMDiff⟩

@[simp] theorem coordMap_apply (x : Cover) : coordMap x = coord x := rfl

theorem coordMap_isOpenMap : IsOpenMap coordMap := coord_isOpenMap

/-- A point of a native open set, regarded in its actual coordinate image. -/
def coordinatePoint (U : Opens Cover) (x : U) : coordOpen U :=
  ⟨coord x.val, ⟨x.val, x.property, rfl⟩⟩

@[simp] theorem coordinatePoint_val (U : Opens Cover) (x : U) :
    (coordinatePoint U x).val = coord x.val := rfl

/-- The analytic coordinate representative is a native holomorphic
section on the actual open image, with the standard inherited model atlas. -/
noncomputable def coordinateSection (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) :
    HolomorphicFunctionSheaf.Section IF Model (coordOpen U) :=
  ⟨fun y => sectionCoordinates U p y.val, by
    intro y
    exact (contMDiffAt_subtype_iff (f := sectionCoordinates U p) (x := y)).mpr
      ((sectionCoordinates_analyticOnNhd U p) y.val y.property).contDiffAt.contMDiffAt⟩

@[simp] theorem coordinateSection_apply (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) (y : coordOpen U) :
    coordinateSection U p y = sectionCoordinates U p y.val := rfl

@[simp] theorem coordinateSection_coordinatePoint (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) (x : U) :
    coordinateSection U p (coordinatePoint U x) = p x :=
  sectionCoordinates_apply U p x

theorem le_coord_pullbackOpen (U : Opens Cover) :
    U ≤ pullbackOpen IF IF coordMap (coordOpen U) := by
  intro x hx
  exact ⟨x, hx, rfl⟩

/-- Injectivity of the original coordinate map identifies the actual
inverse image of the coordinate domain with the original section domain. -/
theorem coord_pullbackOpen_eq (U : Opens Cover) :
    pullbackOpen IF IF coordMap (coordOpen U) = U := by
  apply le_antisymm
  · intro x hx
    change coord x ∈ coord '' (U : Set Cover) at hx
    obtain ⟨y, hy, hyx⟩ := hx
    exact coord_injective hyx ▸ hy
  · exact le_coord_pullbackOpen U

/-- Genuine holomorphic pullback, restricted to the original open set,
is exactly the original section, not merely equal at one base point. -/
theorem coordinateSection_pullback_restrict (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) :
    HolomorphicFunctionSheaf.restrictionAlgHom IF Cover (le_coord_pullbackOpen U)
      (holomorphicPullback IF IF coordMap (coordOpen U) (coordinateSection U p)) = p := by
  apply ContMDiffMap.ext
  intro x
  change sectionCoordinates U p (coord x.val) = p x
  exact sectionCoordinates_apply U p x

/-- The actual categorical pullback on holomorphic stalks recovers the
original native germ of a coordinate section. -/
theorem holomorphicPullbackStalk_coordinateSection (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) (x : U) :
    holomorphicPullbackStalk IF IF coordMap x.val
      (holomorphicGerm IF Model (coordOpen U) (coordinatePoint U x) (coordinateSection U p)) =
        holomorphicGerm IF Cover U x p := by
  have hres := holomorphicGerm_restrict IF Cover (le_coord_pullbackOpen U) x
    (holomorphicPullback IF IF coordMap (coordOpen U) (coordinateSection U p))
  have heq := congrArg (holomorphicGerm IF Cover U x)
    (coordinateSection_pullback_restrict U p)
  exact (holomorphicPullbackStalk_germ IF IF coordMap (coordOpen U) x.val
    ((le_coord_pullbackOpen U) x.property) (coordinateSection U p)).trans
      (hres.symm.trans heq)

/-- Extending the genuine holomorphic stalk map to its fraction fields
preserves the same coordinate-section germ identity. -/
theorem germPullback_coordinateSection (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) (x : U) :
    germPullback IF IF coordMap coordMap_isOpenMap x.val
      (sectionGerm IF Model (coordOpen U) (coordinatePoint U x) (coordinateSection U p)) =
        sectionGerm IF Cover U x p := by
  exact (germPullback_ofHolomorphicGerm IF IF coordMap coordMap_isOpenMap x.val
    (holomorphicGerm IF Model (coordOpen U) (coordinatePoint U x)
      (coordinateSection U p))).trans
        (congrArg (ofHolomorphicGerm IF Cover x.val)
          (holomorphicPullbackStalk_coordinateSection U p x))

/-- Nonzero original denominator germs imply nonzero denominator germs
on every point of the actual coordinate image. -/
theorem coordinateSection_nonzero_germs (U : Opens Cover)
    (q : HolomorphicFunctionSheaf.Section IF Cover U)
    (hq : ∀ x : U, holomorphicGerm IF Cover U x q ≠ 0) :
    ∀ y : coordOpen U,
      holomorphicGerm IF Model (coordOpen U) y (coordinateSection U q) ≠ 0 := by
  rintro ⟨y, hy⟩ hzero
  obtain ⟨x, hx, rfl⟩ := hy
  apply hq ⟨x, hx⟩
  exact (holomorphicPullbackStalk_coordinateSection U q ⟨x, hx⟩).symm.trans
    ((congrArg (holomorphicPullbackStalk IF IF coordMap x) hzero).trans (map_zero _))

/-- The genuine meromorphic section represented by the original local
fraction in its actual open coordinate image. -/
noncomputable def coordinateFraction (U : Opens Cover)
    (p q : HolomorphicFunctionSheaf.Section IF Cover U)
    (hq : ∀ x : U, holomorphicGerm IF Cover U x q ≠ 0) :
    HolomorphicMeromorphic.Section IF Model (coordOpen U) :=
  ofFraction IF Model (coordOpen U) (coordinateSection U p) (coordinateSection U q)
    (coordinateSection_nonzero_germs U q hq)

@[simp] theorem coordinateFraction_apply (U : Opens Cover)
    (p q : HolomorphicFunctionSheaf.Section IF Cover U)
    (hq : ∀ x : U, holomorphicGerm IF Cover U x q ≠ 0) (y : coordOpen U) :
    coordinateFraction U p q hq y =
      fraction IF Model (coordOpen U) (coordinateSection U p) (coordinateSection U q) y := rfl

/-- Actual meromorphic germ pullback recovers the original fraction at
every point, including zeros of the pointwise denominator. -/
theorem germPullback_coordinateFraction (U : Opens Cover)
    (p q : HolomorphicFunctionSheaf.Section IF Cover U)
    (hq : ∀ x : U, holomorphicGerm IF Cover U x q ≠ 0) (x : U) :
    germPullback IF IF coordMap coordMap_isOpenMap x.val
      (coordinateFraction U p q hq (coordinatePoint U x)) = fraction IF Cover U p q x := by
  change germPullback IF IF coordMap coordMap_isOpenMap x.val
      (sectionGerm IF Model (coordOpen U) (coordinatePoint U x) (coordinateSection U p) /
        sectionGerm IF Model (coordOpen U) (coordinatePoint U x) (coordinateSection U q)) =
    sectionGerm IF Cover U x p / sectionGerm IF Cover U x q
  exact (map_div₀ (germPullback IF IF coordMap coordMap_isOpenMap x.val) _ _).trans
    (congrArg₂ (fun a b : Germ IF Cover x.val => a / b)
      (germPullback_coordinateSection U p x) (germPullback_coordinateSection U q x))

/-- The corresponding equality of genuine meromorphic sections on the
original native open set. -/
theorem coordinateFraction_pullback_restrict (U : Opens Cover)
    (p q : HolomorphicFunctionSheaf.Section IF Cover U)
    (hq : ∀ x : U, holomorphicGerm IF Cover U x q ≠ 0) :
    HolomorphicMeromorphic.restrict IF Cover (le_coord_pullbackOpen U)
      (pullbackSection IF IF coordMap coordMap_isOpenMap (coordOpen U)
        (coordinateFraction U p q hq)) = ofFraction IF Cover U p q hq := by
  apply HolomorphicMeromorphic.section_ext
  intro x
  exact germPullback_coordinateFraction U p q hq x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
