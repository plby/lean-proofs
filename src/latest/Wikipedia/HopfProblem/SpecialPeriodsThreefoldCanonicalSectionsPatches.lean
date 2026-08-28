import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsRestriction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticFullPatch

/-!
# The actual elliptic canonical sections on the full global patches

The sections are transported by the already proved native canonical
bundle biholomorphisms, using inverse differential pullback on fibres.
Equality transport retains the literal fibre over each point of the
actual global patch.  The resulting maps are holomorphic for the original
global bundle atlas.  Their zeros are exactly the prescribed global
central support, with no additional zeros on the full patches.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace

local instance patchSectionsGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The genuine local section in the global canonical fibre at its actual inclusion. -/
def sectionAlongInclusion (j : Kind) (x : SpecialEllipticPiece j) :
    Threefold.Canonical.bundle.Fiber (EllipticGeometry.inclusion j x) :=
  (Elliptic.patchPullback j x).symm (smallSection j x)

def sectionAlongInclusionMap (j : Kind) (x : SpecialEllipticPiece j) :
    Threefold.Canonical.bundle.TotalSpace :=
  ⟨EllipticGeometry.inclusion j x, sectionAlongInclusion j x⟩

@[simp] theorem sectionAlongInclusion_pullback (j : Kind) (x : SpecialEllipticPiece j) :
    Elliptic.patchPullback j x (sectionAlongInclusion j x) = smallSection j x :=
  (Elliptic.patchPullback j x).apply_symm_apply _

theorem sectionAlongInclusionMap_holomorphic (j : Kind) :
    ContMDiff IF Iᴷ ω (sectionAlongInclusionMap j) := by
  change ContMDiff IF Iᴷ ω
    (fun x => ((Elliptic.bundleBiholomorph j (smallSectionMap j x)) :
      Threefold.Canonical.bundle.TotalSpace))
  exact (contMDiff_subtype_val (I := Iᴷ)
    (U := Threefold.Canonical.bundlePatch (some (some j)))).comp
      ((Elliptic.bundleBiholomorph j).contMDiff.comp (smallSectionMap_holomorphic j))

/-- Exact recovery on intrinsic alternating three-covectors, using the
actual global-patch inclusion differential. -/
theorem sectionAlongInclusion_intrinsic_pullback (j : Kind) (x : SpecialEllipticPiece j) :
    (Threefold.Canonical.intrinsicEquiv (EllipticGeometry.inclusion j x)
      (sectionAlongInclusion j x)).compContinuousLinearMap
        (mfderiv IF IF (EllipticGeometry.inclusion j) x) =
      Elliptic.intrinsicEquiv j x (smallSection j x) :=
  (Elliptic.intrinsic_patchPullback j x (sectionAlongInclusion j x)).symm.trans
    (congrArg (Elliptic.intrinsicEquiv j x) (sectionAlongInclusion_pullback j x))

theorem sectionAlongInclusion_eq_zero_iff (j : Kind) (x : SpecialEllipticPiece j) :
    sectionAlongInclusion j x = 0 ↔ smallSection j x = 0 :=
  (Elliptic.patchPullback j x).symm.map_eq_zero_iff

/-- The transported section agrees with the original full-filling bundle
comparison on its entire exact source. -/
theorem fullBundlePatchBiholomorph_fullSectionOnPiece (j : Kind)
    (x : SpecialEllipticPiece j) :
    (Elliptic.fullBundlePatchBiholomorph j (fullSectionOnPiece j x) :
      Threefold.Canonical.bundle.TotalSpace) = sectionAlongInclusionMap j x := by
  rw [Elliptic.fullBundlePatchBiholomorph_val]
  rfl

/-- A section of the literal global canonical fibre on the entire patch. -/
def patchSection (j : Kind) (y : Threefold.liftedPatch (some (some j))) :
    Threefold.Canonical.bundle.Fiber y.val :=
  Pullback.fiberTransport
    (congrArg Subtype.val ((EllipticGeometry.nativePatchBiholomorph j).apply_symm_apply y))
    (sectionAlongInclusion j ((EllipticGeometry.nativePatchBiholomorph j).symm y))

def patchSectionMap (j : Kind) (y : Threefold.liftedPatch (some (some j))) :
    Threefold.Canonical.bundle.TotalSpace := ⟨y.val, patchSection j y⟩

@[simp] theorem patchSectionMap_proj (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) : (patchSectionMap j y).proj = y.val := rfl

theorem patchSectionMap_eq_transport (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    patchSectionMap j y =
      sectionAlongInclusionMap j ((EllipticGeometry.nativePatchBiholomorph j).symm y) :=
  ((SectionsDescent.fiberTransport_eq_iff_totalSpace_eq (N := Threefold.Space)
    (congrArg Subtype.val ((EllipticGeometry.nativePatchBiholomorph j).apply_symm_apply y))
      (sectionAlongInclusion j ((EllipticGeometry.nativePatchBiholomorph j).symm y)) _).mp rfl).symm

theorem patchSectionMap_holomorphic (j : Kind) :
    ContMDiff IF Iᴷ ω (patchSectionMap j) := by
  have h : patchSectionMap j = sectionAlongInclusionMap j ∘
      (EllipticGeometry.nativePatchBiholomorph j).symm :=
    funext (patchSectionMap_eq_transport j)
  rw [h]
  exact (sectionAlongInclusionMap_holomorphic j).comp
    (EllipticGeometry.nativePatchBiholomorph j).symm.contMDiff

@[simp] theorem patchSection_inclusion (j : Kind) (x : SpecialEllipticPiece j) :
    patchSection j (EllipticGeometry.nativePatchBiholomorph j x) =
      sectionAlongInclusion j x :=
  congrArg (fun p : Threefold.Canonical.bundle.TotalSpace => id (α := ℂ) p.2)
    ((patchSectionMap_eq_transport j (EllipticGeometry.nativePatchBiholomorph j x)).trans
      (congrArg (sectionAlongInclusionMap j)
        ((EllipticGeometry.nativePatchBiholomorph j).symm_apply_apply x)))

theorem patchSection_pullback (j : Kind) (x : SpecialEllipticPiece j) :
    Elliptic.patchPullback j x
      (patchSection j (EllipticGeometry.nativePatchBiholomorph j x)) = smallSection j x := by
  rw [patchSection_inclusion, sectionAlongInclusion_pullback]

/-- The actual global sphere fibre is the only possible zero support. -/
theorem patchSection_eq_zero_iff (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    patchSection j y = 0 ↔ SectionsUnit.vanishingOrder j ≠ 0 ∧
      Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j := by
  let x := (EllipticGeometry.nativePatchBiholomorph j).symm y
  have hb : EllipticGeometry.inclusion j x = y.val :=
    congrArg Subtype.val ((EllipticGeometry.nativePatchBiholomorph j).apply_symm_apply y)
  have hc : specialFullFillingProjection j x.val = Wikipedia.HopfProblem.Elliptic.discZero ↔
      Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j := by
    rw [← hb, EllipticGeometry.projectionSphere_inclusion_eq_value_iff]
    constructor
    · exact congrArg (fun s : Disc => (s : ℂ))
    · exact fun h => Subtype.ext h
  change Pullback.fiberTransport hb (sectionAlongInclusion j x) = 0 ↔ _
  rw [(Pullback.fiberTransport hb).map_eq_zero_iff,
    sectionAlongInclusion_eq_zero_iff, smallSection_eq_zero_iff]
  exact and_congr_right fun _ => hc

theorem patchSection_ne_zero_iff (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    patchSection j y ≠ 0 ↔ SectionsUnit.vanishingOrder j = 0 ∨
      Threefold.projectionSphere y.val ≠ EllipticGeometry.sphereValue j := by
  simpa only [not_and_or, not_not] using not_congr (patchSection_eq_zero_iff j y)

theorem patchSection_three_ne_zero
    (y : Threefold.liftedPatch (some (some .three))) : patchSection .three y ≠ 0 :=
  (patchSection_ne_zero_iff .three y).mpr (Or.inl rfl)

theorem patchSection_four_eq_zero_iff
    (y : Threefold.liftedPatch (some (some .four))) :
    patchSection .four y = 0 ↔ Threefold.projectionSphere y.val = ((1 : ℂ) : RiemannSphere) := by
  simpa only [SectionsUnit.vanishingOrder, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    true_and, EllipticGeometry.sphereValue_four] using patchSection_eq_zero_iff .four y

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
