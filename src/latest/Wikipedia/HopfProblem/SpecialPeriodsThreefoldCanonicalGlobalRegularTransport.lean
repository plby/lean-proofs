import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPatchesHolomorphic

/-!
# Transport of the native regular canonical section to the actual threefold

The original regular canonical bundle is identified with the restriction
of the global canonical bundle by actual differential pullback.  The
transport below preserves the original atlases and bundle topology,
including the literal canonical fibre over every point of the global
regular locus.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace specialRegularFamilyChartedSpace
  localPieceChartedSpace localPiece_nonempty localPiece_isManifold

local instance transportRegularManifold : IsManifold I₃ ω Threefold.SpecialRegularFamily :=
  specialRegularFamily_isManifold

local instance transportGlobalManifold : IsManifold I₃ ω Threefold.Space :=
  Threefold.space_isManifold

/-- Inverse differential pullback puts the native section in its actual global fibre. -/
def sectionAlongInclusion (C : TriangleRegularPoint → ℂ) (x : Threefold.SpecialRegularFamily) :
    Threefold.Canonical.bundle.Fiber (regularFamilyInclusion x) :=
  (Regular.pullbackEquiv x).symm (descendedWeightedSection C x)

def sectionAlongInclusionMap (C : TriangleRegularPoint → ℂ)
    (x : Threefold.SpecialRegularFamily) : Threefold.Canonical.bundle.TotalSpace :=
  ⟨regularFamilyInclusion x, sectionAlongInclusion C x⟩

@[simp] theorem sectionAlongInclusion_pullback (C : TriangleRegularPoint → ℂ)
    (x : Threefold.SpecialRegularFamily) :
    Regular.pullbackEquiv x (sectionAlongInclusion C x) = descendedWeightedSection C x :=
  (Regular.pullbackEquiv x).apply_symm_apply _

theorem sectionAlongInclusionMap_holomorphic (C : TriangleRegularPoint → ℂ)
    (hhol : ContMDiff I₁ I₁ ω C) (hinv : WeightedInvariant C) :
    ContMDiff I₃ Iᴷ ω (sectionAlongInclusionMap C) := by
  change ContMDiff I₃ Iᴷ ω
    (Threefold.Canonical.patchPushforward none ∘ descendedWeightedSectionMap C)
  exact (Threefold.Canonical.patchPushforward_holomorphic none).comp
    (descendedWeightedSectionMap_holomorphic C hhol hinv)

/-- The comparison is pullback of actual alternating three-covectors. -/
theorem sectionAlongInclusion_intrinsic_pullback (C : TriangleRegularPoint → ℂ)
    (x : Threefold.SpecialRegularFamily) :
    (Threefold.Canonical.intrinsicEquiv (regularFamilyInclusion x)
      (sectionAlongInclusion C x)).compContinuousLinearMap
        (mfderiv I₃ I₃ regularFamilyInclusion x) =
      Regular.intrinsicEquiv x (descendedWeightedSection C x) :=
  (Regular.pullback_intrinsic x (sectionAlongInclusion C x)).symm.trans
    (congrArg (Regular.intrinsicEquiv x) (sectionAlongInclusion_pullback C x))

/-- The genuine global canonical section on the entire actual regular locus. -/
def globalWeightedSection (C : TriangleRegularPoint → ℂ) (y : regularLocus) :
    Threefold.Canonical.bundle.Fiber y.val :=
  Pullback.fiberTransport
    (congrArg Subtype.val (regularFamilyBiholomorph.apply_symm_apply y))
    (sectionAlongInclusion C (regularLocusBiholomorph y))

def globalWeightedSectionMap (C : TriangleRegularPoint → ℂ) (y : regularLocus) :
    Threefold.Canonical.bundle.TotalSpace := ⟨y.val, globalWeightedSection C y⟩

@[simp] theorem globalWeightedSectionMap_proj (C : TriangleRegularPoint → ℂ)
    (y : regularLocus) : (globalWeightedSectionMap C y).proj = y.val := rfl

theorem globalWeightedSectionMap_eq_transport (C : TriangleRegularPoint → ℂ)
    (y : regularLocus) :
    globalWeightedSectionMap C y = sectionAlongInclusionMap C (regularLocusBiholomorph y) :=
  ((SectionsDescent.fiberTransport_eq_iff_totalSpace_eq (N := Threefold.Space)
    (congrArg Subtype.val (regularFamilyBiholomorph.apply_symm_apply y))
    (sectionAlongInclusion C (regularLocusBiholomorph y)) _).mp rfl).symm

theorem globalWeightedSectionMap_holomorphic (C : TriangleRegularPoint → ℂ)
    (hhol : ContMDiff I₁ I₁ ω C) (hinv : WeightedInvariant C) :
    ContMDiff I₃ Iᴷ ω (globalWeightedSectionMap C) := by
  have h : globalWeightedSectionMap C = sectionAlongInclusionMap C ∘
      regularLocusBiholomorph := funext (globalWeightedSectionMap_eq_transport C)
  rw [h]
  exact (sectionAlongInclusionMap_holomorphic C hhol hinv).comp
    regularLocusBiholomorph.contMDiff

@[simp] theorem globalWeightedSection_inclusion (C : TriangleRegularPoint → ℂ)
    (x : Threefold.SpecialRegularFamily) :
    globalWeightedSection C (regularFamilyBiholomorph x) = sectionAlongInclusion C x :=
  congrArg (fun p : Threefold.Canonical.bundle.TotalSpace => id (α := ℂ) p.2)
    ((globalWeightedSectionMap_eq_transport C (regularFamilyBiholomorph x)).trans
      (congrArg (sectionAlongInclusionMap C) (regularFamilyBiholomorph.symm_apply_apply x)))

theorem globalWeightedSection_pullback (C : TriangleRegularPoint → ℂ)
    (x : Threefold.SpecialRegularFamily) :
    Regular.pullbackEquiv x
      (globalWeightedSection C (regularFamilyBiholomorph x)) = descendedWeightedSection C x := by
  rw [globalWeightedSection_inclusion, sectionAlongInclusion_pullback]

theorem globalWeightedSection_ne_zero (C : TriangleRegularPoint → ℂ)
    (hinv : WeightedInvariant C) (hne : ∀ z, C z ≠ 0) (y : regularLocus) :
    globalWeightedSection C y ≠ 0 := by
  change Pullback.fiberTransport _ (sectionAlongInclusion C (regularLocusBiholomorph y)) ≠ 0
  apply (not_congr (Pullback.fiberTransport _).map_eq_zero_iff).mpr
  apply (not_congr (Regular.pullbackEquiv (regularLocusBiholomorph y)).symm.map_eq_zero_iff).mpr
  exact descendedWeightedSection_ne_zero C hinv hne (regularLocusBiholomorph y)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
