import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalRegularWeighted
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDescentAction

/-!
# Differential descent to the original regular canonical bundle

The actual triangle quotient is a surjective local biholomorphism for
the original varying-period and quotient atlases.  Invariant weighted
three-forms therefore descend to genuine holomorphic sections of the
already constructed regular canonical bundle, with exact differential
recovery and preservation of nonvanishing.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular

open TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

attribute [local instance] specialRegularFamilyChartedSpace

local instance descentUpstairsChartedSpace : ChartedSpace Model SpecialRegularUpstairs :=
  specialRegularData.periods.totalChartedSpace

local instance descentUpstairsManifold : IsManifold I₃ ω SpecialRegularUpstairs :=
  specialRegularData.periods.totalSpace_isManifold

local instance descentUpstairsAction : MulAction TriangleGroup SpecialRegularUpstairs :=
  specialRegularData.totalAction

local instance descentRegularManifold : IsManifold I₃ ω Threefold.SpecialRegularFamily :=
  specialRegularFamily_isManifold

/-- The proved actual covering on the original regular base. -/
theorem baseCovering :
    IsQuotientCoveringMap specialRegularData.baseQuotient TriangleGroup :=
  TrianglePeriodFamily.regularCovering specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂

/-- The actual triangle quotient, with its original regular-family codomain. -/
def familyQuotient : SpecialRegularUpstairs → Threefold.SpecialRegularFamily :=
  specialRegularData.quotient

theorem familyQuotient_surjective : Function.Surjective familyQuotient :=
  specialRegularData.quotient_surjective

theorem familyQuotient_isLocalDiffeomorph :
    IsLocalDiffeomorph I₃ I₃ ω familyQuotient :=
  specialRegularData.quotient_isLocalDiffeomorph baseCovering

/-- Each actual triangle action is biholomorphic in the native family atlas. -/
def upstairsActionBiholomorph (g : TriangleGroup) :
    Diffeomorph I₃ I₃ SpecialRegularUpstairs SpecialRegularUpstairs ω where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := familyMap_holomorphic specialRegularData g
  contMDiff_invFun := familyMap_holomorphic specialRegularData g⁻¹

@[simp] theorem upstairsActionBiholomorph_apply (g : TriangleGroup)
    (x : SpecialRegularUpstairs) :
    upstairsActionBiholomorph g x = familyMap specialRegularData g x := rfl

/-- Invariance means actual pullback on native canonical fibres. -/
def WeightedInvariant (C : TriangleRegularPoint → ℂ) : Prop :=
  ∀ (g : TriangleGroup) (x : SpecialRegularUpstairs),
    Pullback.pullbackLinear (familyMap specialRegularData g) x
      (upstairsWeightedSection C (familyMap specialRegularData g x)) =
        upstairsWeightedSection C x

theorem weightedCompatible (C : TriangleRegularPoint → ℂ) (hC : WeightedInvariant C) :
    SectionsDescent.Compatible familyQuotient_isLocalDiffeomorph
      (upstairsWeightedSection C) := by
  apply SectionsDescent.compatible_of_action_invariant familyQuotient_isLocalDiffeomorph
    (fun g => (upstairsActionBiholomorph g).isLocalDiffeomorph)
  · intro g x
    exact specialRegularData.quotient_smul g x
  · intro x y hxy
    exact (specialRegularData.quotient_eq_iff y x).mp hxy.symm
  · intro g x
    exact hC g x

/-- The actual descended section of the old regular canonical bundle. -/
def descendedWeightedSection (C : TriangleRegularPoint → ℂ)
    (y : Threefold.SpecialRegularFamily) : Regular.bundle.Fiber y :=
  SectionsDescent.descendedSection familyQuotient_isLocalDiffeomorph
    familyQuotient_surjective (upstairsWeightedSection C) y

def descendedWeightedSectionMap (C : TriangleRegularPoint → ℂ)
    (y : Threefold.SpecialRegularFamily) : Regular.bundle.TotalSpace :=
  ⟨y, descendedWeightedSection C y⟩

@[simp] theorem descendedWeightedSectionMap_proj (C : TriangleRegularPoint → ℂ)
    (y : Threefold.SpecialRegularFamily) : (descendedWeightedSectionMap C y).proj = y := rfl

theorem descendedWeightedSectionMap_holomorphic (C : TriangleRegularPoint → ℂ)
    (hhol : ContMDiff I₁ I₁ ω C) (hinv : WeightedInvariant C) :
    ContMDiff I₃ ((I₃).prod I₁) ω (descendedWeightedSectionMap C) :=
  SectionsDescent.descendedSection_holomorphic familyQuotient_isLocalDiffeomorph
    familyQuotient_surjective (upstairsWeightedSection C) (weightedCompatible C hinv)
    (upstairsWeightedSectionMap_holomorphic C hhol)

def descendedWeightedHolomorphicSection (C : TriangleRegularPoint → ℂ)
    (hhol : ContMDiff I₁ I₁ ω C) (hinv : WeightedInvariant C) :
    ContMDiffSection I₃ ℂ ω Regular.bundle.Fiber where
  toFun := descendedWeightedSection C
  contMDiff_toFun := descendedWeightedSectionMap_holomorphic C hhol hinv

@[simp] theorem descendedWeightedHolomorphicSection_apply (C : TriangleRegularPoint → ℂ)
    (hhol : ContMDiff I₁ I₁ ω C) (hinv : WeightedInvariant C)
    (y : Threefold.SpecialRegularFamily) :
    descendedWeightedHolomorphicSection C hhol hinv y = descendedWeightedSection C y := rfl

/-- Exact recovery by the original quotient differential. -/
theorem descendedWeightedSection_pullback (C : TriangleRegularPoint → ℂ)
    (hinv : WeightedInvariant C) (x : SpecialRegularUpstairs) :
    Pullback.pullbackEquiv familyQuotient_isLocalDiffeomorph x
      (descendedWeightedSection C (familyQuotient x)) = upstairsWeightedSection C x :=
  SectionsDescent.pullback_descendedSection familyQuotient_isLocalDiffeomorph
    familyQuotient_surjective (upstairsWeightedSection C) (weightedCompatible C hinv) x

theorem descendedWeightedSection_ne_zero (C : TriangleRegularPoint → ℂ)
    (hinv : WeightedInvariant C) (hne : ∀ z, C z ≠ 0)
    (y : Threefold.SpecialRegularFamily) : descendedWeightedSection C y ≠ 0 := by
  obtain ⟨x, rfl⟩ := familyQuotient_surjective y
  exact (SectionsDescent.descendedSection_ne_zero_iff_at_image
    familyQuotient_isLocalDiffeomorph familyQuotient_surjective (upstairsWeightedSection C)
      (weightedCompatible C hinv) x).mpr
        ((upstairsWeightedSection_ne_zero_iff C x).mpr (hne x.1))

theorem descendedWeightedSection_unique (C : TriangleRegularPoint → ℂ)
    (hinv : WeightedInvariant C)
    (t : ∀ y : Threefold.SpecialRegularFamily, Regular.bundle.Fiber y)
    (ht : ∀ x, Pullback.pullbackEquiv familyQuotient_isLocalDiffeomorph x
      (t (familyQuotient x)) = upstairsWeightedSection C x) :
    t = descendedWeightedSection C :=
  SectionsDescent.descendedSection_unique familyQuotient_isLocalDiffeomorph
    familyQuotient_surjective (upstairsWeightedSection C) (weightedCompatible C hinv) t ht

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalRegular
