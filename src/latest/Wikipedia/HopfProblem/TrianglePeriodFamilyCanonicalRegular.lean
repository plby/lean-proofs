import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalForms
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLocalFrames
import Wikipedia.HopfProblem.SpecialPeriodsExistence

/-!
# Canonical forms for the actual special regular family

All period and covariance inputs in this file are the constructed special
periods.  On the actual varying lattice quotient over the regular domain,
there is a genuine nowhere-zero holomorphic canonical form, with the exact
triangle-generator pullbacks computed below.  On the further triangle
quotient, the genuine canonical bundle has the constructed holomorphic
local frames of its actual tangent atlas.

The upstairs form is not asserted to be triangle-invariant.  No extension
across the later fillings, or global canonical-bundle conclusion for the
compact threefold, is asserted here.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

open SpecialPeriods

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

/-- The actual special period family restricted to the actual free locus. -/
abbrev specialRegularData : Data ℂ TriangleRegularPoint :=
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The varying lattice quotient before the final triangle-group quotient. -/
abbrev SpecialRegularUpstairs := specialRegularData.TotalSpace

/-- The actual regular triangle-quotient family. -/
abbrev SpecialRegularFamily := specialRegularData.Space

/-- The genuine canonical bundle on the upstairs regular period family. -/
abbrev specialUpstairsCanonicalBundle := familyCanonicalBundle specialRegularData.periods

def specialUpstairsCanonicalVolume (x : SpecialRegularUpstairs) :
    specialUpstairsCanonicalBundle.Fiber x :=
  familyCanonicalVolume specialRegularData.periods x

theorem specialUpstairsCanonicalVolume_ne_zero (x : SpecialRegularUpstairs) :
    specialUpstairsCanonicalVolume x ≠ 0 :=
  familyCanonicalVolume_ne_zero specialRegularData.periods x

theorem specialUpstairsCanonicalVolume_holomorphic :
    letI := specialRegularData.periods.totalChartedSpace
    ContMDiff I₃ ((I₃).prod I₁) ω
      (fun x => (⟨x, specialUpstairsCanonicalVolume x⟩ :
        specialUpstairsCanonicalBundle.TotalSpace)) :=
  familyCanonicalVolume_holomorphic (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply specialRegularData.periods

/-- The canonical form as a genuine covector on the actual tangent space. -/
def specialUpstairsForm (x : SpecialRegularUpstairs) :
    letI := specialRegularData.periods.totalChartedSpace
    (TangentSpace I₃ x) [⋀^(Fin 3)]→L[ℂ] ℂ :=
  familyCanonicalIntrinsicEquiv specialRegularData.periods x (specialUpstairsCanonicalVolume x)

theorem specialUpstairsForm_ne_zero (x : SpecialRegularUpstairs) :
    specialUpstairsForm x ≠ 0 := by
  intro h
  apply specialUpstairsCanonicalVolume_ne_zero x
  apply (familyCanonicalIntrinsicEquiv specialRegularData.periods x).injective
  rw [map_zero]
  exact h

/-- A genuine analytic, base-preserving, fibrewise-linear trivialization
of this actual upstairs canonical bundle. -/
def specialUpstairsCanonicalTrivialization :
    letI := specialRegularData.periods.totalChartedSpace
    Diffeomorph ((I₃).prod I₁) ((I₃).prod I₁)
      specialUpstairsCanonicalBundle.TotalSpace (SpecialRegularUpstairs × ℂ) ω :=
  familyCanonicalTrivialization (fun z : TriangleRegularPoint => (z.val : ℂ))
    regularPoint_chart_apply specialRegularData.periods

/-- The first generator's exact intrinsic pullback, including its sign. -/
theorem specialUpstairsForm_generator₁ (x : SpecialRegularUpstairs) :
    letI := specialRegularData.periods.totalChartedSpace
    (specialUpstairsForm
      (familyMap specialRegularData triangleGenerator₁ x)).compContinuousLinearMap
        (mfderiv I₃ I₃ (familyMap specialRegularData triangleGenerator₁) x) =
        (((((x.1.val : ℂ) + 1) ^ 2)⁻¹) * (-1 / specialTau x.1.val)) •
          specialUpstairsForm x :=
  familyCanonicalVolume_pullback_generator₁ specialRegularData x

/-- The second generator's exact intrinsic pullback. -/
theorem specialUpstairsForm_generator₂ (x : SpecialRegularUpstairs) :
    letI := specialRegularData.periods.totalChartedSpace
    (specialUpstairsForm
      (familyMap specialRegularData triangleGenerator₂ x)).compContinuousLinearMap
        (mfderiv I₃ I₃ (familyMap specialRegularData triangleGenerator₂) x) =
        (((((x.1.val : ℂ) + (Triangle.width : ℂ)) ^ 2)⁻¹) *
          (1 / specialTau x.1.val)) • specialUpstairsForm x :=
  familyCanonicalVolume_pullback_generator₂ specialRegularData x

/-- The actual cusp translation preserves the full upstairs canonical form. -/
theorem specialUpstairsForm_cusp (x : SpecialRegularUpstairs) :
    letI := specialRegularData.periods.totalChartedSpace
    (specialUpstairsForm
      (familyMap specialRegularData triangleCuspGenerator x)).compContinuousLinearMap
        (mfderiv I₃ I₃ (familyMap specialRegularData triangleCuspGenerator) x) =
          specialUpstairsForm x :=
  familyCanonicalVolume_pullback_cusp specialRegularData x

private theorem specialRegularCovering :
    IsQuotientCoveringMap specialRegularData.baseQuotient TriangleGroup :=
  regularCovering specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The native analytic quotient atlas on the actual regular family. -/
@[instance_reducible] def specialRegularCanonicalChartedSpace :
    ChartedSpace Model SpecialRegularFamily :=
  specialRegularData.chartedSpace specialRegularCovering

theorem specialRegularCanonicalIsManifold :
    letI := specialRegularCanonicalChartedSpace
    IsManifold I₃ ω SpecialRegularFamily :=
  specialRegularData.isManifold specialRegularCovering

/-- The descended regular family's actual canonical bundle.  Its
transitions are the inverse determinants of its actual tangent charts. -/
abbrev specialRegularCanonicalBundle :=
  letI := specialRegularCanonicalChartedSpace
  letI := specialRegularCanonicalIsManifold
  Atlas.core SpecialRegularFamily

theorem specialRegularCanonicalBundle_holomorphic :
    letI := specialRegularCanonicalChartedSpace
    ContMDiffVectorBundle ω ℂ specialRegularCanonicalBundle.Fiber I₃ := by
  let := specialRegularCanonicalChartedSpace
  let := specialRegularCanonicalIsManifold
  exact Atlas.holomorphicVectorBundle SpecialRegularFamily

/-- Identification with the full top-covector space on the actual
regular quotient's tangent space, not with a merely named formal line. -/
def specialRegularCanonicalIntrinsicEquiv (x : SpecialRegularFamily) :
    letI := specialRegularCanonicalChartedSpace
    specialRegularCanonicalBundle.Fiber x ≃L[ℂ]
      (TangentSpace I₃ x) [⋀^(Fin 3)]→L[ℂ] ℂ :=
  letI := specialRegularCanonicalChartedSpace
  letI := specialRegularCanonicalIsManifold
  Atlas.intrinsicEquiv SpecialRegularFamily x

/-- The natural open domain of a preferred chart on the actual quotient. -/
abbrev specialRegularCanonicalChartSource (i : SpecialRegularFamily) :
    TopologicalSpace.Opens SpecialRegularFamily :=
  letI := specialRegularCanonicalChartedSpace
  Atlas.chartSource SpecialRegularFamily (achart Model i)

def specialRegularCanonicalLocalFrame (i : SpecialRegularFamily)
    (x : specialRegularCanonicalChartSource i) : specialRegularCanonicalBundle.Fiber x.val :=
  letI := specialRegularCanonicalChartedSpace
  letI := specialRegularCanonicalIsManifold
  Atlas.localFrame SpecialRegularFamily (achart Model i) x

theorem specialRegularCanonicalLocalFrame_ne_zero (i : SpecialRegularFamily)
    (x : specialRegularCanonicalChartSource i) : specialRegularCanonicalLocalFrame i x ≠ 0 := by
  let := specialRegularCanonicalChartedSpace
  let := specialRegularCanonicalIsManifold
  exact Atlas.localFrame_ne_zero SpecialRegularFamily (achart Model i) x

theorem specialRegularCanonicalLocalFrame_holomorphic (i : SpecialRegularFamily) :
    letI := specialRegularCanonicalChartedSpace
    ContMDiff I₃ ((I₃).prod I₁) ω
      (fun x : specialRegularCanonicalChartSource i =>
        (⟨x.val, specialRegularCanonicalLocalFrame i x⟩ :
          specialRegularCanonicalBundle.TotalSpace)) := by
  let := specialRegularCanonicalChartedSpace
  let := specialRegularCanonicalIsManifold
  exact Atlas.localFrameSection_holomorphic SpecialRegularFamily (achart Model i)

theorem specialRegularCanonicalLocalFrame_inCoordinates (i : SpecialRegularFamily)
    (x : specialRegularCanonicalChartSource i) :
    letI := specialRegularCanonicalChartedSpace
    letI := specialRegularCanonicalIsManifold
    Atlas.inCoordinates SpecialRegularFamily (achart Model i) x.val
      (specialRegularCanonicalLocalFrame i x) = volume := by
  let := specialRegularCanonicalChartedSpace
  let := specialRegularCanonicalIsManifold
  exact Atlas.localFrame_inCoordinates SpecialRegularFamily (achart Model i) x

theorem specialRegularCanonicalLocalFrames_cover (x : SpecialRegularFamily) :
    ∃ i, x ∈ specialRegularCanonicalChartSource i := by
  let := specialRegularCanonicalChartedSpace
  exact ⟨x, mem_chart_source Model x⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
