import Wikipedia.HopfProblem.HolomorphicDolbeaultThreePeriodFamily

/-!
# Native degree-one Dolbeault comparison on actual family opens

Every actual open subset inherits the original varying-period complex
atlas.  Its topology and smooth-function acyclicity are proved, so the
genuine cohomology comparison needs no extra premises.  This includes
the literal full inverse image of every original base open set.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Family.OpenSets

open CuspNormalization.SheafCohomology

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U) (Ω : Opens P.TotalSpace)

local instance nativeChartedSpace : ChartedSpace Model P.TotalSpace := P.totalChartedSpace
local instance nativeComplexManifold : IsManifold 𝓘(ℂ, Model) ω P.TotalSpace :=
  P.totalSpace_isManifold
local instance nativeRealManifold : IsManifold 𝓘(ℝ, Model) ∞ P.TotalSpace :=
  Geometry.totalSpace_realManifold P
local instance openT2 : T2Space Ω := Geometry.open_t2 P Ω
local instance openSigmaCompact : SigmaCompactSpace Ω := Geometry.open_sigmaCompact P Ω

/-- The actual holomorphic sheaf on the inherited original open manifold. -/
abbrev coefficientSheaf := HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, Model) Ω

abbrev ClosedForms := Cohomology.GlobalClosed Ω
abbrev SmoothFunctions := Cohomology.GlobalSmooth Ω
abbrev DolbeaultH1 := Cohomology.DolbeaultH1 Ω

local instance openH1Module : Module ℂ (CategoryTheory.Sheaf.H.{0} (coefficientSheaf P Ω) 1) :=
  Cohomology.h1Module Ω

/-- The original positive connecting class on an actual family open. -/
def classMap : ClosedForms P Ω →+ CategoryTheory.Sheaf.H.{0} (coefficientSheaf P Ω) 1 :=
  Cohomology.classMap Ω

theorem classMap_surjective : Function.Surjective (classMap P Ω) :=
  Cohomology.classMap_surjective Ω

theorem classMap_eq_zero_iff (s : ClosedForms P Ω) :
    classMap P Ω s = 0 ↔ ∃ f : SmoothFunctions P Ω,
      NativeDifferential.closedSection Model Ω ⊤ f = s :=
  Cohomology.classMap_eq_zero_iff Ω s

/-- The actual complex action on the original open cohomology group. -/
theorem h1_smul (c : ℂ) (a : CategoryTheory.Sheaf.H.{0} (coefficientSheaf P Ω) 1) :
    c • a = CategoryTheory.Sheaf.H.map (holomorphicScalarEnd 𝓘(ℂ, Model) Ω c) 1 a := rfl

/-- The genuine complex-linear comparison on the inherited original open. -/
def linearEquiv : DolbeaultH1 P Ω ≃ₗ[ℂ]
    CategoryTheory.Sheaf.H.{0} (coefficientSheaf P Ω) 1 :=
  Cohomology.linearEquiv Ω

@[simp] theorem linearEquiv_mk (s : ClosedForms P Ω) :
    linearEquiv P Ω (Submodule.Quotient.mk s) = classMap P Ω s :=
  Cohomology.linearEquiv_mk Ω s

variable (A : Opens U)

/-- In particular, the literal full inverse image of any base open has
actual smooth closed-form representatives for every native `H¹(O)` class. -/
theorem basePreimage_classMap_surjective :
    Function.Surjective (classMap P (PeriodFamilyHigherDirectImage.Zero.basePreimage P A)) :=
  classMap_surjective P (PeriodFamilyHigherDirectImage.Zero.basePreimage P A)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Family.OpenSets
