import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCohomologyLinear
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeGeometry
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroDerived

/-!
# Unconditional native degree-one Dolbeault comparison for period families

Every instance below is proved for the original `P.totalChartedSpace`.
The target is the already existing `Zero.totalAdditiveSheaf P`; its
identity with the coefficient sheaf in the native construction is
definitional.  No cohomology or local-solvability hypothesis is supplied.
-/

noncomputable section

open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Family

open CuspNormalization.SheafCohomology

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local instance nativeChartedSpace : ChartedSpace Model P.TotalSpace := P.totalChartedSpace
local instance nativeComplexManifold : IsManifold 𝓘(ℂ, Model) ω P.TotalSpace :=
  P.totalSpace_isManifold
local instance nativeRealManifold : IsManifold 𝓘(ℝ, Model) ∞ P.TotalSpace :=
  Geometry.totalSpace_realManifold P
local instance nativeT2 : T2Space P.TotalSpace := Geometry.totalSpace_t2 P
local instance nativeSigmaCompact : SigmaCompactSpace P.TotalSpace :=
  Geometry.totalSpace_sigmaCompact P

/-- The original coefficient sheaf is retained exactly, not just up to a
chosen equivalence of cohomology groups. -/
theorem totalHolomorphicSheaf_eq :
    Functions.holomorphicSheaf Model P.TotalSpace =
      PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P := rfl

abbrev TotalClosedForms := Cohomology.GlobalClosed P.TotalSpace
abbrev TotalSmoothFunctions := Cohomology.GlobalSmooth P.TotalSpace
abbrev TotalDolbeaultH1 := Cohomology.DolbeaultH1 P.TotalSpace

local instance nativeH1Module : Module ℂ
    (CategoryTheory.Sheaf.H.{0} (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) 1) :=
  Cohomology.h1Module P.TotalSpace

/-- The original native positive connecting map for the actual family sheaf. -/
def totalClassMap : TotalClosedForms P →+
    CategoryTheory.Sheaf.H.{0} (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) 1 :=
  Cohomology.classMap P.TotalSpace

/-- Every actual class on the original family is represented by a genuine
global smooth closed native `(0,1)` form. -/
theorem totalClassMap_surjective : Function.Surjective (totalClassMap P) :=
  Cohomology.classMap_surjective P.TotalSpace

/-- A native representative is zero exactly when it is the actual
antiholomorphic derivative of an actual global smooth function. -/
theorem totalClassMap_eq_zero_iff (s : TotalClosedForms P) :
    totalClassMap P s = 0 ↔ ∃ f : TotalSmoothFunctions P,
      NativeDifferential.closedSection Model P.TotalSpace ⊤ f = s :=
  Cohomology.classMap_eq_zero_iff P.TotalSpace s

/-- The original sheaf-induced scalar action, written as its actual
cohomology map, not transported through the form comparison. -/
theorem totalH1_smul (c : ℂ)
    (a : CategoryTheory.Sheaf.H.{0}
      (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) 1) :
    c • a = CategoryTheory.Sheaf.H.map
      (holomorphicScalarEnd 𝓘(ℂ, Model) P.TotalSpace c) 1 a := rfl

/-- The unconditional native complex-linear Dolbeault comparison for the
original period-family total space and its already existing sheaf. -/
def totalLinearEquiv : TotalDolbeaultH1 P ≃ₗ[ℂ]
    CategoryTheory.Sheaf.H.{0} (PeriodFamilyHigherDirectImage.Zero.totalAdditiveSheaf P) 1 :=
  Cohomology.linearEquiv P.TotalSpace

@[simp] theorem totalLinearEquiv_mk (s : TotalClosedForms P) :
    totalLinearEquiv P (Submodule.Quotient.mk s) = totalClassMap P s :=
  Cohomology.linearEquiv_mk P.TotalSpace s

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Family
