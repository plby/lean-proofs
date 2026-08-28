import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeSmooth
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFunctions

/-!
# The genuine native smooth section of the descended scalar

The descended scalar defines an actual section of the existing smooth
function sheaf in the original period-family atlas. Restrictions are the
literal restrictions of that function. Its global section has exactly
the original scalar as its ambient representative, and its pullback to
the original cover is the original inverse-period formula.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative

open FourierParameter HolomorphicDolbeaultThree PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- An actual smooth-function section on any original total-space open. -/
def smoothSection (f : SmoothFamily U (Fin 4)) (A : Opens P.TotalSpace) :
    letI := P.totalChartedSpace
    Functions.SmoothSection Model P.TotalSpace A := by
  let := P.totalChartedSpace
  exact Functions.sectionOfSmooth Model P.TotalSpace A (scalar P f)
    (fun x _ => scalar_contMDiff P f x)

@[simp] theorem smoothSection_apply (f : SmoothFamily U (Fin 4))
    (A : Opens P.TotalSpace) (x : A) :
    letI := P.totalChartedSpace
    smoothSection P f A x = scalar P f (x : P.TotalSpace) := by
  let := P.totalChartedSpace
  rfl

/-- Restriction uses the original native smooth-function sheaf maps. -/
theorem smoothSection_restrict (f : SmoothFamily U (Fin 4))
    {A B : Opens P.TotalSpace} (hAB : A ≤ B) :
    letI := P.totalChartedSpace
    Functions.restriction Model P.TotalSpace hAB (smoothSection P f B) =
      smoothSection P f A := by
  let := P.totalChartedSpace
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The descended scalar as a genuine global native smooth section. -/
def globalSection (f : SmoothFamily U (Fin 4)) :
    letI := P.totalChartedSpace
    Functions.SmoothSection Model P.TotalSpace ⊤ := by
  let := P.totalChartedSpace
  exact smoothSection P f ⊤

@[simp] theorem globalSection_apply (f : SmoothFamily U (Fin 4)) (x : P.TotalSpace) :
    letI := P.totalChartedSpace
    globalSection P f ⟨x, by trivial⟩ = scalar P f x := by
  let := P.totalChartedSpace
  rfl

/-- The global section's ambient representative is literally the original descended scalar. -/
theorem extend_globalSection (f : SmoothFamily U (Fin 4)) :
    letI := P.totalChartedSpace
    Functions.extend Model P.TotalSpace ⊤ (globalSection P f) = scalar P f := by
  let := P.totalChartedSpace
  funext x
  rw [Functions.extend_apply Model P.TotalSpace ⊤ (globalSection P f) x (by trivial)]
  rfl

/-- Exact values of the genuine global smooth section on the original complex vector cover. -/
theorem globalSection_quotientMap (f : SmoothFamily U (Fin 4))
    (b : U) (z : ComplexPlane₂) :
    letI := P.totalChartedSpace
    globalSection P f ⟨P.quotientMap (b, z), by trivial⟩ =
      f (b, torusQuotient ((P.periodEquiv b).symm z)) := by
  let := P.totalChartedSpace
  rw [globalSection_apply]
  exact scalar_quotientMap P f b z

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative
