import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeLocalSmooth
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFunctions

/-!
# An actual smooth section on the original full inverse image

The input family is defined only over its smaller open base. The output
is a section of the existing native smooth-function sheaf on the literal
`Zero.basePreimage` in the original total space. Its zero extension agrees
with the named ambient scalar, but no smoothness of that extension across
the boundary is asserted.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local

open FourierParameter HolomorphicDolbeaultThree PeriodTorusLineBundleClassification
open PeriodFamilyHigherDirectImage

variable {U V : Opens ℂ} (P : HolomorphicPeriodMap ℂ U) (hVU : V ≤ U)

/-- The genuine native smooth section on the original smaller-base full inverse image. -/
def smoothSection (f : SmoothFamily V (Fin 4)) :
    letI := P.totalChartedSpace
    Functions.SmoothSection Model P.TotalSpace (Zero.basePreimage P (baseOpen U V)) := by
  let := P.totalChartedSpace
  exact Functions.sectionOfSmooth Model P.TotalSpace (preimageOpen P V) (ambientScalar P f)
    (ambientScalar_contMDiffAt P hVU f)

/-- Literal values on the original total-space open, with the base point in the smaller open. -/
theorem smoothSection_apply (f : SmoothFamily V (Fin 4)) (x : preimageOpen P V) :
    letI := P.totalChartedSpace
    smoothSection P hVU f x =
      f (⟨(x.val.1 : ℂ), x.property⟩, unitTorusMark x.val.2) := by
  let := P.totalChartedSpace
  exact ambientScalar_apply P f (x : P.TotalSpace) x.property

/-- The section is evaluated on the actual original quotient map over the smaller base. -/
theorem smoothSection_quotientMap (f : SmoothFamily V (Fin 4))
    (b : V) (z : ComplexPlane₂) :
    letI := P.totalChartedSpace
    smoothSection P hVU f (coverPoint P hVU b z) =
      f (b, torusQuotient ((P.periodEquiv (Set.inclusion hVU b)).symm z)) := by
  let := P.totalChartedSpace
  exact ambientScalar_coverPoint P hVU f b z

/-- Equality of the two ambient representatives; their smoothness is only local to the open. -/
theorem extend_smoothSection (f : SmoothFamily V (Fin 4)) :
    letI := P.totalChartedSpace
    Functions.extend Model P.TotalSpace (preimageOpen P V) (smoothSection P hVU f) =
      ambientScalar P f := by
  let := P.totalChartedSpace
  classical
  funext x
  by_cases hx : x ∈ preimageOpen P V
  · rw [Functions.extend_apply Model P.TotalSpace (preimageOpen P V)
      (smoothSection P hVU f) x hx]
    rfl
  · simp only [Functions.extend, ambientScalar, ambientValue, dif_neg hx]

/-- The actual sheaf section's ambient representative pulls back to the original local formula. -/
theorem extend_smoothSection_comp_quotientMap (f : SmoothFamily V (Fin 4)) :
    letI := P.totalChartedSpace
    Functions.extend Model P.TotalSpace (preimageOpen P V) (smoothSection P hVU f) ∘
      P.quotientMap = upstairs P f := by
  let := P.totalChartedSpace
  rw [extend_smoothSection, ambientScalar_comp_quotientMap]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local
