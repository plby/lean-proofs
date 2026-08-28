import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeLocalBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeLocalPullback
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeLocalDescent
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisNativeSmooth

/-!
# Native smoothness on the original smaller-base total-space inverse image

The actual local scalar and its actual covering pullback agree everywhere
as ambient functions. The pullback is smooth only above the smaller base;
open-set descent through the original quotient local inverses proves
smoothness precisely on the original full inverse image of that base.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local

open FourierParameter HolomorphicDolbeaultThree

variable {U V : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

local notation "IR" => modelWithCornersSelf ℝ Model
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

local instance nativeLocalCoverChartedSpace : ChartedSpace Model (U × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

/-- Exact equality of the two original ambient functions, without boundary regularity. -/
theorem ambientScalar_comp_quotientMap (f : SmoothFamily V (Fin 4)) :
    ambientScalar P f ∘ P.quotientMap = upstairs P f := by
  funext q
  exact (ambientScalar_quotientMap P f q.1 q.2).trans (upstairs_apply P f q).symm

/-- Real smoothness on the original open subset, in precisely `P.totalChartedSpace`. -/
theorem ambientScalar_contMDiffOn (hVU : V ≤ U) (f : SmoothFamily V (Fin 4)) :
    letI := P.totalChartedSpace
    ContMDiffOn IR IR₁ ∞ (ambientScalar P f) (preimageOpen P V) := by
  let := P.totalChartedSpace
  apply contMDiffOn_of_comp_real_localDiffeomorph
    (FourierSynthesisNative.quotientMap_real_isLocalDiffeomorph P)
    P.quotientMap_surjective (preimageOpen P V).isOpen
  rw [ambientScalar_comp_quotientMap, quotientMap_preimage]
  exact upstairs_contMDiffOn P hVU f

/-- Every point of the original inverse image has the genuine native smooth scalar germ. -/
theorem ambientScalar_contMDiffAt (hVU : V ≤ U) (f : SmoothFamily V (Fin 4))
    (x : P.TotalSpace) (hx : x ∈ preimageOpen P V) :
    letI := P.totalChartedSpace
    ContMDiffAt IR IR₁ ∞ (ambientScalar P f) x := by
  let := P.totalChartedSpace
  exact (ambientScalar_contMDiffOn P hVU f).contMDiffAt
    ((preimageOpen P V).isOpen.mem_nhds hx)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative.Local
