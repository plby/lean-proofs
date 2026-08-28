import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphImage

/-! # Equal open subsets have the same native smooth structure and point coordinates -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.OpenDiffeomorph

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]

def setCongr (U V : Opens X) (h : (U : Set X) = V) : Diffeomorph I I U V ∞ where
  toEquiv := (Homeomorph.setCongr h).toEquiv
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff V _).mp contMDiff_subtype_val
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff U _).mp contMDiff_subtype_val

theorem setCongr_coe (U V : Opens X) (h : (U : Set X) = V) (x : U) :
    (setCongr (I := I) U V h x).val = x.val := rfl

theorem setCongr_symm_coe (U V : Opens X) (h : (U : Set X) = V) (y : V) :
    ((setCongr (I := I) U V h).symm y).val = y.val := rfl

end Wikipedia.SmoothSixDPoincare.OpenDiffeomorph
