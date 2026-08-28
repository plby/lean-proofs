import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # A native diffeomorphism restricts to a diffeomorphism of an open set and its actual image -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.OpenDiffeomorph

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]

def imageOpen (e : Diffeomorph I J X Y ∞) (U : Opens X) : Opens Y :=
  ⟨e '' (U : Set X), e.toHomeomorph.isOpenMap _ U.isOpen⟩

/-- Both directions retain the original smooth structures on the open submanifolds. -/
def imageDiffeomorph (e : Diffeomorph I J X Y ∞) (U : Opens X) :
    Diffeomorph I J U (imageOpen e U) ∞ := by
  let h : U ≃ₜ imageOpen e U := e.toHomeomorph.image U
  refine {
    toEquiv := h.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (imageOpen e U) h).mp
    exact e.contMDiff.comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff U h.symm).mp
    exact e.symm.contMDiff.comp contMDiff_subtype_val

theorem imageDiffeomorph_coe (e : Diffeomorph I J X Y ∞) (U : Opens X) (x : U) :
    (imageDiffeomorph e U x : Y) = e (x : X) := rfl

theorem imageDiffeomorph_symm_coe (e : Diffeomorph I J X Y ∞) (U : Opens X)
    (y : imageOpen e U) : ((imageDiffeomorph e U).symm y : X) = e.symm (y : Y) := rfl

end Wikipedia.SmoothSixDPoincare.OpenDiffeomorph
