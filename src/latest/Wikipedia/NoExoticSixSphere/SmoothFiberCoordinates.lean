import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth invertible fiber-coordinate changes

Both operator families are smooth in the given base atlas. Their actions
give mutually inverse smooth maps of the full product, with the base fixed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M K : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  (L : M → K ≃L[ℝ] K)
  (hL : ContMDiff I 𝓘(ℝ, K →L[ℝ] K) ∞ (fun p ↦ (L p).toContinuousLinearMap))
  (hLi : ContMDiff I 𝓘(ℝ, K →L[ℝ] K) ∞ (fun p ↦ (L p).symm.toContinuousLinearMap))

def fiberCoordinatesDiffeomorph :
    Diffeomorph (I.prod 𝓘(ℝ, K)) (I.prod 𝓘(ℝ, K)) (M × K) (M × K) ∞ where
  toEquiv := {
    toFun := fun p ↦ (p.1, L p.1 p.2)
    invFun := fun p ↦ (p.1, (L p.1).symm p.2)
    left_inv p := Prod.ext rfl ((L p.1).symm_apply_apply p.2)
    right_inv p := Prod.ext rfl ((L p.1).apply_symm_apply p.2) }
  contMDiff_toFun :=
    contMDiff_fst.prodMk ((hL.comp contMDiff_fst).clm_apply contMDiff_snd)
  contMDiff_invFun :=
    contMDiff_fst.prodMk ((hLi.comp contMDiff_fst).clm_apply contMDiff_snd)

theorem fiberCoordinatesDiffeomorph_apply (p : M × K) :
    fiberCoordinatesDiffeomorph L hL hLi p = (p.1, L p.1 p.2) := rfl

theorem fiberCoordinatesDiffeomorph_symm_apply (p : M × K) :
    (fiberCoordinatesDiffeomorph L hL hLi).symm p = (p.1, (L p.1).symm p.2) := rfl

end NoExoticSixSphere
