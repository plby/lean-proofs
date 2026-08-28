import Wikipedia.NoExoticSixSphere.QuaternionicHopfSmoothCollapseData
import Wikipedia.NoExoticSixSphere.ProductThirdHomologyFactors

/-!
# The actual two factor spheres in the compatible Euclidean atlas

Both maps are the original factor inclusions. Their smoothness and
injective native differentials are proved through the already checked
identity diffeomorphism, retaining the actual source tangent frames.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

local instance : ChartedSpace (V 6) (Sphere 3 × Sphere 3) := southPairEuclideanAtlas

def southPairLeftSphere : C(Sphere 3, Sphere 3 × Sphere 3) :=
  ProductThirdHomology.leftSection (spherePole 3)

def southPairRightSphere : C(Sphere 3, Sphere 3 × Sphere 3) :=
  ProductThirdHomology.rightSection (spherePole 3)

theorem southPairLeftSphere_apply (s : Sphere 3) : southPairLeftSphere s = (s, spherePole 3) := rfl

theorem southPairRightSphere_apply (s : Sphere 3) :
    southPairRightSphere s = (spherePole 3, s) := rfl

theorem contMDiff_southPairLeftSphere_product :
    ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ southPairLeftSphere :=
  contMDiff_id.prodMk (contMDiff_const (c := spherePole 3))

theorem contMDiff_southPairRightSphere_product :
    ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ southPairRightSphere :=
  (contMDiff_const (c := spherePole 3)).prodMk contMDiff_id

theorem contMDiff_southPairLeftSphere : ContMDiff (𝓡 3) (𝓡 6) ∞ southPairLeftSphere := by
  have h := southPairEuclideanToProduct.symm.contMDiff.comp contMDiff_southPairLeftSphere_product
  exact h

theorem contMDiff_southPairRightSphere : ContMDiff (𝓡 3) (𝓡 6) ∞ southPairRightSphere := by
  have h := southPairEuclideanToProduct.symm.contMDiff.comp contMDiff_southPairRightSphere_product
  exact h

theorem southPairLeftSphere_injective : Function.Injective southPairLeftSphere := by
  intro s t h
  exact congrArg Prod.fst h

theorem southPairRightSphere_injective : Function.Injective southPairRightSphere := by
  intro s t h
  exact congrArg Prod.snd h

theorem southPairLeftSphere_derivative (s : Sphere 3) :
    mfderiv (𝓡 3) (𝓡 6) southPairLeftSphere s =
      (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 6)
        southPairEuclideanToProduct.symm (s, spherePole 3)).comp
          (ContinuousLinearMap.inl ℝ (V 3) (V 3)) := by
  have hp : (mfderiv (𝓡 3) ((𝓡 3).prod (𝓡 3)) southPairLeftSphere s :
      V 3 →L[ℝ] (V 3 × V 3)) = ContinuousLinearMap.inl ℝ (V 3) (V 3) :=
    mfderiv_prod_left
  have h := mfderiv_comp s
    (southPairEuclideanToProduct.symm.contMDiff.mdifferentiableAt (by simp))
    (contMDiff_southPairLeftSphere_product.mdifferentiableAt (by simp))
  exact h.trans (congrArg (fun L : V 3 →L[ℝ] (V 3 × V 3) ↦
    (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 6)
      southPairEuclideanToProduct.symm (s, spherePole 3)).comp L) hp)

theorem southPairRightSphere_derivative (s : Sphere 3) :
    mfderiv (𝓡 3) (𝓡 6) southPairRightSphere s =
      (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 6)
        southPairEuclideanToProduct.symm (spherePole 3, s)).comp
          (ContinuousLinearMap.inr ℝ (V 3) (V 3)) := by
  have hp : (mfderiv (𝓡 3) ((𝓡 3).prod (𝓡 3)) southPairRightSphere s :
      V 3 →L[ℝ] (V 3 × V 3)) = ContinuousLinearMap.inr ℝ (V 3) (V 3) :=
    mfderiv_prod_right
  have h := mfderiv_comp s
    (southPairEuclideanToProduct.symm.contMDiff.mdifferentiableAt (by simp))
    (contMDiff_southPairRightSphere_product.mdifferentiableAt (by simp))
  exact h.trans (congrArg (fun L : V 3 →L[ℝ] (V 3 × V 3) ↦
    (mfderiv ((𝓡 3).prod (𝓡 3)) (𝓡 6)
      southPairEuclideanToProduct.symm (spherePole 3, s)).comp L) hp)

theorem southPairLeftSphere_differential_injective (s : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 6) southPairLeftSphere s) := by
  rw [southPairLeftSphere_derivative]
  apply (southPairEuclideanToProduct.symm.mfderivToContinuousLinearEquiv
    (by simp) (s, spherePole 3)).injective.comp
  intro v w h
  exact congrArg Prod.fst h

theorem southPairRightSphere_differential_injective (s : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 6) southPairRightSphere s) := by
  rw [southPairRightSphere_derivative]
  apply (southPairEuclideanToProduct.symm.mfderivToContinuousLinearEquiv
    (by simp) (spherePole 3, s)).injective.comp
  intro v w h
  exact congrArg Prod.snd h

end NoExoticSixSphere.QuaternionicHopf
