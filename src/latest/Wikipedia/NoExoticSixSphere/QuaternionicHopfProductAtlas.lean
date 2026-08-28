import Wikipedia.NoExoticSixSphere.QuaternionicHopfProductFrame
import Wikipedia.SmoothSixDPoincare.BoundarylessModelChange

/-!
# Six-dimensional Euclidean charts for the original product of Hopf fibers

The new charts concatenate the two original three-dimensional chart
coordinates. Both identity maps are smooth, so this is a proved change of
model for the original product smooth structure, not a replacement by an
unrelated atlas.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.SmoothSixDPoincare

def southPairModelCoordinates : (V 3 × V 3) ≃L[ℝ] V 6 :=
  EuclideanSpace.finAddEquivProd.symm

def southPairModelChart :
    PartialDiffeomorph 𝓘(ℝ, V 3 × V 3) (𝓡 6) (V 3 × V 3) (V 6) ∞ :=
  southPairModelCoordinates.toDiffeomorph.toPartialDiffeomorph

theorem southPairModelChart_source : southPairModelChart.source = Set.univ := rfl

@[instance_reducible]
def southPairEuclideanAtlas : ChartedSpace (V 6) (Sphere 3 × Sphere 3) :=
  BoundarylessModelChange.chartedSpace (I := (𝓡 3).prod (𝓡 3))
    southPairModelChart southPairModelChart_source

theorem southPairEuclideanIsManifold :
    letI := southPairEuclideanAtlas; IsManifold (𝓡 6) ∞ (Sphere 3 × Sphere 3) :=
  BoundarylessModelChange.isManifold (I := (𝓡 3).prod (𝓡 3))
    southPairModelChart southPairModelChart_source

def southPairEuclideanToProduct :
    letI := southPairEuclideanAtlas;
    Diffeomorph (𝓡 6) ((𝓡 3).prod (𝓡 3)) (Sphere 3 × Sphere 3) (Sphere 3 × Sphere 3) ∞ :=
  BoundarylessModelChange.diffeomorph (I := (𝓡 3).prod (𝓡 3))
    southPairModelChart southPairModelChart_source

theorem southPairEuclideanToProduct_apply (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas; southPairEuclideanToProduct p = p := rfl

theorem southPairEuclideanToProduct_symm_apply (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas; southPairEuclideanToProduct.symm p = p := rfl

theorem contMDiff_southPairAmbient_euclidean :
    letI := southPairEuclideanAtlas;
    ContMDiff (𝓡 6) 𝓘(ℝ, SouthPairAmbientModel) ∞ southPairAmbient := by
  let _ := southPairEuclideanAtlas
  have h := contMDiff_southPairAmbient.comp southPairEuclideanToProduct.contMDiff
  exact h

section Differential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {i : Sphere 3 × Sphere 3 → E}
  (hi : ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, E) ∞ i)

include hi

theorem southPairEuclidean_ambientDifferential (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    NormalFrameOfEquations.ambientDifferential (𝓡 6) i p =
      (NormalFrameOfEquations.ambientDifferential ((𝓡 3).prod (𝓡 3)) i p).comp
        (mfderiv (𝓡 6) ((𝓡 3).prod (𝓡 3)) southPairEuclideanToProduct p) := by
  let _ := southPairEuclideanAtlas
  change mfderiv (𝓡 6) 𝓘(ℝ, E) (i ∘ southPairEuclideanToProduct) p = _
  exact mfderiv_comp p (hi.mdifferentiableAt (by simp))
    (southPairEuclideanToProduct.contMDiff.mdifferentiableAt (by simp))

theorem southPairEuclidean_tangentRange (p : Sphere 3 × Sphere 3) :
    letI := southPairEuclideanAtlas;
    (NormalFrameOfEquations.ambientDifferential (𝓡 6) i p).range =
      (NormalFrameOfEquations.ambientDifferential ((𝓡 3).prod (𝓡 3)) i p).range := by
  let _ := southPairEuclideanAtlas
  rw [southPairEuclidean_ambientDifferential hi]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    (southPairEuclideanToProduct.mfderivToContinuousLinearEquiv (by simp) p).surjective)

theorem southPairEuclidean_differential_injective (p : Sphere 3 × Sphere 3)
    (hp : Function.Injective
      (NormalFrameOfEquations.ambientDifferential ((𝓡 3).prod (𝓡 3)) i p)) :
    letI := southPairEuclideanAtlas;
    Function.Injective (NormalFrameOfEquations.ambientDifferential (𝓡 6) i p) := by
  let _ := southPairEuclideanAtlas
  rw [southPairEuclidean_ambientDifferential hi]
  exact hp.comp
    (southPairEuclideanToProduct.mfderivToContinuousLinearEquiv (by simp) p).injective

end Differential

end NoExoticSixSphere.QuaternionicHopf
