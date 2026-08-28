import Wikipedia.NoExoticSixSphere.SphereCollarFrameFactorization
import Wikipedia.NoExoticSixSphere.SphereLinearCollarDerivative

/-!
# Exact source-linear coordinates for the twisted immersion frame

The normal columns stay fixed. The four collar-derivative columns transform
by the given ambient linear isometry. This is a constant source-coordinate
change, which extends over the entire disk regardless of orientation.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere
namespace SphereLinearReparametrization

open GLOrthonormalization StabilizedSpanningDisk

variable (L : Vector 4 ≃ₗᵢ[ℝ] Vector 4)

def sourceBlock (k : ℕ) : Vector ((k + 5) + 4) ≃L[ℝ] Vector ((k + 5) + 4) :=
  EuclideanSpace.finAddEquivProd.trans
    (((ContinuousLinearEquiv.refl ℝ (Vector (k + 5))).prodCongr
      L.toContinuousLinearEquiv).trans EuclideanSpace.finAddEquivProd.symm)

theorem sourceBlock_apply (k : ℕ) (v : Vector ((k + 5) + 4)) :
    sourceBlock L k v = EuclideanSpace.finAddEquivProd.symm
      ((EuclideanSpace.finAddEquivProd v).1,
        L (EuclideanSpace.finAddEquivProd (n := k + 5) (m := 4) v).2) := rfl

theorem collarOperator_precomp {N k : ℕ} (b : Sphere 3) (f : Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (s : Sphere 3) (a : Vector k →L[ℝ] Vector N) :
    OperatorSum.operator (boundaryFrameOperator a)
      (fderiv ℝ (collar b (f ∘ sphereMap L)) s.val) =
      (OperatorSum.operator (boundaryFrameOperator a)
        (fderiv ℝ (collar b f) (sphereMap L s).val)).comp
          (sourceBlock L k).toContinuousLinearMap := by
  rw [fderiv_collar_precomp L b f hf s]
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator (boundaryFrameOperator a)
      ((fderiv ℝ (collar b f) (sphereMap L s).val).comp
        L.toContinuousLinearEquiv.toContinuousLinearMap) v =
    OperatorSum.operator (boundaryFrameOperator a)
      (fderiv ℝ (collar b f) (sphereMap L s).val) (sourceBlock L k v)
  simp only [sourceBlock_apply, OperatorSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  rfl

theorem injective_mfderiv_precomp {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Vector 6) M] (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) (s : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (f ∘ sphereMap L) s) := by
  have hL : ContMDiff (𝓡 3) (𝓡 3) ∞ (sphereMap L) :=
    (sphereDiffeomorph L).contMDiff_toFun
  rw [mfderiv_comp (f := sphereMap L) (g := f) s (hf.mdifferentiableAt (by simp))
    (hL.mdifferentiableAt (by simp))]
  exact (hd _).comp (((sphereDiffeomorph L).mfderivToContinuousLinearEquiv (by simp) s).injective)

end SphereLinearReparametrization

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates SphereLinearReparametrization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (L : Vector 4 ≃ₗᵢ[ℝ] Vector 4) (f : Sphere 3 → M)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

theorem twistedSphereFrame_precomp_linear (s : Sphere 3) :
    twistedBlockMap (e.sphereFrameOperatorMap a (f ∘ sphereMap L)
      (hf.comp (sphereDiffeomorph L).contMDiff_toFun) (injective_mfderiv_precomp L f hf hd)) s =
    Monomorphism.recoordinate (ContinuousLinearEquiv.refl ℝ (Vector (e.ambientDimension + 6)))
      (sourceBlock L (e.ambientDimension - 6))
      (twistedBlockMap (e.sphereFrameOperatorMap a f hf hd) (sphereMap L s)) := by
  apply Subtype.ext
  change _ = ((twistedBlockMap (e.sphereFrameOperatorMap a f hf hd) (sphereMap L s)).val).comp
    (sourceBlock L (e.ambientDimension - 6)).toContinuousLinearMap
  rw [e.twistedSphereFrame_collar a _ _ _ (Stiefel.pole 3),
    e.twistedSphereFrame_collar a f hf hd (Stiefel.pole 3)]
  exact collarOperator_precomp L (Stiefel.pole 3) (e.toFun ∘ f) (e.smooth.comp hf) s
    (e.normalFrameOnSphere a f (sphereMap L s)).val

end EuclideanEmbedding
end NoExoticSixSphere
