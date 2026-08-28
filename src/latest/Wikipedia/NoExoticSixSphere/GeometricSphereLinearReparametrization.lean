import Wikipedia.NoExoticSixSphere.ImmersedSphereLinearReparametrization
import Wikipedia.NoExoticSixSphere.GeometricSphereParity

/-!
# Geometric sphere parity is invariant under linear sphere isometries

Precomposing a constructed self-transverse immersive representative
preserves its native differential conditions. Its actual corrected parity
is unchanged by the checked frame and double-point calculations. Ordinary
homotopy invariance then gives the result for arbitrary continuous maps.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere
namespace SphereLinearReparametrization

open GLOrthonormalization

theorem selfTransverse_precomp (L : Vector 4 ≃ₗᵢ[ℝ] Vector 4)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y))) :
    ∀ x y, x ≠ y → (f ∘ sphereMap L) x = (f ∘ sphereMap L) y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (f ∘ sphereMap L) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) (f ∘ sphereMap L) y)) := by
  intro x y hxy he z
  have hL : ContMDiff (𝓡 3) (𝓡 3) ∞ (sphereMap L) :=
    (sphereDiffeomorph L).contMDiff_toFun
  have hi : Injective (sphereMap L) := (sphereDiffeomorph L).injective
  obtain ⟨⟨u, v⟩, huv⟩ := ht (sphereMap L x) (sphereMap L y) (hi.ne hxy) he z
  let Dx := (sphereDiffeomorph L).mfderivToContinuousLinearEquiv (by simp) x
  let Dy := (sphereDiffeomorph L).mfderivToContinuousLinearEquiv (by simp) y
  refine ⟨(Dx.symm u, Dy.symm v), ?_⟩
  rw [mfderiv_comp (f := sphereMap L) (g := f) x (hf.mdifferentiableAt (by simp))
      (hL.mdifferentiableAt (by simp)),
    mfderiv_comp (f := sphereMap L) (g := f) y (hf.mdifferentiableAt (by simp))
      (hL.mdifferentiableAt (by simp))]
  change ((mfderiv (𝓡 3) (𝓡 6) f (sphereMap L x)).coprod
    (mfderiv (𝓡 3) (𝓡 6) f (sphereMap L y))) (Dx (Dx.symm u), Dy (Dy.symm v)) = z
  exact (congrArg ((mfderiv (𝓡 3) (𝓡 6) f (sphereMap L x)).coprod
    (mfderiv (𝓡 3) (𝓡 6) f (sphereMap L y)))
      (Prod.ext (Dx.apply_symm_apply u) (Dy.apply_symm_apply v))).trans huv

end SphereLinearReparametrization

namespace EuclideanEmbedding

open GLOrthonormalization SphereLinearReparametrization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)

theorem geometricSphereParity_precomp_linear (L : Vector 4 ≃ₗᵢ[ℝ] Vector 4)
    (f : C(Sphere 3, M)) :
    e.geometricSphereParity a r (f.comp (sphereMap L)) = e.geometricSphereParity a r f := by
  obtain ⟨g, hg, H, hd, ht⟩ := e.exists_selfTransverse_immersed_homotopic r f
  have H' : (f.comp (sphereMap L)).Homotopic (g.comp (sphereMap L)) := by
    obtain ⟨H⟩ := H
    exact ⟨H.compContinuousMap (sphereMap L)⟩
  have hleft := e.geometricSphereParity_eq_representative a r
    (f.comp (sphereMap L)) (g.comp (sphereMap L))
    (hg.comp (sphereDiffeomorph L).contMDiff_toFun)
    (injective_mfderiv_precomp L g hg hd) (selfTransverse_precomp L g hg ht) H'
  have hright := e.geometricSphereParity_eq_representative a r f g hg hd ht H
  exact hleft.trans ((e.immersedSphereCorrectedParity_precomp_linear a L g hg hd).trans
    hright.symm)

end EuclideanEmbedding
end NoExoticSixSphere
