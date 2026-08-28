import Wikipedia.NoExoticSixSphere.OrthonormalRangeFrame
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# Reparametrizing an actual embedded normal frame by a native diffeomorphism

The embedding and all ambient normal columns are pulled back along the
specified smooth diffeomorphism. The chain rule and its invertible tangent
map prove equality of the actual tangent and normal subspaces. No change
of atlas or additional normal-space identification is assumed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {n : ℕ} {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [TopologicalSpace M'] [ChartedSpace (Vector n) M']
  (e : EuclideanEmbedding n M) (D : M' ≃ₘ⟮𝓡 n, 𝓡 n⟯ M)

def reparametrize : EuclideanEmbedding n M' where
  ambientDimension := e.ambientDimension
  toFun := e.toFun ∘ D
  smooth := e.smooth.comp D.contMDiff
  closedEmbedding := e.closedEmbedding.comp D.toHomeomorph.isClosedEmbedding
  injective_mfderiv x := by
    rw [mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
      (D.contMDiff.mdifferentiableAt (by simp))]
    exact (e.injective_mfderiv (D x)).comp
      ((D.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)).injective

theorem reparametrize_apply (x : M') : (e.reparametrize D).toFun x = e.toFun (D x) := rfl

theorem reparametrize_tangentImage (x : M') :
    (e.reparametrize D).tangentImage x = e.tangentImage (D x) := by
  change (mfderiv (𝓡 n) (𝓡 e.ambientDimension) (e.toFun ∘ D) x).range =
    (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun (D x)).range
  rw [mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
    (D.contMDiff.mdifferentiableAt (by simp))]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr
    ((D.isLocalDiffeomorph x).mfderivToContinuousLinearEquiv (by simp)).surjective)

theorem reparametrize_normalProjection (x : M') :
    (e.reparametrize D).normalProjection x = e.normalProjection (D x) := by
  change ((e.reparametrize D).tangentImage x)ᗮ.starProjection =
    (e.tangentImage (D x))ᗮ.starProjection
  rw [reparametrize_tangentImage]
  rfl

def reparametrizeFrame (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) :
    SmoothRangeFrame (𝓡 n) (e.reparametrize D).normalProjection
      (e.reparametrize D).NormalModel := by
  let F (x : M') : Vector (e.ambientDimension - n) →L[ℝ] Vector e.ambientDimension :=
    a.ambient (D x)
  let P (x : M') : Vector e.ambientDimension →L[ℝ] Vector e.ambientDimension :=
    (e.reparametrize D).normalProjection x
  have hF (x : M') : (F x).range = (P x).range := by
    dsimp only [F, P]
    rw [reparametrize_normalProjection, a.ambient_range]
  let q (x : M') : Vector (e.ambientDimension - n) ≃L[ℝ] (P x).range :=
    (LinearEquiv.ofInjective (F x).toLinearMap (a.ambient_injective (D x))
      ).toContinuousLinearEquiv.trans (ContinuousLinearEquiv.ofEq _ _ (hF x))
  refine ⟨q, ?_⟩
  change ContMDiff (𝓡 n)
    𝓘(ℝ, Vector (e.ambientDimension - n) →L[ℝ] Vector e.ambientDimension) ∞
    (fun x : M' ↦ (P x).range.subtypeL.comp (q x).toContinuousLinearMap)
  have he : (fun x : M' ↦ (P x).range.subtypeL.comp (q x).toContinuousLinearMap) = F := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [he]
  exact a.smooth.comp D.contMDiff

theorem reparametrizeFrame_ambient
    (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) (x : M') :
    (e.reparametrizeFrame D a).ambient x = a.ambient (D x) := rfl

end NoExoticSixSphere.EuclideanEmbedding
