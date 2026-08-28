import Wikipedia.NoExoticSixSphere.SphereLocalFrameChainRule
import Wikipedia.NoExoticSixSphere.SphereGluedFrameGerms
import Wikipedia.NoExoticSixSphere.ManifoldFrameBlockCoordinates

/-!
# Exact frame reparametrization on both retained caps of the glued sphere

The normal columns are unchanged and the tangent columns transform by the
actual quaternionic source Jacobian. Its block extension is a continuous
family of invertible coordinates on each cap, with continuous inverse.
No assertion about global frame parity follows from these local identities.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SphereThreeTangentFrame

open GLOrthonormalization FrameBlockCoordinates

def sourceBlockJacobian (k : ℕ) (u : Sphere 3 → Sphere 3) (x : Sphere 3) :
    Vector (k + 3) →L[ℝ] Vector (k + 3) := identityBlockOperator k (sourceJacobian u x)

def sourceBlockJacobianEquiv (k : ℕ) (u : Sphere 3 → Sphere 3) (x : Sphere 3)
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) :
    Vector (k + 3) ≃L[ℝ] Vector (k + 3) :=
  EuclideanSpace.finAddEquivProd.trans
    (((ContinuousLinearEquiv.refl ℝ (Vector k)).prodCongr (sourceJacobianEquiv u x hu)).trans
      EuclideanSpace.finAddEquivProd.symm)

theorem sourceBlockJacobianEquiv_toContinuousLinearMap (k : ℕ) (u : Sphere 3 → Sphere 3)
    (x : Sphere 3) (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) :
    (sourceBlockJacobianEquiv k u x hu).toContinuousLinearMap = sourceBlockJacobian k u x := by
  ext v
  rfl

theorem continuous_sourceBlockJacobianEquiv (k : ℕ) (u : Sphere 3 → Sphere 3)
    (U : Set (Sphere 3)) (hu : ∀ x : U, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x.val) :
    Continuous (fun x : U ↦
      (sourceBlockJacobianEquiv k u x.val (hu x)).toContinuousLinearMap) := by
  simp_rw [sourceBlockJacobianEquiv_toContinuousLinearMap]
  exact continuous_identityBlockOperator k (fun x : U ↦ sourceJacobian u x.val)
    (continuous_sourceJacobianEquiv u U hu)

theorem continuous_inverse_sourceBlockJacobianEquiv (k : ℕ) (u : Sphere 3 → Sphere 3)
    (U : Set (Sphere 3)) (hu : ∀ x : U, IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x.val) :
    Continuous (fun x : U ↦
      (sourceBlockJacobianEquiv k u x.val (hu x)).symm.toContinuousLinearMap) := by
  have he (x : U) : (sourceBlockJacobianEquiv k u x.val (hu x)).symm.toContinuousLinearMap =
      (sourceBlockJacobian k u x.val).inverse := by
    rw [← sourceBlockJacobianEquiv_toContinuousLinearMap k u x.val (hu x)]
    exact (ContinuousLinearMap.inverse_equiv (sourceBlockJacobianEquiv k u x.val (hu x))).symm
  simp_rw [he]
  rw [continuous_iff_continuousAt]
  intro x
  have hi : (sourceBlockJacobian k u x.val).IsInvertible :=
    ⟨sourceBlockJacobianEquiv k u x.val (hu x),
      sourceBlockJacobianEquiv_toContinuousLinearMap k u x.val (hu x)⟩
  have hc : ContinuousAt (fun y : U ↦ sourceBlockJacobian k u y.val) x := by
    simpa only [sourceBlockJacobianEquiv_toContinuousLinearMap] using
      (continuous_sourceBlockJacobianEquiv k u U hu).continuousAt (x := x)
  exact (hi.contDiffAt_map_inverse (n := ∞)).continuousAt.comp
    (f := fun y : U ↦ sourceBlockJacobian k u y.val) hc

end SphereThreeTangentFrame

namespace FrameBlockCoordinates

open GLOrthonormalization

theorem operatorSum_comp_identityBlock {N k n d : ℕ}
    (A : Vector k →L[ℝ] Vector N) (B : Vector n →L[ℝ] Vector N)
    (C : Vector d →L[ℝ] Vector n) :
    OperatorSum.operator A (B.comp C) =
      (OperatorSum.operator A B).comp (identityBlockOperator k C) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, OperatorSum.operator_apply,
    identityBlockOperator_apply, ContinuousLinearEquiv.apply_symm_apply]

end FrameBlockCoordinates

namespace EuclideanEmbedding

open GLOrthonormalization SphereThreeTangentFrame FrameBlockCoordinates SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem sphereFrameOperator_comp_at (f : Sphere 3 → M) (u : Sphere 3 → Sphere 3)
    (x : Sphere 3) (hf : MDifferentiableAt (𝓡 3) (𝓡 6) f (u x))
    (hu : MDifferentiableAt (𝓡 3) (𝓡 3) u x) :
    e.sphereFrameOperator ν (f ∘ u) x = (e.sphereFrameOperator ν f (u x)).comp
      (sourceBlockJacobian (e.ambientDimension - 6) u x) := by
  have he : MDifferentiableAt (𝓡 6) (𝓡 e.ambientDimension) e.toFun (f (u x)) :=
    e.smooth.mdifferentiableAt (by simp)
  have hef : MDifferentiableAt (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) (u x) :=
    he.comp (u x) hf
  have hd := framedDerivative_comp_at (e.toFun ∘ f) u x hef hu
  let A := (ν.orthonormal (f (u x))).val
  let B := framedDerivative (e.toFun ∘ f) (u x)
  change OperatorSum.operator A (framedDerivative ((e.toFun ∘ f) ∘ u) x) =
    (OperatorSum.operator A B).comp
      (identityBlockOperator (e.ambientDimension - 6) (sourceJacobian u x))
  rw [hd]
  exact operatorSum_comp_identityBlock A B (sourceJacobian u x)

theorem sphereFrameOperator_comp_cancel (f : Sphere 3 → M) (u : Sphere 3 → Sphere 3)
    (x : Sphere 3) (hf : MDifferentiableAt (𝓡 3) (𝓡 6) f (u x))
    (hu : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ u x) :
    (e.sphereFrameOperator ν (f ∘ u) x).comp
      (sourceBlockJacobianEquiv (e.ambientDimension - 6) u x hu).symm.toContinuousLinearMap =
      e.sphereFrameOperator ν f (u x) := by
  rw [e.sphereFrameOperator_comp_at ν f u x hf (hu.mdifferentiableAt (by simp)),
    ← sourceBlockJacobianEquiv_toContinuousLinearMap (e.ambientDimension - 6) u x hu]
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (e.sphereFrameOperator ν f (u x))
    ((sourceBlockJacobianEquiv (e.ambientDimension - 6) u x hu).apply_symm_apply v)

variable (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

include hε ha hprod in
theorem sphereFrameOperator_glued_north_chain (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
    {x : Sphere 3} (hx : x ∈ northRegion) :
    e.sphereFrameOperator ν (gluedSphere Φ ε a F G) x =
      (e.sphereFrameOperator ν F (sphereCap ε x)).comp
        (sourceBlockJacobian (e.ambientDimension - 6) (sphereCap ε) x) := by
  rw [e.sphereFrameOperator_glued_north ν Φ F G hε ha hprod hleft hx]
  exact e.sphereFrameOperator_comp_at ν F (sphereCap ε) x
    (hF.mdifferentiableAt (by simp))
    ((isLocalDiffeomorphAt_sphereCap hε.ne' (northRegion_head_pos hx)).mdifferentiableAt
      (by simp))

include hε ha hprod in
theorem sphereFrameOperator_glued_south_chain (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
    {x : Sphere 3} (hx : x ∈ southRegion) :
    e.sphereFrameOperator ν (gluedSphere Φ ε a F G) x =
      (e.sphereFrameOperator ν G (sphereCap ε (reflectHead x))).comp
        (sourceBlockJacobian (e.ambientDimension - 6) (sphereCap ε ∘ reflectHead) x) := by
  rw [e.sphereFrameOperator_glued_south ν Φ F G hε ha hprod hright hx]
  exact e.sphereFrameOperator_comp_at ν G (sphereCap ε ∘ reflectHead) x
    (hG.mdifferentiableAt (by simp))
    ((isLocalDiffeomorphAt_southCap hε.ne' hx).mdifferentiableAt (by simp))

end EuclideanEmbedding
end NoExoticSixSphere
