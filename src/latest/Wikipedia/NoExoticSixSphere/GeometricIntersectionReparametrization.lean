import Wikipedia.NoExoticSixSphere.GeometricSphereIntersection
import Wikipedia.NoExoticSixSphere.SphereNativeDerivativeCoordinates
import Wikipedia.NoExoticSixSphere.SphereLinearDiskExtension

/-!
# Intersection number under independent sphere diffeomorphisms

Actual native derivatives transport transversality through the two source
diffeomorphisms. The source-pair bijection preserves the finite intersection
count, and the constructed representative homotopies give the result for
arbitrary continuous maps. No orientation condition is needed modulo two.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere
namespace SphereSumNeck

open GLOrthonormalization

theorem nativeSpherePairTransverse_precomp_diffeomorph
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
    (f g : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g) (ht : NativeSpherePairTransverse f g)
    (u v : Diffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞) :
    NativeSpherePairTransverse (f ∘ u) (g ∘ v) := by
  intro x y he
  unfold NativeSphereTransverseAt
  rw [nativeSphereDerivative_comp f u x hf (u.isLocalDiffeomorph x),
    nativeSphereDerivative_comp g v y hg (v.isLocalDiffeomorph y)]
  exact surjective_coprod_comp_both _ _ _ _
    (nativeSphereSourceDerivative_surjective u x (u.isLocalDiffeomorph x))
    (nativeSphereSourceDerivative_surjective v y (v.isLocalDiffeomorph y)) (ht _ _ he)

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization SphereSumNeck SphereLinearReparametrization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

theorem sphereIntersectionNumber_precomp_diffeomorph
    (u v : Diffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞)
    (f g : C(Sphere 3, M)) :
    e.sphereIntersectionNumber r (f.comp ⟨u, u.contMDiff_toFun.continuous⟩)
      (g.comp ⟨v, v.contMDiff_toFun.continuous⟩) = e.sphereIntersectionNumber r f g := by
  let D := e.intersectionRepresentative r f g
  have Hf : (f.comp ⟨u, u.contMDiff_toFun.continuous⟩).Homotopic
      (D.left.comp ⟨u, u.contMDiff_toFun.continuous⟩) := by
    obtain ⟨H⟩ := D.homotopic_left
    exact ⟨H.compContinuousMap ⟨u, u.contMDiff_toFun.continuous⟩⟩
  have Hg : (g.comp ⟨v, v.contMDiff_toFun.continuous⟩).Homotopic
      (D.right.comp ⟨v, v.contMDiff_toFun.continuous⟩) := by
    obtain ⟨H⟩ := D.homotopic_right
    exact ⟨H.compContinuousMap ⟨v, v.contMDiff_toFun.continuous⟩⟩
  calc
    e.sphereIntersectionNumber r (f.comp ⟨u, u.contMDiff_toFun.continuous⟩)
        (g.comp ⟨v, v.contMDiff_toFun.continuous⟩) =
        e.sphereIntersectionNumber r (D.left.comp ⟨u, u.contMDiff_toFun.continuous⟩)
          (D.right.comp ⟨v, v.contMDiff_toFun.continuous⟩) :=
      e.sphereIntersectionNumber_homotopic r _ _ _ _ Hf Hg
    _ = MapIntersections.parity (D.left ∘ u) (D.right ∘ v) :=
      e.sphereIntersectionNumber_eq_parity r _ _
        (D.smooth_left.comp u.contMDiff_toFun) (D.smooth_right.comp v.contMDiff_toFun)
        (nativeSpherePairTransverse_precomp_diffeomorph D.left D.right
          D.smooth_left D.smooth_right D.transverse u v)
    _ = MapIntersections.parity D.left D.right :=
      MapIntersections.parity_reparametrize D.left D.right u.toEquiv v.toEquiv
    _ = e.sphereIntersectionNumber r f g :=
      (e.sphereIntersectionNumber_eq_representative r f g D).symm

theorem sphereIntersectionNumber_precomp_linear
    (L K : Vector 4 ≃ₗᵢ[ℝ] Vector 4) (f g : C(Sphere 3, M)) :
    e.sphereIntersectionNumber r (f.comp (sphereMap L)) (g.comp (sphereMap K)) =
      e.sphereIntersectionNumber r f g :=
  e.sphereIntersectionNumber_precomp_diffeomorph r (sphereDiffeomorph L)
    (sphereDiffeomorph K) f g

end EuclideanEmbedding
end NoExoticSixSphere
