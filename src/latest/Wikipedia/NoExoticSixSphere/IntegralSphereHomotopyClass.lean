import Wikipedia.NoExoticSixSphere.SphereHurewiczFundamentalClass
import Wikipedia.NoExoticSixSphere.SmoothSphereBasepointAdjustment
import Wikipedia.NoExoticSixSphere.SpherePinchHomology

/-!
# Actual integral sphere classes classify maps into a two-connected target

The class is the image of the genuine cubical sphere fundamental class.
Moving basepoint values and applying the native Hurewicz isomorphism proves
that equality of these integral classes gives an actual sphere homotopy.
The geometric hemisphere pinch adds these classes.
-/

noncomputable section

open Function
open scoped Topology

namespace NoExoticSixSphere.SmoothCube

open SphereSumNeck
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type} [TopologicalSpace X]

def integralSphereClass (f : C(Sphere 3, X)) : SingularHomology X 3 :=
  singularHomologyMap f 3 integralCubeSphereClass

theorem integralSphereClass_homotopic {f g : C(Sphere 3, X)} (H : f.Homotopic g) :
    integralSphereClass f = integralSphereClass g := by
  unfold integralSphereClass
  rw [homotopic_homologyMap H 3]

theorem integralSphereClass_pinch (f g : C(Sphere 3, X))
    (hbase : f (antipode pinchPole) = g (antipode pinchPole)) :
    integralSphereClass (SphereFold.pinch pinchPole f g hbase) =
      integralSphereClass f + integralSphereClass g := by
  unfold integralSphereClass
  rw [SphereFold.homologyMap_pinch f g hbase 3 (by decide), LinearMap.add_apply]

theorem integralSphereClass_const (x : X) :
    integralSphereClass (ContinuousMap.const (Sphere 3) x) = 0 := by
  unfold integralSphereClass
  rw [Wikipedia.HopfProblem.CuspCentralHomology.singularHomologyMap_const_eq_zero
    _ _ 3 (by decide), LinearMap.zero_apply]

variable [SimplyConnectedSpace X] (x : X) [h₂ : Subsingleton (π_ 2 X x)]

theorem hurewiczSphereClass_eq_integralSphereClass (f : BasedMap 3 X x) :
    hurewiczSphereClass x f = integralSphereClass f.val :=
  hurewiczSphereClass_eq_image_cube f

def integralClassRepresentative (c : SingularHomology X 3) : BasedMap 3 X x :=
  (hurewiczSphereClass_surjective x c).choose

theorem integralSphereClass_representative (c : SingularHomology X 3) :
    integralSphereClass (integralClassRepresentative x c).val = c :=
  (hurewiczSphereClass_eq_integralSphereClass x _).symm.trans
    (hurewiczSphereClass_surjective x c).choose_spec

include x h₂ in
theorem integralSphereClass_eq_iff_homotopic (f g : C(Sphere 3, X)) :
    integralSphereClass f = integralSphereClass g ↔ f.Homotopic g := by
  constructor
  · intro he
    obtain ⟨F, HF⟩ := exists_based_map_homotopic (by decide : 0 < 3) f x
    obtain ⟨G, HG⟩ := exists_based_map_homotopic (by decide : 0 < 3) g x
    have hFG : hurewiczSphereClass x F = hurewiczSphereClass x G := by
      rw [hurewiczSphereClass_eq_integralSphereClass,
        hurewiczSphereClass_eq_integralSphereClass,
        ← integralSphereClass_homotopic HF, ← integralSphereClass_homotopic HG, he]
    have hclass : sphereClass F = sphereClass G :=
      congrArg Additive.toMul ((hurewiczLinearEquiv x).injective hFG)
    exact HF.trans (((sphereClass_eq_iff (by decide : 0 < 3) F G).mp hclass).homotopic.trans
      HG.symm)
  · exact integralSphereClass_homotopic

end NoExoticSixSphere.SmoothCube

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube
open scoped Manifold ContDiff

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)
  (m : M) [Subsingleton (π_ 2 M m)]

theorem integralHomologyIntersection_integralSphereClass (f g : C(Sphere 3, M)) :
    e.integralHomologyIntersection r m (integralSphereClass f) (integralSphereClass g) =
      e.sphereIntersectionNumber r f g := by
  obtain ⟨F, HF⟩ := exists_based_map_homotopic (by decide : 0 < 3) f m
  obtain ⟨G, HG⟩ := exists_based_map_homotopic (by decide : 0 < 3) g m
  rw [integralSphereClass_homotopic HF, integralSphereClass_homotopic HG,
    ← hurewiczSphereClass_eq_integralSphereClass m F,
    ← hurewiczSphereClass_eq_integralSphereClass m G, integralHomologyIntersection_sphereClass]
  exact (e.sphereIntersectionNumber_homotopic r f F.val g G.val HF HG).symm

end NoExoticSixSphere.EuclideanEmbedding
