import Wikipedia.NoExoticSixSphere.NativeHomotopyIntersection
import Wikipedia.HopfProblem.ThirdHurewiczIso
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The geometric mod-two pairing on native integral middle homology

For an actually two-connected compact smooth six-manifold, the checked
native third Hurewicz isomorphism transfers the geometric intersection
pairing to its actual integral singular third homology. This is an integral
bilinear form with values in `ZMod 2`. Every homology class has an actual
based-sphere representative, and the form evaluates to the geometric
intersection number on those representatives.

No mod-two homology identification, nondegeneracy, quadratic refinement,
or framed-bordism detection is asserted in this file.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SmoothCube

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (x : X) [Subsingleton (π_ 2 X x)]

def hurewiczSphereClass (f : BasedMap 3 X x) : SingularHomology X 3 :=
  hurewiczLinearEquiv x (Additive.ofMul (sphereClass f))

theorem hurewiczSphereClass_surjective : Surjective (hurewiczSphereClass x) := by
  intro c
  obtain ⟨f, hf⟩ := sphereClass_surjective (by decide : 0 < 3)
    (Additive.toMul ((hurewiczLinearEquiv x).symm c))
  refine ⟨f, ?_⟩
  unfold hurewiczSphereClass
  rw [hf]
  exact (hurewiczLinearEquiv x).apply_symm_apply c

end NoExoticSixSphere.SmoothCube

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.ThirdHurewicz

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)
  (m : M) [Subsingleton (π_ 2 M m)]

def integralHomologyIntersection :
    SingularHomology M 3 →ₗ[ℤ] SingularHomology M 3 →ₗ[ℤ] ZMod 2 :=
  (homotopyIntersectionForm e r).compl₁₂ (hurewiczLinearEquiv m).symm.toLinearMap
    (hurewiczLinearEquiv m).symm.toLinearMap

theorem integralHomologyIntersection_apply (c d : SingularHomology M 3) :
    integralHomologyIntersection e r m c d =
      homotopyIntersectionForm e r ((hurewiczLinearEquiv m).symm c)
        ((hurewiczLinearEquiv m).symm d) := rfl

theorem integralHomologyIntersection_sphereClass (f g : BasedMap 3 M m) :
    integralHomologyIntersection e r m (hurewiczSphereClass m f) (hurewiczSphereClass m g) =
      sphereIntersectionNumber e r f.val g.val := by
  rw [integralHomologyIntersection_apply]
  unfold hurewiczSphereClass
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact homotopyIntersectionForm_sphereClass e r f g

theorem integralHomologyIntersection_comm (c d : SingularHomology M 3) :
    integralHomologyIntersection e r m c d = integralHomologyIntersection e r m d c :=
  homotopyIntersection_comm e r _ _

theorem integralHomologyIntersection_independent (e' : EuclideanEmbedding 6 M)
    (r' : TubularRetraction e') :
    integralHomologyIntersection e r m = integralHomologyIntersection e' r' m := by
  ext c d
  exact homotopyIntersection_independent e r e' r' _ _

theorem integralHomologyIntersection_unique
    (B : SingularHomology M 3 →ₗ[ℤ] SingularHomology M 3 →ₗ[ℤ] ZMod 2)
    (hB : ∀ f g : BasedMap 3 M m,
      B (hurewiczSphereClass m f) (hurewiczSphereClass m g) =
        sphereIntersectionNumber e r f.val g.val) : B = integralHomologyIntersection e r m := by
  ext c d
  obtain ⟨f, rfl⟩ := hurewiczSphereClass_surjective m c
  obtain ⟨g, rfl⟩ := hurewiczSphereClass_surjective m d
  exact (hB f g).trans (integralHomologyIntersection_sphereClass e r m f g).symm

end NoExoticSixSphere.EuclideanEmbedding
