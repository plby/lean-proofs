import Wikipedia.NoExoticSixSphere.IntegralHomologyIntersection
import Wikipedia.NoExoticSixSphere.ModTwoBilinearDescent
import Wikipedia.NoExoticSixSphere.TwoConnectedCoefficientReduction
import Wikipedia.NoExoticSixSphere.ModHomologyModule

/-!
# The actual geometric pairing on native mod-two middle homology

The native coefficient exact sequence identifies mod-two third homology
with the quotient of integral third homology by twice the group. The
geometric integral bilinear form kills that subgroup in both variables,
so it descends to a `ZMod 2`-bilinear form on the original finite-coefficient
homology object. Every class has an actual based sphere representative,
and evaluation agrees with the geometric intersection number.

The target manifold is assumed actually two-connected. No replacement
homology object, nondegeneracy, quadratic refinement, bordism detection,
or no-exotic-spheres conclusion is introduced by this construction.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SmoothCube

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
  (x : X) [Subsingleton (π_ 2 X x)]

def modTwoSphereClass (f : BasedMap 3 X x) : ModHomology 2 X 3 :=
  reductionHomologyMap 2 X 3 (hurewiczSphereClass x f)

theorem modTwoSphereClass_surjective : Surjective (modTwoSphereClass x) :=
  (TwoConnectedCoefficients.middleReduction_surjective x).comp (hurewiczSphereClass_surjective x)

end NoExoticSixSphere.SmoothCube

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] Submodule.Quotient.module modHomologyModule

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)
  (m : M) [Subsingleton (π_ 2 M m)]

def modTwoHomologyIntersectionInt :
    ModHomology 2 M 3 →ₗ[ℤ] ModHomology 2 M 3 →ₗ[ℤ] ZMod 2 :=
  (ModTwoBilinear.quotientForm (integralHomologyIntersection e r m)).compl₁₂
    (TwoConnectedCoefficients.middleQuotientEquiv m).symm.toLinearMap
    (TwoConnectedCoefficients.middleQuotientEquiv m).symm.toLinearMap

theorem modTwoHomologyIntersectionInt_reduction (a b : SingularHomology M 3) :
    modTwoHomologyIntersectionInt e r m
        (reductionHomologyMap 2 M 3 a) (reductionHomologyMap 2 M 3 b) =
      integralHomologyIntersection e r m a b := by
  change ModTwoBilinear.quotientForm (integralHomologyIntersection e r m)
    ((TwoConnectedCoefficients.middleQuotientEquiv m).symm (reductionHomologyMap 2 M 3 a))
    ((TwoConnectedCoefficients.middleQuotientEquiv m).symm (reductionHomologyMap 2 M 3 b)) = _
  rw [TwoConnectedCoefficients.middleQuotientEquiv_symm_reduction,
    TwoConnectedCoefficients.middleQuotientEquiv_symm_reduction, ModTwoBilinear.quotientForm_mk]

def modTwoHomologyIntersection :
    ModHomology 2 M 3 →ₗ[ZMod 2] ModHomology 2 M 3 →ₗ[ZMod 2] ZMod 2 :=
  ModTwoBilinear.scalarUpgrade (modTwoHomologyIntersectionInt e r m)

theorem modTwoHomologyIntersection_reduction (a b : SingularHomology M 3) :
    modTwoHomologyIntersection e r m
        (reductionHomologyMap 2 M 3 a) (reductionHomologyMap 2 M 3 b) =
      integralHomologyIntersection e r m a b :=
  modTwoHomologyIntersectionInt_reduction e r m a b

theorem modTwoHomologyIntersection_sphereClass (f g : BasedMap 3 M m) :
    modTwoHomologyIntersection e r m (modTwoSphereClass m f) (modTwoSphereClass m g) =
      sphereIntersectionNumber e r f.val g.val := by
  unfold modTwoSphereClass
  rw [modTwoHomologyIntersection_reduction, integralHomologyIntersection_sphereClass]

theorem modTwoHomologyIntersection_comm (a b : ModHomology 2 M 3) :
    modTwoHomologyIntersection e r m a b = modTwoHomologyIntersection e r m b a := by
  obtain ⟨f, rfl⟩ := modTwoSphereClass_surjective m a
  obtain ⟨g, rfl⟩ := modTwoSphereClass_surjective m b
  rw [modTwoHomologyIntersection_sphereClass, modTwoHomologyIntersection_sphereClass]
  exact sphereIntersectionNumber_comm e r f.val g.val

theorem modTwoHomologyIntersection_independent (e' : EuclideanEmbedding 6 M)
    (r' : TubularRetraction e') :
    modTwoHomologyIntersection e r m = modTwoHomologyIntersection e' r' m := by
  ext a b
  obtain ⟨f, rfl⟩ := modTwoSphereClass_surjective m a
  obtain ⟨g, rfl⟩ := modTwoSphereClass_surjective m b
  rw [modTwoHomologyIntersection_sphereClass, modTwoHomologyIntersection_sphereClass]
  exact sphereIntersectionNumber_independent e r e' r' f.val g.val

theorem modTwoHomologyIntersection_unique
    (B : ModHomology 2 M 3 →ₗ[ZMod 2] ModHomology 2 M 3 →ₗ[ZMod 2] ZMod 2)
    (hB : ∀ f g : BasedMap 3 M m,
      B (modTwoSphereClass m f) (modTwoSphereClass m g) =
        sphereIntersectionNumber e r f.val g.val) : B = modTwoHomologyIntersection e r m := by
  ext a b
  obtain ⟨f, rfl⟩ := modTwoSphereClass_surjective m a
  obtain ⟨g, rfl⟩ := modTwoSphereClass_surjective m b
  exact (hB f g).trans (modTwoHomologyIntersection_sphereClass e r m f g).symm

end NoExoticSixSphere.EuclideanEmbedding
