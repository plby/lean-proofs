import Wikipedia.NoExoticSixSphere.HigherHopfNativeEquivalence
import Wikipedia.HomotopyGroupsOfSpheres.SphereTwoThird
import Wikipedia.HomotopyGroupsOfSpheres.SphereThreeSix

/-!
# Higher Hopf comparison on the literal two- and three-spheres

The actual normal and meridian sphere homeomorphisms put the ORIGINAL
Hopf projection on the standard Euclidean spheres. Its higher native
isomorphisms retain that continuous map and explicit image-basepoint
equality. In degree six the proved quaternionic calculation therefore
also computes the actual sixth homotopy group of the two-sphere.
-/

noncomputable section

open scoped Topology
open Wikipedia.HomotopyGroupsOfSpheres
open Wikipedia.HopfProblem Wikipedia.HopfProblem.OrbitPair
open Wikipedia.HopfProblem.SpecialPeriods
open Wikipedia.HopfProblem.CuspCircleNormalTrivialization

namespace NoExoticSixSphere.HigherHopf

def radius : ℝ := injectiveRadius / 2

theorem radius_pos : 0 < radius := half_pos injectiveRadius_pos

theorem radius_lt : radius < injectiveRadius := half_lt_self injectiveRadius_pos

def totalCoordinates : NormalSphere radius ≃ₜ Sphere 3 :=
  normalSphereHomeomorph radius radius_pos

def baseCoordinates : MeridianSphere radius ≃ₜ Sphere 2 :=
  meridianSphereHomeomorph radius radius_pos

def sphereProjection : C(Sphere 3, Sphere 2) :=
  (baseCoordinates : C(_, _)).comp
    ((sphereHopfMap radius).comp (totalCoordinates.symm : C(_, _)))

theorem sphereProjection_surjective : Function.Surjective sphereProjection :=
  baseCoordinates.surjective.comp
    ((sphereHopfMap_surjective radius).comp totalCoordinates.symm.surjective)

def spherePiMulEquiv (n : ℕ) (x : Sphere 3) :
    π_ (n + 3) (Sphere 3) x ≃* π_ (n + 3) (Sphere 2) (sphereProjection x) :=
  (homeomorphMulEquiv (N := Fin (n + 3)) totalCoordinates.symm x).trans
    ((piMulEquiv (OnePoint.infty : RiemannSphere) radius radius_pos radius_lt n
      (totalCoordinates.symm x)).trans
        (homeomorphMulEquiv (N := Fin (n + 3)) baseCoordinates
          (sphereHopfMap radius (totalCoordinates.symm x))))

theorem spherePiMulEquiv_apply (n : ℕ) (x : Sphere 3) (c : π_ (n + 3) (Sphere 3) x) :
    spherePiMulEquiv n x c =
      HigherHomotopy.map (N := Fin (n + 3)) sphereProjection (y := x) rfl c := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

def spherePointedPiEquiv (n : ℕ) (x : Sphere 3) (y : Sphere 2) (h : sphereProjection x = y) :
    π_ (n + 3) (Sphere 3) x ≃* π_ (n + 3) (Sphere 2) y :=
  (spherePiMulEquiv n x).trans (basepointEqMulEquiv h)

theorem spherePointedPiEquiv_apply (n : ℕ) (x : Sphere 3) (y : Sphere 2)
    (h : sphereProjection x = y) (c : π_ (n + 3) (Sphere 3) x) :
    spherePointedPiEquiv n x y h c =
      HigherHomotopy.map (N := Fin (n + 3)) sphereProjection h c := by
  cases h
  exact spherePiMulEquiv_apply n x c

def preimage (x : Sphere 2) : Sphere 3 := (sphereProjection_surjective x).choose

theorem preimage_projection (x : Sphere 2) : sphereProjection (preimage x) = x :=
  (sphereProjection_surjective x).choose_spec

def sphereTwoPiEquiv (n : ℕ) (x : Sphere 2) :
    π_ (n + 3) (Sphere 2) x ≃* π_ (n + 3) (Sphere 3) (preimage x) :=
  (spherePointedPiEquiv n (preimage x) x (preimage_projection x)).symm

theorem sphereTwoPiEquiv_symm_apply (n : ℕ) (x : Sphere 2)
    (c : π_ (n + 3) (Sphere 3) (preimage x)) :
    (sphereTwoPiEquiv n x).symm c =
      HigherHomotopy.map (N := Fin (n + 3)) sphereProjection (preimage_projection x) c :=
  spherePointedPiEquiv_apply n (preimage x) x (preimage_projection x) c

def piSixSphereTwoMulEquiv (x : Sphere 2) : π_ 6 (Sphere 2) x ≃* Multiplicative (ZMod 12) :=
  (sphereTwoPiEquiv 3 x).trans (pi6_sphere_three_mulEquiv (preimage x))

end NoExoticSixSphere.HigherHopf
