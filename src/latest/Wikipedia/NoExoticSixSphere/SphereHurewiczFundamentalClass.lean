import Wikipedia.NoExoticSixSphere.ModTwoHomologyIntersection
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups
import Wikipedia.HopfProblem.ThirdHurewiczNaturality
import Wikipedia.HopfProblem.SphereHomologyCoefficientsNaturality
import Wikipedia.HopfProblem.SphereHomologyCoefficientsSphere

/-!
# Comparison with the standard mod-two sphere fundamental class

Naturality identifies every constructed sphere class with the image of
one actual class of the original three-sphere. Surjectivity of the native
Hurewicz/coefficient construction proves that this class is nonzero modulo
two. The computed mod-two homology of the sphere has exactly one nonzero
element, so the class is the already chosen standard fundamental class.
No orientation sign or degree convention is assumed.
-/

noncomputable section

open Set Function
open scoped Topology

namespace NoExoticSixSphere.SmoothCube

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients
open Wikipedia.HopfProblem.ThirdHurewicz

def integralCubeSphereClass : SingularHomology (Sphere 3) 3 :=
  cubeHomologyClass (toGenLoop identityBased)

def modTwoCubeSphereClass : ModHomology 2 (Sphere 3) 3 :=
  reductionHomologyMap 2 (Sphere 3) 3 integralCubeSphereClass

variable {X : Type} [TopologicalSpace X] {x : X}

theorem cubeHomologyClass_toGenLoop (f : BasedMap 3 X x) :
    cubeHomologyClass (toGenLoop f) =
      singularHomologyMap f.val 3 integralCubeSphereClass := by
  rcases f with ⟨f, hf⟩
  subst x
  have he : Wikipedia.HopfProblem.SecondHurewicz.mapGenLoop f (spherePole 3)
      (toGenLoop identityBased) = toGenLoop (⟨f, rfl⟩ : BasedMap 3 X (f (spherePole 3))) := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro u
    rfl
  have h := cubeHomologyClass_natural f (spherePole 3) (toGenLoop identityBased)
  rw [he] at h
  exact h.symm

variable [SimplyConnectedSpace X] [Subsingleton (π_ 2 X x)]

theorem hurewiczSphereClass_eq_image_cube (f : BasedMap 3 X x) :
    hurewiczSphereClass x f = singularHomologyMap f.val 3 integralCubeSphereClass := by
  change cubeHomologyClass (toGenLoop f) = _
  exact cubeHomologyClass_toGenLoop f

theorem modTwoSphereClass_eq_image_cube (f : BasedMap 3 X x) :
    modTwoSphereClass x f = modHomologyMap 2 f.val 3 modTwoCubeSphereClass := by
  unfold modTwoSphereClass modTwoCubeSphereClass
  rw [hurewiczSphereClass_eq_image_cube, modHomologyMap_reduction]

theorem modTwoCubeSphereClass_ne_zero : modTwoCubeSphereClass ≠ 0 := by
  let : Subsingleton (π_ 2 (Sphere 3) (spherePole 3)) :=
    subsingleton_sphereHomotopyGroup (by decide : 2 < 3) (spherePole 3)
  obtain ⟨f, hf⟩ := modTwoSphereClass_surjective (spherePole 3) (unitSphereModTopClass 2 2)
  intro hz
  have h := modTwoSphereClass_eq_image_cube f
  rw [hz, map_zero] at h
  exact unitSphereModTopClass_ne_zero 2 (by decide) 2 (hf.symm.trans h)

theorem modTwoCubeSphereClass_eq_standard :
    modTwoCubeSphereClass = unitSphereModTopClass 2 2 := by
  let e := unitSphereModHomologyTopEquiv 2 (by decide) 2
  have hn : e modTwoCubeSphereClass ≠ 0 := by
    intro h
    apply modTwoCubeSphereClass_ne_zero
    exact e.injective (h.trans e.map_zero.symm)
  have he : e modTwoCubeSphereClass = 1 := by
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (e modTwoCubeSphereClass) with h | h
    · exact (hn h).elim
    · exact h
  apply e.injective
  exact he.trans (unitSphereModHomologyTopEquiv_topClass 2 (by decide) 2).symm

theorem modTwoSphereClass_eq_standard (f : BasedMap 3 X x) :
    modTwoSphereClass x f = modHomologyMap 2 f.val 3 (unitSphereModTopClass 2 2) := by
  rw [modTwoSphereClass_eq_image_cube, modTwoCubeSphereClass_eq_standard]

end NoExoticSixSphere.SmoothCube
