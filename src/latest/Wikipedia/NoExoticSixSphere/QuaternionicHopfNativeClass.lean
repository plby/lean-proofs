import Wikipedia.NoExoticSixSphere.QuaternionicHopfFiberDiffeomorph
import Wikipedia.NoExoticSixSphere.OriginalHopfSixthSquare

/-!
# The native class of the explicit smooth quaternionic Hopf map

The literal standard source pole lies on the displayed north fiber.
Thus the smooth polynomial gives an actual based sphere map and native
class. Its Hopf coordinate is defined through the ORIGINAL James--Hopf
homomorphism, and is deliberately not assigned a value by definition.
-/

noncomputable section

open scoped Quaternion Topology

namespace NoExoticSixSphere.QuaternionicHopf

open SmoothCube SphereComposition
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

theorem fiberPoint_pole : fiberPoint (spherePole 3) = spherePole 7 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [fiberPoint, axis, planeCoordinates, spherePole]
  all_goals rfl

theorem sphereMap_pole : sphereMap (spherePole 7) = spherePole 4 := by
  rw [← fiberPoint_pole]
  exact sphereMap_fiberPoint (spherePole 3)

def basedMap : Based 7 4 := ⟨sphereMap, sphereMap_pole⟩

def nativeClass : π_ 7 (Sphere 4) (spherePole 4) := sphereClass basedMap

def hopfNumber : ℤ := OriginalHopfSixthSquare.hopfCoordinate nativeClass

def suspendedMap : Based 8 5 := CubicalSphereSuspension.productBasedMap basedMap

def suspendedSmashClass : StableSixSphereMaps.NativeStage 8 :=
  sphereClass (SphereSmash.basedSquare suspendedMap)

theorem suspendedSmashClass_eq_of_hopfNumber (h : hopfNumber.natAbs = 1) :
    suspendedSmashClass = SixthStemSmashSquare.nativeClass :=
  OriginalHopfSixthSquare.sphereClass_square basedMap h

end NoExoticSixSphere.QuaternionicHopf
