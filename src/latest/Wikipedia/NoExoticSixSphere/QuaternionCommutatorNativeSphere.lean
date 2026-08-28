import Wikipedia.NoExoticSixSphere.QuaternionCommutatorBoundaryLift
import Wikipedia.NoExoticSixSphere.QuaternionCommutatorLocalRegularity
import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy

/-!
# An explicit native seven-sphere representative of the commutator lift

The two quaternion inputs use the actual smooth-interior cube quotient
of the standard three-sphere, followed by its quaternion coordinate
homeomorphism. The projected seven-loop descends through the original
smooth cube quotient. No arbitrary chosen loop is treated as smooth.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.QuaternionCommutatorNativeSphere

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres
open QuaternionicFibration QuaternionCommutatorBoundaryLift

theorem sphereHomeomorph_one : sphereHomeomorph 1 = spherePole 3 := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

theorem sphereHomeomorph_symm_pole : sphereHomeomorph.symm (spherePole 3) = 1 := by
  rw [← sphereHomeomorph_one, Homeomorph.symm_apply_apply]

def quaternionSphere : SmoothCube.BasedMap 3 UnitQuaternions 1 :=
  ⟨(sphereHomeomorph.symm : C(Sphere 3, UnitQuaternions)), sphereHomeomorph_symm_pole⟩

def quaternionCube : GenLoop (Fin 3) UnitQuaternions 1 := SmoothCube.toGenLoop quaternionSphere

theorem quaternionCube_apply (u : Fin 3 → I) :
    quaternionCube u = sphereHomeomorph.symm (SmoothCube.quotient 3 u) := rfl

theorem quaternionCube_surjective : Function.Surjective quaternionCube :=
  sphereHomeomorph.symm.surjective.comp (SmoothCube.quotient_surjective (by decide : 0 < 3))

def sevenLoop : GenLoop (Fin 7) BaseSphere north := projectedLoop quaternionCube quaternionCube

def sphereMap : C(Sphere 7, BaseSphere) := SmoothCube.descend (by decide : 0 < 7) sevenLoop

theorem sphereMap_quotient (u : Fin 7 → I) :
    sphereMap (SmoothCube.quotient 7 u) = sevenLoop u :=
  SmoothCube.descend_quotient (by decide : 0 < 7) sevenLoop u

theorem sphereMap_pole : sphereMap (spherePole 7) = north :=
  SmoothCube.descend_pole (by decide : 0 < 7) sevenLoop

def basedSphereMap : SmoothCube.BasedMap 7 BaseSphere north := ⟨sphereMap, sphereMap_pole⟩

theorem sphereClass_eq :
    SmoothCube.sphereClass basedSphereMap = (⟦sevenLoop⟧ : π_ 7 BaseSphere north) := by
  apply congrArg (fun p : GenLoop (Fin 7) BaseSphere north ↦ (⟦p⟧ : π_ 7 BaseSphere north))
  apply GenLoop.ext
  exact sphereMap_quotient

theorem connecting_sphereClass :
    connecting 6 (SmoothCube.sphereClass basedSphereMap) =
      fiberEquiv (QuaternionSamelson.pairing ⟦quaternionCube⟧ ⟦quaternionCube⟧) :=
  (congrArg (connecting 6) sphereClass_eq).trans
    (connecting_projectedLoop_pairing quaternionCube quaternionCube)

end NoExoticSixSphere.QuaternionCommutatorNativeSphere
