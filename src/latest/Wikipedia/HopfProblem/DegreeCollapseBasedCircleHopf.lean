import Wikipedia.NoExoticSixSphere.SphereTwoHigherHopf
import Wikipedia.HopfProblem.DegreeCollapseSecondStemReduction
import Wikipedia.HopfProblem.DegreeCollapseSphereLiftFamily

/-!
# The original circle-Hopf projection with the standard sphere poles

Quaternionic multiplication supplies an actual homeomorphism moving
the three-sphere pole to the required Hopf preimage. Compose it with
the original Hopf projection. The resulting based map retains the
original higher-homotopy isomorphisms, including their values on maps.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.BasedCircleHopf

open NoExoticSixSphere SmoothCube SphereLiftFamily
open Wikipedia.HomotopyGroupsOfSpheres (pointedHomeomorphMulEquiv pointedHomeomorphMulEquiv_mk)

abbrev fiberHomeomorph :=
  Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration.fiberSphereHomeomorph

def movePole (x : Sphere 3) : Sphere 3 ≃ₜ Sphere 3 :=
  fiberHomeomorph.symm.trans ((Homeomorph.mulLeft (fiberHomeomorph.symm x)).trans fiberHomeomorph)

theorem movePole_pole (x : Sphere 3) : movePole x (spherePole 3) = x := by
  have hp : fiberHomeomorph.symm (spherePole 3) = 1 := by
    apply fiberHomeomorph.injective
    exact (fiberHomeomorph.apply_symm_apply (spherePole 3)).trans
      QuaternionicClutching.fiberSphereHomeomorph_one.symm
  change fiberHomeomorph (fiberHomeomorph.symm x * fiberHomeomorph.symm (spherePole 3)) = x
  rw [hp, mul_one, Homeomorph.apply_symm_apply]

abbrev preimage : Sphere 3 := HigherHopf.preimage (spherePole 2)

def projection : SphereComposition.Based 3 2 :=
  ⟨HigherHopf.sphereProjection.comp (movePole preimage : C(_, _)), by
    change HigherHopf.sphereProjection (movePole preimage (spherePole 3)) = spherePole 2
    rw [movePole_pole]
    exact HigherHopf.preimage_projection (spherePole 2)⟩

def homEquiv (k : ℕ) : π_ (k + 3) (Sphere 3) (spherePole 3) ≃*
    π_ (k + 3) (Sphere 2) (spherePole 2) :=
  (pointedHomeomorphMulEquiv (N := Fin (k + 3)) (movePole preimage) (spherePole 3) preimage
    (movePole_pole preimage)).trans
      (HigherHopf.spherePointedPiEquiv k preimage (spherePole 2)
        (HigherHopf.preimage_projection (spherePole 2)))

theorem homEquiv_apply (k : ℕ) (c : π_ (k + 3) (Sphere 3) (spherePole 3)) :
    homEquiv k c = HigherHomotopy.map projection.val projection.property c := by
  induction c using Quotient.inductionOn with
  | h p =>
    exact (congrArg
      (HigherHopf.spherePointedPiEquiv k preimage (spherePole 2)
        (HigherHopf.preimage_projection (spherePole 2)))
      (pointedHomeomorphMulEquiv_mk (movePole preimage) (spherePole 3) preimage
        (movePole_pole preimage) p)).trans
          (HigherHopf.spherePointedPiEquiv_apply k preimage (spherePole 2)
            (HigherHopf.preimage_projection (spherePole 2)) _)

theorem homEquiv_class (k : ℕ) (g : SphereComposition.Based (k + 3) 3) :
    homEquiv k (sphereClass g) = sphereClass (compose projection g) := by
  rw [homEquiv_apply]
  rfl

def fourthGroupEquiv : π_ 4 (Sphere 2) (spherePole 2) ≃* Multiplicative (ZMod 2) :=
  (homEquiv 1).symm.trans (FirstStemGroup.groupEquiv 0)

theorem fourth_card : Nat.card (π_ 4 (Sphere 2) (spherePole 2)) = 2 :=
  (Nat.card_congr (homEquiv 1).symm.toEquiv).trans (FirstStemGroup.card 0)

end Wikipedia.HopfProblem.DegreeCollapse.BasedCircleHopf
