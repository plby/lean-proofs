import Wikipedia.HopfProblem.DegreeCollapseQuaternionicPiEight
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicClutchingAction
import Wikipedia.HopfProblem.DegreeCollapseFirstStemGroup
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDegreeTwelve

/-!
# The actual quaternionic connecting map computes pi7(S3)

The source kernel vanishes by pi8(Sp(2)) = 0. The target obstruction
vanishes because the actual projection on pi7(Sp(2)) is multiplication
by a nonzero integer of absolute value twelve. Thus the original
connecting map identifies pi7(S3) with the computed first stem pi8(S7).
The actual clutching action on pi7(S6) is also injective.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicSeven

open NoExoticSixSphere SmoothCube SphereComposition CubicalSphereSuspension
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration QuaternionicColumns
open SecondHurewicz

theorem projectionDegree_injective : Function.Injective projectionDegree := by
  have hz : generatorProjectionDegree ≠ 0 := by
    intro h
    have ha := generatorProjectionDegree_natAbs
    rw [h] at ha
    norm_num at ha
  intro a b h
  have he := congrArg Multiplicative.toAdd h
  rw [projectionDegree_toAdd, projectionDegree_toAdd] at he
  have hc : (piSevenSpTwoMulEquiv a).toAdd = (piSevenSpTwoMulEquiv b).toAdd :=
    mul_right_cancel₀ hz he
  apply piSevenSpTwoMulEquiv.injective
  exact congrArg (Multiplicative.ofAdd : ℤ → Multiplicative ℤ) hc

theorem projection_seven_injective : Function.Injective (projectionMap 6) := by
  intro a b h
  exact projectionDegree_injective (congrArg baseDegreeEquiv h)

theorem projection_inclusion_seven (a : π_ 7 northSubgroup 1) :
    projectionMap 6 (inclusionMap 7 a) = 1 := by
  refine Quotient.inductionOn a fun q ↦ ?_
  change (⟦mapGenLoop projection 1 (mapGenLoop inclusion 1 q)⟧ :
    π_ 7 BaseSphere north) = ⟦GenLoop.const⟧
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro u
  exact (q u).property

theorem inclusion_seven_eq_one (a : π_ 7 northSubgroup 1) : inclusionMap 7 a = 1 :=
  projection_seven_injective
    ((projection_inclusion_seven a).trans (map_one (projectionMap 6)).symm)

theorem connecting_seven_surjective : Function.Surjective (connecting 7) := by
  intro a
  exact (connecting_range_eq_kernel a).mpr (inclusion_seven_eq_one a)

theorem connecting_seven_injective : Function.Injective (connecting 7) := by
  let := QuaternionicPiEight.piEightSpTwo_subsingleton
  intro a b h
  have hab : connecting 7 (a / b) = 1 := by
    change connectingHom 7 (a / b) = 1
    rw [map_div]
    exact div_eq_one.mpr h
  obtain ⟨c, hc⟩ :=
    (projectionMap_range_eq_connecting_kernel (n := 7) (a / b)).mpr hab
  have hsource : c = 1 := Subsingleton.elim _ _
  have hone : projectionMap 7 (1 : π_ 8 SpTwo 1) = 1 := rfl
  exact div_eq_one.mp
    (hc.symm.trans ((congrArg (projectionMap 7) hsource).trans hone))

def connectingEquiv : π_ 8 BaseSphere north ≃* π_ 7 northSubgroup 1 :=
  MulEquiv.ofBijective (connectingHom 7)
    ⟨connecting_seven_injective, connecting_seven_surjective⟩

def baseCoordinates : π_ 8 BaseSphere north ≃*
    π_ 8 (NoExoticSixSphere.Sphere 7) (spherePole 7) :=
  (homeomorphMulEquiv (N := Fin 8) baseSphereHomeomorph north).trans
    (basepointEqMulEquiv (N := Fin 8) NinthSphereQuotient.baseSphereHomeomorph_north)

def fiberCoordinates : π_ 7 northSubgroup 1 ≃*
    π_ 7 (NoExoticSixSphere.Sphere 3) (spherePole 3) :=
  (homeomorphMulEquiv (N := Fin 7) fiberSphereHomeomorph 1).trans
    (basepointEqMulEquiv (N := Fin 7) QuaternionicClutching.fiberSphereHomeomorph_one)

def sphereEquiv :
    π_ 8 (NoExoticSixSphere.Sphere 7) (spherePole 7) ≃*
      π_ 7 (NoExoticSixSphere.Sphere 3) (spherePole 3) :=
  (baseCoordinates.symm.trans connectingEquiv).trans fiberCoordinates

def groupEquiv : π_ 7 (NoExoticSixSphere.Sphere 3) (spherePole 3) ≃*
    Multiplicative (ZMod 2) :=
  sphereEquiv.symm.trans (FirstStemGroup.groupEquiv 4)

theorem sphereClutching_seven_injective :
    Function.Injective (mapHom QuaternionicClutching.sphereClutching 7) := by
  intro a b h
  have hf := SphereSelfMapSurjectivity.native_homeomorph_injective
    fiberSphereHomeomorph QuaternionicClutching.fiberSphereHomeomorph_one
    ((QuaternionicClutching.sphereClutching_map a).symm.trans
      (h.trans (QuaternionicClutching.sphereClutching_map b)))
  have hb := (QuaternionicClutching.baseMap_native_bijective 8).injective
    (connecting_seven_injective hf)
  exact hom_injective (by decide : 7 + 3 < 2 * (6 + 1)) hb

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicSeven
