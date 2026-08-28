import Wikipedia.HopfProblem.DegreeCollapseHopfRadialPrecomposition
import Wikipedia.NoExoticSixSphere.QuaternionicHopfNativeClass

/-!
# The original quaternionic Hopf composite and its actual finite nullhomotopy

Use explicit sum coordinates that retain the standard source pole.
The joined S4-to-S3 map is then an actual based S8-to-S7 map. Composing
with the original polynomial Hopf map agrees exactly with the already
contracted orthogonal-family construction. Twelve ORIGINAL sphere
suspensions of this precise composite are therefore nullhomotopic.
-/

noncomputable section

open scoped Topology Quaternion
open NoExoticSixSphere GLOrthonormalization SmoothCube

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfPrecomposition

open QuaternionicHopfFamily HopfBlockCoordinates RadialSphereMap RadialJoinNaturality
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

def inputCoordinates : WithLp 2 (Vector 5 × Vector 4) ≃ₗᵢ[ℝ] Vector 9 :=
  ((EuclideanSpace.basisFun (Fin 5) ℝ).prod (EuclideanSpace.basisFun (Fin 4) ℝ)).equiv
    (EuclideanSpace.basisFun (Fin 9) ℝ) finSumFinEquiv

theorem inputCoordinates_pole :
    inputCoordinates (WithLp.toLp 2 ((spherePole 4).val, (0 : Vector 4))) = (spherePole 8).val := by
  have h := OrthonormalBasis.equiv_apply_basis
    ((EuclideanSpace.basisFun (Fin 5) ℝ).prod (EuclideanSpace.basisFun (Fin 4) ℝ))
    (EuclideanSpace.basisFun (Fin 9) ℝ) finSumFinEquiv (Sum.inl (0 : Fin 5))
  have hi : finSumFinEquiv (m := 5) (n := 4) (Sum.inl 0) = 0 := by decide
  simpa only [OrthonormalBasis.prod_apply, Sum.elim_inl, Function.comp_apply,
    EuclideanSpace.basisFun_apply, LinearMap.coe_inl, inputCoordinates, spherePole, hi] using h

def inputPole : UnitSphere (WithLp 2 (Vector 5 × Vector 4)) :=
  ⟨WithLp.toLp 2 ((spherePole 4).val, 0), by
    rw [mem_sphere_zero_iff_norm, WithLp.norm_toLp_fst]
    exact mem_sphere_zero_iff_norm.mp (spherePole 4).property⟩

theorem inputPole_coordinates : unitSphereCoordinates inputCoordinates inputPole = spherePole 8 :=
  Subtype.ext inputCoordinates_pole

theorem sourceCoordinates_pole :
    sourceCoordinates (WithLp.toLp 2 ((spherePole 3).val, (0 : Vector 4))) =
      (spherePole 7).val := by
  have h := congrArg (fun x : Sphere 7 ↦ x.val) QuaternionicHopf.fiberPoint_pole
  change planeCoordinates
    (WithLp.toLp 2 (quatCoordinates.symm (spherePole 3).val, (0 : ℍ))) = _ at h
  change planeCoordinates
    (WithLp.toLp 2 (quatCoordinates.symm (spherePole 3).val, quatCoordinates.symm 0)) = _
  rw [map_zero]
  exact h

def joinedMap (g : C(Sphere 4, Sphere 3)) : C(Sphere 8, Sphere 7) :=
  (unitSphereCoordinates sourceCoordinates : C(_, _)).comp
    ((RadialSphereJoin.sphereMap (G := Vector 4) g).comp
      ((unitSphereCoordinates inputCoordinates).symm : C(_, _)))

theorem joinedMap_square (g : C(Sphere 4, Sphere 3))
    (x : UnitSphere (WithLp 2 (Vector 5 × Vector 4))) :
    joinedMap g (unitSphereCoordinates inputCoordinates x) =
      unitSphereCoordinates sourceCoordinates (RadialSphereJoin.sphereMap (G := Vector 4) g x) := by
  change unitSphereCoordinates sourceCoordinates (RadialSphereJoin.sphereMap g
    ((unitSphereCoordinates inputCoordinates).symm
      (unitSphereCoordinates inputCoordinates x))) = _
  rw [Homeomorph.symm_apply_apply]

theorem joinedMap_nullhomotopic_iff (g : C(Sphere 4, Sphere 3)) :
    (joinedMap g).Nullhomotopic ↔ (SphereMapSuspension.iterate g 4).Nullhomotopic := by
  have h := nullhomotopic_iff_of_homeomorph_square
    (unitSphereCoordinates inputCoordinates) (unitSphereCoordinates sourceCoordinates)
    (RadialSphereJoin.sphereMap (G := Vector 4) g) (joinedMap g)
    (fun x ↦ (joinedMap_square g x).symm)
  exact h.symm.trans (RadialJoinIteration.nullhomotopic_iff_iterate g 4)

theorem joinedMap_pole (g : SphereComposition.Based 4 3) :
    joinedMap g.val (spherePole 8) = spherePole 7 := by
  rw [← inputPole_coordinates, joinedMap_square]
  apply Subtype.ext
  change sourceCoordinates (WithLp.toLp 2 (extend g.val (spherePole 4).val, 0)) = _
  rw [extend_unit, g.property]
  exact sourceCoordinates_pole

def joinedBasedMap (g : SphereComposition.Based 4 3) : SphereComposition.Based 8 7 :=
  ⟨joinedMap g.val, joinedMap_pole g⟩

def composite (g : SphereComposition.Based 4 3) : SphereComposition.Based 8 4 :=
  SphereComposition.comp QuaternionicHopf.basedMap (joinedBasedMap g)

theorem standardMap_eq_composite (g : C(Sphere 4, Sphere 3)) :
    RadialHopfStableVanishing.standardMap inputCoordinates
      (RadialJoinSuspension.leftCoordinates 3) (family.comp g) =
        QuaternionicHopf.sphereMap.comp (joinedMap g) := by
  apply ContinuousMap.ext
  intro y
  change unitSphereCoordinates (RadialJoinSuspension.leftCoordinates 3)
    (OrthogonalHopfMap.sphereMap (family.comp g)
      ((unitSphereCoordinates inputCoordinates).symm y)) = _
  rw [HopfRadialPrecomposition.sphereMap_precompose, QuaternionicHopfFamily.sphereMap_square]
  rfl

theorem composite_twelve_suspensions_nullhomotopic (g : SphereComposition.Based 4 3) :
    (SphereMapSuspension.iterate (composite g).val 12).Nullhomotopic := by
  have h := RadialHopfStableVanishing.standard_hopf_twelve_suspensions_nullhomotopic
    inputCoordinates (RadialJoinSuspension.leftCoordinates 3) (family.comp g.val)
  rw [standardMap_eq_composite] at h
  exact h

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfPrecomposition
