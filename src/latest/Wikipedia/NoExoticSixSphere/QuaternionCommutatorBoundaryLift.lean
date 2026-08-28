import Wikipedia.NoExoticSixSphere.QuaternionCommutatorRotation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicConnecting
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionSamelson
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-!
# A genuine quaternionic fibration lift with Samelson boundary

Reversing the explicit diagonal rotation starts at the identity and
ends at the included quaternion commutator. Projection therefore gives
a native seven-loop, with all boundary faces fixed. Its actual
connecting class is the Samelson product of the two input three-loops.
No degree or generation assertion is made for this seven-loop.
-/

noncomputable section

open scoped Topology unitInterval commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorBoundaryLift

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres
open QuaternionicFibration QuaternionCommutatorRotation CubeFirstCoordinate

def blockCoordinates : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

def cubePair (p q : GenLoop (Fin 3) UnitQuaternions 1) :
    C((Fin 6 → I), UnitQuaternions × UnitQuaternions) where
  toFun u := (p (fun i ↦ u (blockCoordinates (Sum.inl i))),
    q (fun i ↦ u (blockCoordinates (Sum.inr i))))
  continuous_toFun :=
    (p.val.continuous.comp
      (continuous_pi (fun i ↦ continuous_apply (blockCoordinates (Sum.inl i))))).prodMk
        (q.val.continuous.comp
          (continuous_pi (fun i ↦ continuous_apply (blockCoordinates (Sum.inr i)))))

theorem cubePair_boundary (p q : GenLoop (Fin 3) UnitQuaternions 1)
    (u : Fin 6 → I) (hu : u ∈ Cube.boundary (Fin 6)) :
    (cubePair p q u).1 = 1 ∨ (cubePair p q u).2 = 1 := by
  have hb : (u ∘ blockCoordinates) ∈ Cube.boundary (Fin 3 ⊕ Fin 3) := by
    obtain ⟨i, hi⟩ := hu
    refine ⟨blockCoordinates.symm i, ?_⟩
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi
  rcases Cube.boundary_sum_iff.mp hb with h | h
  · exact Or.inl (p.property _ h)
  · exact Or.inr (q.property _ h)

def commutatorLoop (p q : GenLoop (Fin 3) UnitQuaternions 1) :
    GenLoop (Fin 6) UnitQuaternions 1 :=
  GenLoop.congr 1 finSumFinEquiv (Samelson.loop p q)

theorem commutatorLoop_apply (p q : GenLoop (Fin 3) UnitQuaternions 1) (u : Fin 6 → I) :
    commutatorLoop p q u = ⁅(cubePair p q u).1, (cubePair p q u).2⁆ := rfl

def contractionMap : C(I × (UnitQuaternions × UnitQuaternions), SpTwo) :=
  ⟨fun z ↦ contraction z.1 z.2.1 z.2.2, continuous_contraction⟩

def liftMap (p q : GenLoop (Fin 3) UnitQuaternions 1) : C(I × (Fin 6 → I), SpTwo) :=
  contractionMap.comp
    ⟨fun z ↦ (unitInterval.symm z.1, cubePair p q z.2),
      (unitInterval.continuous_symm.comp continuous_fst).prodMk
        ((cubePair p q).continuous.comp continuous_snd)⟩

theorem liftMap_initial (p q : GenLoop (Fin 3) UnitQuaternions 1) (u : Fin 6 → I) :
    liftMap p q (0, u) = 1 := by
  change contraction (unitInterval.symm 0) (cubePair p q u).1 (cubePair p q u).2 = 1
  rw [unitInterval.symm_zero, contraction_one]

theorem liftMap_terminal (p q : GenLoop (Fin 3) UnitQuaternions 1) (u : Fin 6 → I) :
    liftMap p q (1, u) = fiberInclusion (commutatorLoop p q u) := by
  change contraction (unitInterval.symm 1) (cubePair p q u).1 (cubePair p q u).2 = _
  rw [unitInterval.symm_one, contraction_zero, commutatorLoop_apply]

theorem liftMap_boundary (p q : GenLoop (Fin 3) UnitQuaternions 1)
    (t : I) (u : Fin 6 → I) (hu : u ∈ Cube.boundary (Fin 6)) :
    liftMap p q (t, u) = 1 :=
  contraction_fatWedge (unitInterval.symm t) _ _ (cubePair_boundary p q u hu)

attribute [local irreducible] liftMap

def projectedLoop (p q : GenLoop (Fin 3) UnitQuaternions 1) :
    GenLoop (Fin 7) BaseSphere north :=
  ⟨projection.comp ((liftMap p q).comp (split 6)), fun u hu ↦ by
    change projection (liftMap p q (split 6 u)) = north
    rcases (boundary_split_iff 6 u).mp hu with h | h | h
    · have he : split 6 u = (0, (split 6 u).2) := Prod.ext h rfl
      rw [he, liftMap_initial, projection_one]
    · have he : split 6 u = (1, (split 6 u).2) := Prod.ext h rfl
      rw [he, liftMap_terminal, projection_fiberInclusion]
    · exact (congrArg projection (liftMap_boundary p q _ _ h)).trans projection_one⟩

def cubeLift (p q : GenLoop (Fin 3) UnitQuaternions 1) : CubeLift (projectedLoop p q) where
  map := liftMap p q
  initial := liftMap_initial p q
  project t u := by
    change projection (liftMap p q (t, u)) = projection (liftMap p q (split 6 (join 6 (t, u))))
    rw [split_join]
  boundary := liftMap_boundary p q

def fiberLoop (p q : GenLoop (Fin 3) UnitQuaternions 1) :
    GenLoop (Fin 6) northSubgroup 1 :=
  ⟨⟨fun u ↦ northFiberMulEquiv (commutatorLoop p q u),
      northFiberHomeomorph.continuous.comp (commutatorLoop p q).val.continuous⟩,
    fun u hu ↦ (congrArg northFiberMulEquiv ((commutatorLoop p q).property u hu)).trans
      (map_one northFiberMulEquiv)⟩

theorem endpoint_eq_fiberLoop (p q : GenLoop (Fin 3) UnitQuaternions 1) :
    (cubeLift p q).endpoint = fiberLoop p q := by
  apply GenLoop.ext
  intro u
  apply Subtype.ext
  exact liftMap_terminal p q u

theorem connecting_projectedLoop (p q : GenLoop (Fin 3) UnitQuaternions 1) :
    connecting 6 (⟦projectedLoop p q⟧ : π_ 7 BaseSphere north) =
      (⟦fiberLoop p q⟧ : π_ 6 northSubgroup 1) := by
  rw [connecting_eq_endpoint _ (cubeLift p q), endpoint_eq_fiberLoop]

def fiberEquiv : π_ 6 UnitQuaternions 1 ≃* π_ 6 northSubgroup 1 :=
  pointedHomeomorphMulEquiv (N := Fin 6) northFiberHomeomorph 1 (1 : northSubgroup)
    (map_one northFiberMulEquiv)

theorem fiberLoop_class (p q : GenLoop (Fin 3) UnitQuaternions 1) :
    (⟦fiberLoop p q⟧ : π_ 6 northSubgroup 1) =
      fiberEquiv (QuaternionSamelson.pairing ⟦p⟧ ⟦q⟧) := by
  exact (pointedHomeomorphMulEquiv_mk northFiberHomeomorph 1 (1 : northSubgroup)
    (map_one northFiberMulEquiv) (commutatorLoop p q)).symm

theorem connecting_projectedLoop_pairing (p q : GenLoop (Fin 3) UnitQuaternions 1) :
    connecting 6 (⟦projectedLoop p q⟧ : π_ 7 BaseSphere north) =
      fiberEquiv (QuaternionSamelson.pairing ⟦p⟧ ⟦q⟧) :=
  (connecting_projectedLoop p q).trans (fiberLoop_class p q)

def fundamentalProjectedLoop : GenLoop (Fin 7) BaseSphere north :=
  projectedLoop QuaternionSamelson.fundamentalLoop QuaternionSamelson.fundamentalLoop

theorem fundamental_endpoint (u : Fin 6 → I) :
    (cubeLift QuaternionSamelson.fundamentalLoop QuaternionSamelson.fundamentalLoop).endpoint u =
      northFiberMulEquiv (QuaternionSamelson.nuLoop u) := by
  rw [endpoint_eq_fiberLoop]
  rfl

theorem connecting_fundamentalProjectedLoop :
    connecting 6 (⟦fundamentalProjectedLoop⟧ : π_ 7 BaseSphere north) =
      fiberEquiv QuaternionSamelson.nu := by
  exact (connecting_projectedLoop_pairing
    QuaternionSamelson.fundamentalLoop QuaternionSamelson.fundamentalLoop).trans
      (congrArg (fun a ↦ fiberEquiv (QuaternionSamelson.pairing a a))
        QuaternionSamelson.fundamentalLoop_class)

end NoExoticSixSphere.QuaternionCommutatorBoundaryLift
