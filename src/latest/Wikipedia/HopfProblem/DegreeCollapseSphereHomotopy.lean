import Wikipedia.HopfProblem.SixSphereCubeFactorization

/-!
# Descending actual cube homotopies to the literal six-sphere

The product of the cube-collapse quotient with the time interval is a
quotient map, by compactness. A homotopy fixed on the whole cube boundary
therefore descends to a homotopy fixed at the actual sphere base point.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse

open SixSphereCube

/-- Time is unchanged; only the original cube boundary is collapsed. -/
def cylinderQuotient : C(I × (Fin 6 → I), I × StandardSphere) :=
  (ContinuousMap.id I).prodMap cubeSphereMap

theorem cylinderQuotient_surjective : Function.Surjective cylinderQuotient := by
  rintro ⟨t, z⟩
  obtain ⟨u, rfl⟩ := cubeSphereMap_surjective z
  exact ⟨(t, u), rfl⟩

theorem cylinderQuotient_isQuotientMap : IsQuotientMap cylinderQuotient :=
  .of_surjective_continuous cylinderQuotient_surjective cylinderQuotient.continuous

variable {X : Type*} [TopologicalSpace X] {x : X}
  {p q : GenLoop (Fin 6) X x}
  (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6)))

theorem cubeHomotopy_constant_on_cylinderFibres
    (a b : I × (Fin 6 → I)) (h : cylinderQuotient a = cylinderQuotient b) :
    H a = H b := by
  rcases a with ⟨t, u⟩
  rcases b with ⟨s, v⟩
  have ht : t = s := congrArg Prod.fst h
  subst s
  have huv : cubeSphereMap u = cubeSphereMap v := congrArg Prod.snd h
  rcases (cubeSphereMap_eq_iff u v).mp huv with rfl | ⟨hu, hv⟩
  · rfl
  · exact ((H.eq_fst t hu).trans (p.property u hu)).trans
      ((H.eq_fst t hv).trans (p.property v hv)).symm

/-- A jointly continuous family on the sphere, obtained by genuine quotient descent. -/
def cubeHomotopyLift : C(I × StandardSphere, X) :=
  cylinderQuotient_isQuotientMap.lift H.toHomotopy.toContinuousMap
    (cubeHomotopy_constant_on_cylinderFibres H)

@[simp] theorem cubeHomotopyLift_apply (t : I) (u : Fin 6 → I) :
    cubeHomotopyLift H (t, cubeSphereMap u) = H (t, u) :=
  ContinuousMap.congr_fun
    (cylinderQuotient_isQuotientMap.lift_comp H.toHomotopy.toContinuousMap
      (cubeHomotopy_constant_on_cylinderFibres H)) (t, u)

/-- The descended homotopy is fixed at the same distinguished sphere point. -/
def factorHomotopy :
    (factorMap p).HomotopyRel (factorMap q) {sphereBasePoint} where
  toContinuousMap := cubeHomotopyLift H
  map_zero_left z := by
    obtain ⟨u, rfl⟩ := cubeSphereMap_surjective z
    change cubeHomotopyLift H (0, cubeSphereMap u) = factorMap p (cubeSphereMap u)
    rw [cubeHomotopyLift_apply, H.apply_zero, factorMap_cubeSphereMap]
    rfl
  map_one_left z := by
    obtain ⟨u, rfl⟩ := cubeSphereMap_surjective z
    change cubeHomotopyLift H (1, cubeSphereMap u) = factorMap q (cubeSphereMap u)
    rw [cubeHomotopyLift_apply, H.apply_one, factorMap_cubeSphereMap]
    rfl
  prop' t z hz := by
    have hz' : z = sphereBasePoint := hz
    subst z
    change cubeHomotopyLift H (t, sphereBasePoint) = factorMap p sphereBasePoint
    rw [← cubeSphereMap_boundary 0 zero_mem_cubeBoundary, cubeHomotopyLift_apply]
    rw [H.eq_fst t zero_mem_cubeBoundary, factorMap_cubeSphereMap]
    rfl

/-- Native boundary-relative cube homotopy gives native based sphere homotopy. -/
theorem factorMap_homotopicRel (h : GenLoop.Homotopic p q) :
    (factorMap p).HomotopicRel (factorMap q) {sphereBasePoint} := by
  obtain ⟨H⟩ := h
  exact ⟨factorHomotopy H⟩

end Wikipedia.HopfProblem.DegreeCollapse
