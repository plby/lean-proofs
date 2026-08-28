import Wikipedia.NoExoticSixSphere.QuaternionicHopfFiberAction
import Wikipedia.NoExoticSixSphere.QuaternionicHopfLocalTransport
import Wikipedia.NoExoticSixSphere.CubeFirstCoordinate

/-!
# Boundary cubes of the explicit quaternionic Hopf fibration

Every based cube lifts with its initial and side faces fixed. The terminal
face is expressed in the actual unit-quaternion fiber. Continuous fiber
division proves that any two lifts have relatively homotopic terminal faces.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

open CubeFirstCoordinate

variable {n : ℕ}

structure CubeLift (p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)) where
  map : C(I × (Fin n → I), Sphere 7)
  initial : ∀ u, map (0, u) = spherePole 7
  project : ∀ t u, sphereMap (map (t, u)) = p (join n (t, u))
  boundary : ∀ t u, u ∈ Cube.boundary (Fin n) → map (t, u) = spherePole 7

theorem cubeLift_nonempty (p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)) :
    Nonempty (CubeLift p) := by
  have hp₀ (u : Fin n → I) : p (join n (0, u)) = spherePole 4 :=
    p.property _ ((boundary_join_iff n _).mpr (Or.inl rfl))
  obtain ⟨L, hL₀, hLp, hLfix⟩ := exists_homotopy_lift
    (p.val.comp (join n)) (ContinuousMap.const _ (spherePole 7))
      (fun u ↦ sphereMap_pole.trans (hp₀ u).symm)
  refine ⟨⟨L, hL₀, hLp, ?_⟩⟩
  intro t u hu
  exact hLfix u (fun s ↦
    (p.property _ ((boundary_join_iff n _).mpr (Or.inr (Or.inr hu)))).trans (hp₀ u).symm) t

namespace CubeLift

variable {p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)} (L : CubeLift p)

theorem endpoint_mem (u : Fin n → I) : sphereMap (L.map (1, u)) = spherePole 4 :=
  (L.project 1 u).trans
    (p.property _ ((boundary_join_iff n _).mpr (Or.inr (Or.inl rfl))))

def endpoint : GenLoop (Fin n) FiberGroup 1 :=
  ⟨⟨fun u ↦ unitFiberCoordinate (L.map (1, u)) (L.endpoint_mem u),
      continuous_unitFiberCoordinate (L.map.comp ⟨fun u ↦ (1, u),
        continuous_const.prodMk continuous_id⟩) L.endpoint_mem⟩,
    fun u hu ↦ by
      apply unitFiberPoint_injective
      change unitFiberPoint (unitFiberCoordinate (L.map (1, u)) _) = unitFiberPoint 1
      rw [unitFiberPoint_coordinate, L.boundary 1 u hu, unitFiberPoint_one]⟩

theorem endpoint_point (u : Fin n → I) : unitFiberPoint (L.endpoint u) = L.map (1, u) :=
  unitFiberPoint_coordinate _ _

variable (K : CubeLift p)

def difference : C(I × (Fin n → I), FiberGroup) :=
  ⟨fun z ↦ fiberDivision (L.map z) (K.map z) ((L.project z.1 z.2).trans (K.project z.1 z.2).symm),
    continuous_fiberDivision L.map K.map
      (fun z ↦ (L.project z.1 z.2).trans (K.project z.1 z.2).symm)⟩

theorem difference_initial (u : Fin n → I) : L.difference K (0, u) = 1 := by
  apply Subtype.ext
  change divisionQuaternion (L.map (0, u)).val (K.map (0, u)).val = 1
  rw [L.initial, K.initial, divisionQuaternion_self]

theorem difference_boundary (t : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
    L.difference K (t, u) = 1 := by
  apply Subtype.ext
  change divisionQuaternion (L.map (t, u)).val (K.map (t, u)).val = 1
  rw [L.boundary t u hu, K.boundary t u hu, divisionQuaternion_self]

def endpointHomotopy : L.endpoint.val.HomotopyRel K.endpoint.val (Cube.boundary (Fin n)) where
  toFun z := L.endpoint z.2 * L.difference K z
  continuous_toFun :=
    (L.endpoint.val.continuous.comp continuous_snd).mul (L.difference K).continuous
  map_zero_left u := by
    change L.endpoint u * L.difference K (0, u) = L.endpoint u
    rw [L.difference_initial K, mul_one]
  map_one_left u := by
    change L.endpoint u * L.difference K (1, u) = K.endpoint u
    apply unitFiberPoint_injective
    rw [unitFiberPoint_mul, L.endpoint_point, K.endpoint_point]
    exact rightAction_fiberDivision _ _ ((L.project 1 u).trans (K.project 1 u).symm)
  prop' t u hu := by
    change L.endpoint u * L.difference K (t, u) = L.endpoint u
    rw [L.difference_boundary K t u hu, mul_one]

theorem endpoint_homotopic : GenLoop.Homotopic L.endpoint K.endpoint :=
  ⟨L.endpointHomotopy K⟩

end CubeLift

def chosenLift (p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)) : CubeLift p :=
  Classical.choice (cubeLift_nonempty p)

def boundaryLoop (p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)) :
    GenLoop (Fin n) FiberGroup 1 := (chosenLift p).endpoint

theorem boundaryLoop_homotopic_endpoint
    (p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)) (L : CubeLift p) :
    GenLoop.Homotopic (boundaryLoop p) L.endpoint := (chosenLift p).endpoint_homotopic L

end NoExoticSixSphere.QuaternionicHopf
