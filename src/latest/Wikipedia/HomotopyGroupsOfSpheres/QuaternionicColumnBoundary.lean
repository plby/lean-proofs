import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnLifting
import Wikipedia.NoExoticSixSphere.CubeFirstCoordinate

/-!
# Cubical boundary representatives for the quaternionic fibration

A based `(n+1)`-cube lifts with its initial and side faces fixed. Its last
face is a based `n`-cube in the actual fiber subgroup. Any two such lifts
give homotopic last faces: their pointwise quotient lies in the fiber.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.CubeFirstCoordinate

variable {N : Type} [Fintype N] [DecidableEq N] {j : N}
variable {n : ℕ}

/-- A cubical lift with the initial face and all side faces fixed. -/
structure CubeLift (p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j)) where
  map : C(I × (Fin n → I), (SpGroup N))
  initial : ∀ u, map (0, u) = 1
  project : ∀ t u, (column j) (map (t, u)) = p (join n (t, u))
  boundary : ∀ t u, u ∈ Cube.boundary (Fin n) → map (t, u) = 1

theorem cubeLift_nonempty (p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j)) :
    Nonempty (CubeLift p) := by
  have hp₀ (u : Fin n → I) : p (join n (0, u)) = (axisColumn j) :=
    p.property _ ((boundary_join_iff n _).mpr (Or.inl rfl))
  obtain ⟨L, hL₀, hLp, hLfix⟩ := exists_homotopy_lift j
    (p.val.comp (join n)) (ContinuousMap.const _ 1) (fun u => (column_one j).trans (hp₀ u).symm)
  refine ⟨⟨L, hL₀, hLp, ?_⟩⟩
  intro t u hu
  exact hLfix u (fun s =>
    (p.property _ ((boundary_join_iff n _).mpr (Or.inr (Or.inr hu)))).trans (hp₀ u).symm) t

namespace CubeLift

variable {p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j)} (L : CubeLift p)

theorem endpoint_mem (u : Fin n → I) : L.map (1, u) ∈ (axisSubgroup j) := by
  change (column j) (L.map (1, u)) = (axisColumn j)
  exact (L.project 1 u).trans
    (p.property _ ((boundary_join_iff n _).mpr (Or.inr (Or.inl rfl))))

/-- The last face, regarded as a loop in the actual stabilizer subgroup. -/
def endpoint : GenLoop (Fin n) (axisSubgroup j) 1 :=
  ⟨⟨fun u => ⟨L.map (1, u), L.endpoint_mem u⟩,
      (L.map.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩,
    fun u hu => Subtype.ext (L.boundary 1 u hu)⟩

variable (K : CubeLift p)

theorem difference_mem (t : I) (u : Fin n → I) :
    (L.map (t, u))⁻¹ * K.map (t, u) ∈ (axisSubgroup j) := by
  apply (column_inv_mul_eq_axis_iff j _ _).mpr
  exact (L.project t u).trans (K.project t u).symm

/-- The pointwise quotient of two lifts is a continuous family in the fiber. -/
def difference : C(I × (Fin n → I), (axisSubgroup j)) :=
  ⟨fun z => ⟨(L.map z)⁻¹ * K.map z, L.difference_mem K z.1 z.2⟩,
    (L.map.continuous.inv.mul K.map.continuous).subtype_mk _⟩

/-- Any two lifts have homotopic endpoints, without a uniqueness assumption on path lifting. -/
def endpointHomotopy : L.endpoint.val.HomotopyRel K.endpoint.val (Cube.boundary (Fin n)) where
  toFun z := L.endpoint z.2 * L.difference K z
  continuous_toFun :=
    (L.endpoint.val.continuous.comp continuous_snd).mul (L.difference K).continuous
  map_zero_left u := by
    apply Subtype.ext
    change L.map (1, u) * ((L.map (0, u))⁻¹ * K.map (0, u)) = L.map (1, u)
    rw [L.initial, K.initial, inv_one, one_mul, mul_one]
  map_one_left u := by
    apply Subtype.ext
    change L.map (1, u) * ((L.map (1, u))⁻¹ * K.map (1, u)) = K.map (1, u)
    exact mul_inv_cancel_left _ _
  prop' t u hu := by
    apply Subtype.ext
    change L.map (1, u) * ((L.map (t, u))⁻¹ * K.map (t, u)) = L.map (1, u)
    rw [L.boundary t u hu, K.boundary t u hu, inv_one, one_mul, mul_one]

theorem endpoint_homotopic : GenLoop.Homotopic L.endpoint K.endpoint :=
  ⟨L.endpointHomotopy K⟩

end CubeLift

/-- A lift chosen from the proved compact homotopy-lifting theorem. -/
def chosenLift (p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j)) : CubeLift p :=
  Classical.choice (cubeLift_nonempty p)

/-- The connecting-map representative on genuine based cubes. -/
def boundaryLoop (p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j)) :
    GenLoop (Fin n) (axisSubgroup j) 1 := (chosenLift p).endpoint

theorem boundaryLoop_homotopic_endpoint (p : GenLoop (Fin (n + 1)) (UnitColumn N) (axisColumn j))
    (L : CubeLift p) : GenLoop.Homotopic (boundaryLoop p) L.endpoint :=
  (chosenLift p).endpoint_homotopic L

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
