import Wikipedia.NoExoticSixSphere.QuaternionicHopfFiberExactness

/-!
# Exactness at the base of the explicit quaternionic Hopf map

A nullhomotopy in the quaternionic fiber supplies a right-action
correction that closes the lifted cube while preserving its projection.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

open CubeFirstCoordinate HigherHomotopy

variable {n : ℕ}

def projectionMap (n : ℕ) :
    HomotopyGroup (Fin (n + 1)) (Sphere 7) (spherePole 7) →*
      HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4) :=
  mapMonoidHom sphereMap sphereMap_pole

def projectedCubeLift (q : GenLoop (Fin (n + 1)) (Sphere 7) (spherePole 7)) :
    CubeLift (genLoopMap sphereMap sphereMap_pole q) where
  map := q.val.comp (join n)
  initial _ := q.property _ ((boundary_join_iff n _).mpr (Or.inl rfl))
  project _ _ := rfl
  boundary _ _ hu := q.property _ ((boundary_join_iff n _).mpr (Or.inr (Or.inr hu)))

theorem projectedCubeLift_endpoint (q : GenLoop (Fin (n + 1)) (Sphere 7) (spherePole 7)) :
    (projectedCubeLift q).endpoint = GenLoop.const := by
  apply GenLoop.ext
  intro u
  apply unitFiberPoint_injective
  change unitFiberPoint ((projectedCubeLift q).endpoint u) = unitFiberPoint 1
  rw [CubeLift.endpoint_point, unitFiberPoint_one]
  exact q.property _ ((boundary_join_iff n (1, u)).mpr (Or.inr (Or.inl rfl)))

theorem connecting_projectionMap [NeZero n]
    (a : HomotopyGroup (Fin (n + 1)) (Sphere 7) (spherePole 7)) :
    connecting n (projectionMap n a) = 1 := by
  refine Quotient.inductionOn a fun q ↦ ?_
  change connecting n (⟦genLoopMap sphereMap sphereMap_pole q⟧ :
    HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4)) =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) FiberGroup 1)
  exact (connecting_eq_endpoint _ (projectedCubeLift q)).trans
    (congrArg Quotient.mk' (projectedCubeLift_endpoint q))

namespace CubeLift

variable {p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)} (L : CubeLift p)
  (F : (GenLoop.const : GenLoop (Fin n) FiberGroup 1).val.HomotopyRel
    L.endpoint.val (Cube.boundary (Fin n)))

def correctedMap : C(I × (Fin n → I), Sphere 7) :=
  rightInverseActionMap L.map F.toContinuousMap

theorem correctedMap_initial (u : Fin n → I) : L.correctedMap F (0, u) = spherePole 7 := by
  have hF : F (0, u) = 1 := F.map_zero_left u
  change rightAction (L.map (0, u)) (F (0, u))⁻¹ = spherePole 7
  rw [L.initial, hF, inv_one, rightAction_one]

theorem correctedMap_terminal (u : Fin n → I) : L.correctedMap F (1, u) = spherePole 7 := by
  have hF : F (1, u) = L.endpoint u := F.map_one_left u
  change rightAction (L.map (1, u)) (F (1, u))⁻¹ = spherePole 7
  rw [← L.endpoint_point, hF, ← unitFiberPoint_mul, mul_inv_cancel, unitFiberPoint_one]

theorem correctedMap_boundary (t : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) :
    L.correctedMap F (t, u) = spherePole 7 := by
  have hF : F (t, u) = 1 := F.eq_fst t hu
  change rightAction (L.map (t, u)) (F (t, u))⁻¹ = spherePole 7
  rw [L.boundary t u hu, hF, inv_one, rightAction_one]

theorem correctedMap_project (t : I) (u : Fin n → I) :
    sphereMap (L.correctedMap F (t, u)) = p (join n (t, u)) :=
  (sphereMap_rightAction (L.map (t, u)) (F (t, u))⁻¹).trans (L.project t u)

def closedCube : GenLoop (Fin (n + 1)) (Sphere 7) (spherePole 7) :=
  ⟨(L.correctedMap F).comp (split n), by
    intro u hu
    change L.correctedMap F (split n u) = spherePole 7
    rcases (boundary_split_iff n u).mp hu with h₀ | h₁ | hb
    · change L.correctedMap F ((split n u).1, (split n u).2) = spherePole 7
      rw [h₀]
      exact L.correctedMap_initial F _
    · change L.correctedMap F ((split n u).1, (split n u).2) = spherePole 7
      rw [h₁]
      exact L.correctedMap_terminal F _
    · exact L.correctedMap_boundary F _ _ hb⟩

theorem closedCube_project : genLoopMap sphereMap sphereMap_pole (L.closedCube F) = p := by
  apply GenLoop.ext
  intro u
  exact (L.correctedMap_project F (split n u).1 (split n u).2).trans
    (congrArg p (join_split n u))

end CubeLift

theorem exists_closed_lift {p : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)}
    (L : CubeLift p) (h : GenLoop.Homotopic L.endpoint GenLoop.const) :
    ∃ q : GenLoop (Fin (n + 1)) (Sphere 7) (spherePole 7),
      genLoopMap sphereMap sphereMap_pole q = p := by
  obtain ⟨H⟩ := h
  exact ⟨L.closedCube H.symm, L.closedCube_project H.symm⟩

theorem projectionMap_range_eq_connecting_kernel [NeZero n]
    (a : HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4)) :
    (∃ b : HomotopyGroup (Fin (n + 1)) (Sphere 7) (spherePole 7), projectionMap n b = a) ↔
      connecting n a = 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact connecting_projectionMap b
  · refine Quotient.inductionOn a fun p hp ↦ ?_
    have he : (⟦(chosenLift p).endpoint⟧ : HomotopyGroup (Fin n) FiberGroup 1) =
        ⟦GenLoop.const⟧ := hp
    obtain ⟨q, hq⟩ := exists_closed_lift (chosenLift p) (Quotient.exact he)
    exact ⟨⟦q⟧, congrArg Quotient.mk' hq⟩

end NoExoticSixSphere.QuaternionicHopf
