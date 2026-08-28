import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExactness

/-!
# Exactness at the base for the quaternionic fibration

A based cube in `S⁷` has zero connecting class exactly when its homotopy
class comes from `Sp(2)`. A null-homotopy of the lifted last face provides
a fiber-valued correction that closes the lift without changing its projection.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open NoExoticSixSphere.CubeFirstCoordinate
open HopfProblem.SecondHurewicz

variable {n : ℕ}

theorem projection_mul_fiber (A : SpTwo) (q : northSubgroup) :
    projection (A * q.val) = projection A := by
  rw [← sphereAction_projection, q.property, sphereAction_north]

def projectionMap (n : ℕ) :
    HomotopyGroup (Fin (n + 1)) SpTwo 1 →*
      HomotopyGroup (Fin (n + 1)) BaseSphere north := map projection 1

/-- An actual cube in the total space is itself a lift of its projection. -/
def projectedCubeLift (q : GenLoop (Fin (n + 1)) SpTwo 1) :
    CubeLift (mapGenLoop projection 1 q) where
  map := q.val.comp (join n)
  initial _ := q.property _ ((boundary_join_iff n _).mpr (Or.inl rfl))
  project _ _ := rfl
  boundary _ _ hu := q.property _ ((boundary_join_iff n _).mpr (Or.inr (Or.inr hu)))

theorem projectedCubeLift_endpoint (q : GenLoop (Fin (n + 1)) SpTwo 1) :
    (projectedCubeLift q).endpoint = GenLoop.const := by
  apply GenLoop.ext
  intro u
  apply Subtype.ext
  exact q.property _ ((boundary_join_iff n (1, u)).mpr (Or.inr (Or.inl rfl)))

theorem connecting_projectionMap [NeZero n] (a : HomotopyGroup (Fin (n + 1)) SpTwo 1) :
    connecting n (projectionMap n a) = 1 := by
  refine Quotient.inductionOn a fun q => ?_
  change connecting n (⟦mapGenLoop projection 1 q⟧ :
    HomotopyGroup (Fin (n + 1)) BaseSphere north) = (⟦GenLoop.const⟧ :
      HomotopyGroup (Fin n) northSubgroup 1)
  exact (connecting_eq_endpoint _ (projectedCubeLift q)).trans
    (congrArg Quotient.mk' (projectedCubeLift_endpoint q))

/-- A null-homotopy of the last face closes the lift by a correction in the actual fiber. -/
theorem exists_closed_lift {p : GenLoop (Fin (n + 1)) BaseSphere north}
    (L : CubeLift p) (h : GenLoop.Homotopic L.endpoint GenLoop.const) :
    ∃ q : GenLoop (Fin (n + 1)) SpTwo 1, mapGenLoop projection 1 q = p := by
  obtain ⟨H⟩ := h
  let F := H.symm
  let M : C(I × (Fin n → I), SpTwo) :=
    ⟨fun z => L.map z * (F z).val⁻¹,
      L.map.continuous.mul (continuous_subtype_val.comp F.continuous).inv⟩
  have hM₀ (u : Fin n → I) : M (0, u) = 1 := by
    have hF : (F (0, u)).val = (1 : SpTwo) := congrArg Subtype.val (F.map_zero_left u)
    change L.map (0, u) * (F (0, u)).val⁻¹ = 1
    rw [L.initial, hF, inv_one, one_mul]
  have hM₁ (u : Fin n → I) : M (1, u) = 1 := by
    have hF : (F (1, u)).val = L.map (1, u) := congrArg Subtype.val (F.map_one_left u)
    change L.map (1, u) * (F (1, u)).val⁻¹ = 1
    rw [hF, mul_inv_cancel]
  have hMb (t : I) (u : Fin n → I) (hu : u ∈ Cube.boundary (Fin n)) : M (t, u) = 1 := by
    have hF : (F (t, u)).val = (1 : SpTwo) := congrArg Subtype.val (F.eq_fst t hu)
    change L.map (t, u) * (F (t, u)).val⁻¹ = 1
    rw [L.boundary t u hu, hF, inv_one, one_mul]
  have hMp (t : I) (u : Fin n → I) : projection (M (t, u)) = p (join n (t, u)) :=
    (projection_mul_fiber (L.map (t, u)) (F (t, u))⁻¹).trans (L.project t u)
  let q : GenLoop (Fin (n + 1)) SpTwo 1 :=
    ⟨M.comp (split n), by
      intro u hu
      change M (split n u) = 1
      rcases (boundary_split_iff n u).mp hu with h₀ | h₁ | hb
      · change M ((split n u).1, (split n u).2) = 1
        rw [h₀]
        exact hM₀ _
      · change M ((split n u).1, (split n u).2) = 1
        rw [h₁]
        exact hM₁ _
      · exact hMb _ _ hb⟩
  refine ⟨q, ?_⟩
  apply GenLoop.ext
  intro u
  exact (hMp (split n u).1 (split n u).2).trans (congrArg p (join_split n u))

/-- Exactness at the native homotopy group of the seven-sphere model. -/
theorem projectionMap_range_eq_connecting_kernel [NeZero n]
    (a : HomotopyGroup (Fin (n + 1)) BaseSphere north) :
    (∃ b : HomotopyGroup (Fin (n + 1)) SpTwo 1, projectionMap n b = a) ↔
      connecting n a = 1 := by
  constructor
  · rintro ⟨b, rfl⟩
    exact connecting_projectionMap b
  · refine Quotient.inductionOn a fun p hp => ?_
    have he : (⟦(chosenLift p).endpoint⟧ : HomotopyGroup (Fin n) northSubgroup 1) =
        ⟦GenLoop.const⟧ := hp
    obtain ⟨q, hq⟩ := exists_closed_lift (chosenLift p) (Quotient.exact he)
    exact ⟨⟦q⟧, congrArg Quotient.mk' hq⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
