import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameConnectingHom
import Wikipedia.HomotopyGroupsOfSpheres.Basic

/-!
# Exactness constructions for the balanced frame projection

A null-homotopy of an orthogonal frame family in the total Stiefel space
produces a preimage under the connecting map. Conversely, a null-homotopy
of the last face closes a lifted cube using the actual right orthogonal action.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open NoExoticSixSphere.CubeFirstCoordinate HopfProblem.SecondHurewicz

variable {n d : ℕ} (A : Stiefel.Space (n + n) n)

def fiberInclusion : C(OrthogonalOperators n, Stiefel.Space (n + n) n) :=
  ⟨rightAction A, continuous_rightAction.comp (continuous_const.prodMk continuous_id)⟩

def fiberLoop (q : GenLoop (Fin d) (OrthogonalOperators n) 1) :
    GenLoop (Fin d) (Stiefel.Space (n + n) n) A :=
  ⟨(fiberInclusion A).comp q.val, fun u hu ↦ by
    change rightAction A (q u) = A
    have hq : q u = 1 := q.property u hu
    rw [hq, rightAction_one]⟩

theorem exists_connecting_of_nullhomotopic (q : GenLoop (Fin d) (OrthogonalOperators n) 1)
    (hq : GenLoop.Homotopic (fiberLoop A q) GenLoop.const) :
    ∃ p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A),
      connecting A d (⟦p⟧ : HomotopyGroup (Fin (d + 1)) (Space n) (toBalanced A)) =
        (⟦q⟧ : HomotopyGroup (Fin d) (OrthogonalOperators n) 1) := by
  obtain ⟨H⟩ := hq
  let F := H.symm
  let p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A) :=
    ⟨(map n).comp (F.toContinuousMap.comp (split d)), by
      intro u hu
      change toBalanced (F (split d u)) = toBalanced A
      rcases (boundary_split_iff d u).mp hu with h₀ | h₁ | hb
      · change toBalanced (F ((split d u).1, (split d u).2)) = toBalanced A
        rw [h₀]
        exact congrArg toBalanced (F.map_zero_left _)
      · change toBalanced (F ((split d u).1, (split d u).2)) = toBalanced A
        rw [h₁]
        exact (congrArg toBalanced (F.map_one_left _)).trans (toBalanced_rightAction A _)
      · exact congrArg toBalanced (F.eq_fst (split d u).1 hb)⟩
  let L : CubeLift A p := {
    map := F.toContinuousMap
    initial := F.map_zero_left
    project := fun t u ↦ by
      change toBalanced (F (t, u)) = toBalanced (F (split d (join d (t, u))))
      rw [split_join]
    boundary := fun t u hu ↦ F.eq_fst t hu }
  have he : L.endpoint = q := by
    apply GenLoop.ext
    intro u
    change coordinate A (F (1, u)) (L.endpoint_project u).symm = q u
    have hF : F (1, u) = rightAction A (q u) := F.map_one_left u
    simp only [hF, coordinate_rightAction]
  exact ⟨p, (connecting_eq_endpoint A p L).trans (congrArg Quotient.mk' he)⟩

theorem exists_closed_lift {p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A)}
    (L : CubeLift A p) (h : GenLoop.Homotopic L.endpoint GenLoop.const) :
    ∃ q : GenLoop (Fin (d + 1)) (Stiefel.Space (n + n) n) A,
      mapGenLoop (map n) A q = p := by
  obtain ⟨H⟩ := h
  let F := H.symm
  let M : C(I × (Fin d → I), Stiefel.Space (n + n) n) :=
    ⟨fun z ↦ rightAction (L.map z) (F z)⁻¹,
      continuous_rightAction.comp (L.map.continuous.prodMk F.continuous.inv)⟩
  have hM₀ (u : Fin d → I) : M (0, u) = A := by
    have hF : F (0, u) = (1 : OrthogonalOperators n) := F.map_zero_left u
    change rightAction (L.map (0, u)) (F (0, u))⁻¹ = A
    rw [L.initial, hF, inv_one, rightAction_one]
  have hM₁ (u : Fin d → I) : M (1, u) = A := by
    have hF : F (1, u) = L.endpoint u := F.map_one_left u
    have hL : rightAction A (L.endpoint u) = L.map (1, u) :=
      rightAction_coordinate A _ (L.endpoint_project u).symm
    change rightAction (L.map (1, u)) (F (1, u))⁻¹ = A
    rw [hF, ← hL, ← rightAction_mul, mul_inv_cancel, rightAction_one]
  have hMb (t : I) (u : Fin d → I) (hu : u ∈ Cube.boundary (Fin d)) : M (t, u) = A := by
    have hF : F (t, u) = (1 : OrthogonalOperators n) := F.eq_fst t hu
    change rightAction (L.map (t, u)) (F (t, u))⁻¹ = A
    rw [L.boundary t u hu, hF, inv_one, rightAction_one]
  have hMp (t : I) (u : Fin d → I) : toBalanced (M (t, u)) = p (join d (t, u)) :=
    (toBalanced_rightAction (L.map (t, u)) (F (t, u))⁻¹).trans (L.project t u)
  let q : GenLoop (Fin (d + 1)) (Stiefel.Space (n + n) n) A :=
    ⟨M.comp (split d), by
      intro u hu
      change M (split d u) = A
      rcases (boundary_split_iff d u).mp hu with h₀ | h₁ | hb
      · change M ((split d u).1, (split d u).2) = A
        rw [h₀]
        exact hM₀ _
      · change M ((split d u).1, (split d u).2) = A
        rw [h₁]
        exact hM₁ _
      · exact hMb _ _ hb⟩
  refine ⟨q, ?_⟩
  apply GenLoop.ext
  intro u
  exact (hMp (split d u).1 (split d u).2).trans (congrArg p (join_split d u))

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection
