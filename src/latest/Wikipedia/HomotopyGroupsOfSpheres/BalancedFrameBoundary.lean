import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameLifting
import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameCoordinates
import Wikipedia.NoExoticSixSphere.CubeFirstCoordinate

/-!
# Cubical boundary representatives for the balanced frame projection

Lift a based cube with its initial and side faces fixed. Its last face
has orthogonal coordinates relative to the initial frame. Coordinate
changes between two lifts give a based homotopy of their last faces.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open NoExoticSixSphere.CubeFirstCoordinate

variable {n d : ℕ}

structure CubeLift (A : Stiefel.Space (n + n) n)
    (p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A)) where
  map : C(I × (Fin d → I), Stiefel.Space (n + n) n)
  initial : ∀ u, map (0, u) = A
  project : ∀ t u, toBalanced (map (t, u)) = p (join d (t, u))
  boundary : ∀ t u, u ∈ Cube.boundary (Fin d) → map (t, u) = A

theorem cubeLift_nonempty (A : Stiefel.Space (n + n) n)
    (p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A)) : Nonempty (CubeLift A p) := by
  have hp₀ (u : Fin d → I) : p (join d (0, u)) = toBalanced A :=
    p.property _ ((boundary_join_iff d _).mpr (Or.inl rfl))
  obtain ⟨L, hL₀, hLp, hLfix⟩ := exists_homotopy_lift
    (p.val.comp (join d)) (ContinuousMap.const _ A) (fun u ↦ (hp₀ u).symm)
  refine ⟨⟨L, hL₀, hLp, ?_⟩⟩
  intro t u hu
  exact hLfix u (fun s ↦
    (p.property _ ((boundary_join_iff d _).mpr (Or.inr (Or.inr hu)))).trans (hp₀ u).symm) t

namespace CubeLift

variable {A : Stiefel.Space (n + n) n}
variable {p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A)} (L : CubeLift A p)

theorem endpoint_project (u : Fin d → I) : toBalanced (L.map (1, u)) = toBalanced A :=
  (L.project 1 u).trans
    (p.property _ ((boundary_join_iff d _).mpr (Or.inr (Or.inl rfl))))

def endpoint : GenLoop (Fin d) (OrthogonalOperators n) 1 :=
  ⟨⟨fun u ↦ coordinate A (L.map (1, u)) (L.endpoint_project u).symm,
      continuous_coordinate_family (fun _ ↦ A) (fun u ↦ L.map (1, u)) continuous_const
        (L.map.continuous.comp (continuous_const.prodMk continuous_id)) _⟩,
    fun u hu ↦ by
      change coordinate A (L.map (1, u)) (L.endpoint_project u).symm = 1
      simp only [L.boundary 1 u hu, coordinate_self]⟩

variable (K : CubeLift A p)

theorem difference_project (t : I) (u : Fin d → I) :
    toBalanced (L.map (t, u)) = toBalanced (K.map (t, u)) :=
  (L.project t u).trans (K.project t u).symm

def difference : C(I × (Fin d → I), OrthogonalOperators n) :=
  ⟨fun z ↦ coordinate (L.map z) (K.map z) (L.difference_project K z.1 z.2),
    continuous_coordinate_family L.map K.map L.map.continuous K.map.continuous _⟩

def endpointHomotopy : L.endpoint.val.HomotopyRel K.endpoint.val (Cube.boundary (Fin d)) where
  toFun z := L.endpoint z.2 * L.difference K z
  continuous_toFun :=
    (L.endpoint.val.continuous.comp continuous_snd).mul (L.difference K).continuous
  map_zero_left u := by
    change L.endpoint u * coordinate (L.map (0, u)) (K.map (0, u))
      (L.difference_project K 0 u) = L.endpoint u
    simp only [L.initial, K.initial, coordinate_self, mul_one]
  map_one_left u := coordinate_mul A (L.map (1, u)) (K.map (1, u))
    (L.endpoint_project u).symm (L.difference_project K 1 u) (K.endpoint_project u).symm
  prop' t u hu := by
    change L.endpoint u * coordinate (L.map (t, u)) (K.map (t, u))
      (L.difference_project K t u) = L.endpoint u
    simp only [L.boundary t u hu, K.boundary t u hu, coordinate_self, mul_one]

theorem endpoint_homotopic : GenLoop.Homotopic L.endpoint K.endpoint :=
  ⟨L.endpointHomotopy K⟩

end CubeLift

def chosenLift (A : Stiefel.Space (n + n) n)
    (p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A)) : CubeLift A p :=
  Classical.choice (cubeLift_nonempty A p)

def boundaryLoop (A : Stiefel.Space (n + n) n)
    (p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A)) :
    GenLoop (Fin d) (OrthogonalOperators n) 1 := (chosenLift A p).endpoint

theorem boundaryLoop_homotopic_endpoint (A : Stiefel.Space (n + n) n)
    (p : GenLoop (Fin (d + 1)) (Space n) (toBalanced A)) (L : CubeLift A p) :
    GenLoop.Homotopic (boundaryLoop A p) L.endpoint := (chosenLift A p).endpoint_homotopic L

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection
