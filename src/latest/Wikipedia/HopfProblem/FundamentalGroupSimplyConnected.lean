import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Simple connectedness from one fundamental group

In a path-connected space, triviality of the fundamental group at a single
basepoint implies simple connectedness.  We transport loop classes along
actual paths and use the null-homotopic-loop criterion.
-/

noncomputable section

namespace Wikipedia.HopfProblem

variable {X : Type*} [TopologicalSpace X]

/-- Triviality of the fundamental group transports along an actual path. -/
theorem fundamentalGroup_eq_one_of_path {x y : X} (p : Path x y)
    (hx : ∀ g : FundamentalGroup X x, g = 1) (g : FundamentalGroup X y) :
    g = 1 := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath p
  obtain ⟨h, rfl⟩ := e.surjective g
  rw [hx h, map_one]

/-- For a path-connected space, one trivial fundamental group suffices for
simple connectedness. -/
theorem simplyConnectedSpace_iff_fundamentalGroup_eq_one [PathConnectedSpace X]
    (x : X) :
    SimplyConnectedSpace X ↔ ∀ g : FundamentalGroup X x, g = 1 := by
  constructor
  · intro h
    let : SimplyConnectedSpace X := h
    exact fun _ => Subsingleton.elim _ _
  · intro hx
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨inferInstance, ?_⟩
    intro y γ
    exact Path.Homotopic.Quotient.eq.mp
      (fundamentalGroup_eq_one_of_path (PathConnectedSpace.somePath x y) hx
        (Path.Homotopic.Quotient.mk γ))

/-- A direct constructor from triviality at a chosen basepoint. -/
theorem simplyConnectedSpace_of_fundamentalGroup_eq_one [PathConnectedSpace X]
    (x : X) (hx : ∀ g : FundamentalGroup X x, g = 1) :
    SimplyConnectedSpace X :=
  (simplyConnectedSpace_iff_fundamentalGroup_eq_one x).mpr hx

/-- A subsingleton fundamental group at one basepoint gives simple
connectedness in a path-connected space. -/
theorem simplyConnectedSpace_of_fundamentalGroup_subsingleton [PathConnectedSpace X]
    (x : X) [Subsingleton (FundamentalGroup X x)] : SimplyConnectedSpace X :=
  simplyConnectedSpace_of_fundamentalGroup_eq_one x (fun _ => Subsingleton.elim _ _)

end Wikipedia.HopfProblem
