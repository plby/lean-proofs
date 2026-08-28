import Wikipedia.NoExoticSixSphere.LoopSpaceDimensionShift
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The native loop space of a two-connected space

The compact-open topology on `Path x x` is retained. Path connectedness
comes from actual path homotopies. The native dimension shift identifies
its fundamental group at the constant loop with the second homotopy group
of the original space; ordinary change of basepoint handles all other loops.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.OrbitPair

variable {X : Type*} [TopologicalSpace X]

/-- A fixed-endpoint homotopy is a path in the native path space. -/
def pathOfPathHomotopy {x y : X} {p q : Path x y} (H : p.Homotopy q) : Path p q where
  toFun := H.eval
  continuous_toFun := Path.continuous_uncurry_iff.mp H.continuous
  source' := H.eval_zero
  target' := H.eval_one

theorem loopSpace_pathConnected [SimplyConnectedSpace X] (x : X) :
    PathConnectedSpace (Path x x) where
  nonempty := ⟨Path.refl x⟩
  joined p q := by
    obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic p q
    exact ⟨pathOfPathHomotopy H⟩

/-- Vanishing of the original second homotopy group gives simple connectedness
of its actual based-loop space. -/
theorem loopSpace_simplyConnected [SimplyConnectedSpace X] (x : X)
    (h₂ : Subsingleton (π_ 2 X x)) : SimplyConnectedSpace (Path x x) := by
  let := loopSpace_pathConnected x
  let := h₂
  let : Subsingleton (π_ 1 (Path x x) (Path.refl x)) :=
    (NoExoticSixSphere.GeneralizedLoopCurrying.homotopyEquiv 1 x).injective.subsingleton
  let : Subsingleton (FundamentalGroup (Path x x) (Path.refl x)) :=
    HomotopyGroup.pi1EquivFundamentalGroup.symm.injective.subsingleton
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, fun p γ => ?_⟩
  have hp : Subsingleton (FundamentalGroup (Path x x) p) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected p (Path.refl x)).injective.subsingleton
  have he : (⟦γ⟧ : FundamentalGroup (Path x x) p) = ⟦Path.refl p⟧ :=
    hp.elim _ _
  exact Quotient.eq.mp he

end Wikipedia.HopfProblem.OrbitPair
