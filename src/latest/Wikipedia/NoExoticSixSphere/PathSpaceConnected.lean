import Mathlib.Topology.Homotopy.Path
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Path connectedness of the actual loop space of a simply connected space

A fixed-endpoint path homotopy is a path in the native compact-open path
space, by continuity of currying. Simply connectedness then joins any
two based loops in that actual path space.
-/

noncomputable section

namespace NoExoticSixSphere.PathSpaceConnected

variable {X : Type*} [TopologicalSpace X] {x y : X}

def homotopyPath {p q : Path x y} (H : p.Homotopy q) : Path p q where
  toFun := H.eval
  continuous_toFun := Path.continuous_uncurry_iff.mp H.continuous
  source' := H.eval_zero
  target' := H.eval_one

theorem loop_space [SimplyConnectedSpace X] (x : X) : PathConnectedSpace (Path x x) where
  nonempty := ⟨Path.refl x⟩
  joined p q := by
    obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic p q
    exact ⟨homotopyPath H⟩

end NoExoticSixSphere.PathSpaceConnected
