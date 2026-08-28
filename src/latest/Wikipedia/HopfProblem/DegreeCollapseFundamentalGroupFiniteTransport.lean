import Wikipedia.SmoothSixDPoincare.FundamentalGroupMapTools
import Mathlib.GroupTheory.Finiteness

/-!

# Finite generation along actual paths and homotopy equivalences

Basepoint changes use the specified path isomorphism. For a homotopy
equivalence, the actual induced map gives the first isomorphism and the
original inverse homotopy supplies the path to the requested target
basepoint. No replacement fundamental group is introduced.
-/

noncomputable section

open Function ContinuousMap FundamentalGroup

namespace Wikipedia.HopfProblem.DegreeCollapse.FundamentalGroupFiniteness

open Wikipedia.SmoothSixDPoincare

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem of_path {x y : X} (p : Path x y) [Group.FG (FundamentalGroup X x)] :
    Group.FG (FundamentalGroup X y) :=
  Group.fg_of_surjective (f := (fundamentalGroupMulEquivOfPath p).toMonoidHom)
    (fundamentalGroupMulEquivOfPath p).surjective

theorem of_pathConnected [PathConnectedSpace X] (x : X)
    [Group.FG (FundamentalGroup X x)] (y : X) : Group.FG (FundamentalGroup X y) :=
  of_path (PathConnectedSpace.somePath x y)

theorem of_homotopyEquiv (e : X ≃ₕ Y)
    (hX : ∀ x : X, Group.FG (FundamentalGroup X x)) (y : Y) :
    Group.FG (FundamentalGroup Y y) := by
  let : Group.FG (FundamentalGroup X (e.invFun y)) := hX _
  let : Group.FG (FundamentalGroup Y ((e.toFun.comp e.invFun) y)) :=
    Group.fg_of_surjective (f := FundamentalGroup.map e.toFun (e.invFun y))
      (FundamentalGroupTools.map_bijective_of_homotopyEquiv e (e.invFun y)).surjective
  exact of_path (e.right_inv.some.evalAt y)

end Wikipedia.HopfProblem.DegreeCollapse.FundamentalGroupFiniteness
