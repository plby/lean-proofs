import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# The universal rectangle track for cubical whiskering

The parametrization is the literal native path concatenation: the first
arm occupies the first half, the middle occupies the next quarter, and
the reversed final arm occupies the final quarter.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

/-- The first vertical edge of the universal whiskering rectangle. -/
def whiskerStartTrack : Path ((0 : I), (0 : I)) ((0 : I), (1 : I)) where
  toFun s := (0, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The horizontal edge of the universal whiskering rectangle. -/
def whiskerMiddleTrack : Path ((0 : I), (1 : I)) ((1 : I), (1 : I)) where
  toFun s := (s, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The last vertical edge, oriented upwards before reversal. -/
def whiskerFinishTrack : Path ((1 : I), (0 : I)) ((1 : I), (1 : I)) where
  toFun s := (1, s)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The actual concatenated track, with native breakpoints `1/2` and `3/4`. -/
def whiskerTrack : Path ((0 : I), (0 : I)) ((1 : I), (0 : I)) :=
  whiskerStartTrack.trans (whiskerMiddleTrack.trans whiskerFinishTrack.symm)

@[simp] theorem whiskerTrack_zero : whiskerTrack 0 = ((0 : I), (0 : I)) :=
  whiskerTrack.source

@[simp] theorem whiskerTrack_one : whiskerTrack 1 = ((1 : I), (0 : I)) :=
  whiskerTrack.target

/-- Every track point is on one of the two vertical edges or the upper edge. -/
theorem whiskerTrack_boundary (s : I) :
    ((whiskerTrack s).1 = 0 ∨ (whiskerTrack s).1 = 1) ∨ (whiskerTrack s).2 = 1 := by
  unfold whiskerTrack
  rw [Path.trans_apply]
  split_ifs
  · exact Or.inl (Or.inl rfl)
  · rw [Path.trans_apply]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl (Or.inr rfl)

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
