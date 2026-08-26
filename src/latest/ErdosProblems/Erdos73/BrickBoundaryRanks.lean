import ErdosProblems.Erdos73.BrickWall

/-! An explicit injective rank for the two zigzag boundary columns. -/

namespace Erdos73
noncomputable section

open SimpleGraph

def OnBrickColumnBoundary {c r : ℕ} (w : ElementaryWallVertex c r) : Prop :=
  w.val.2.val ≤ 1 ∨ 2 * (c - 1) ≤ w.val.2.val

def brickBoundaryRank {c r : ℕ} (w : ElementaryWallVertex c r) : ℕ :=
  if w.val.2.val ≤ 1 then 2 * w.val.1.val + (w.val.2.val + w.val.1.val) % 2
  else 4 * r - 1 - (2 * w.val.1.val + (w.val.2.val + w.val.1.val) % 2)

theorem brickBoundaryRank_lt {c r : ℕ} (w : ElementaryWallVertex c r) :
    brickBoundaryRank w < 4 * r := by
  have hw := w.val.1.isLt
  dsimp only [brickBoundaryRank]
  split_ifs <;> omega

theorem brickBoundaryRank_injective_on_boundary {c r : ℕ} (hc : 2 ≤ c)
    {v w : ElementaryWallVertex c r} (hv : OnBrickColumnBoundary v) (hw : OnBrickColumnBoundary w)
    (he : brickBoundaryRank v = brickBoundaryRank w) : v = w := by
  have hvr := v.val.1.isLt
  have hwr := w.val.1.isLt
  have hvc := v.val.2.isLt
  have hwc := w.val.2.isLt
  dsimp only [OnBrickColumnBoundary] at hv hw
  have hcoords : v.val.1.val = w.val.1.val ∧ v.val.2.val = w.val.2.val := by
    dsimp only [brickBoundaryRank] at he
    split_ifs at he <;> omega
  exact Subtype.ext (Prod.ext (Fin.ext hcoords.1) (Fin.ext hcoords.2))

theorem brickBoundaryRank_side {c r : ℕ} (w : ElementaryWallVertex c r) :
    brickBoundaryRank w < 2 * r ↔ w.val.2.val ≤ 1 := by
  have hw := w.val.1.isLt
  dsimp only [brickBoundaryRank]
  split_ifs <;> omega

def brickBoundaryColumnCode {c r : ℕ} (w : ElementaryWallVertex c r) : Fin 4 :=
  ⟨if w.val.2.val ≤ 1 then w.val.2.val else w.val.2.val - 2 * (c - 1) + 2, by
    have hw := w.val.2.isLt
    split_ifs <;> omega⟩

theorem brickBoundaryColumnCode_injective_at_row {c r : ℕ}
    {v w : ElementaryWallVertex c r} (hv : OnBrickColumnBoundary v) (hw : OnBrickColumnBoundary w)
    (hrow : v.val.1 = w.val.1) (he : brickBoundaryColumnCode v = brickBoundaryColumnCode w) : v = w := by
  have hh := congrArg Fin.val he
  have hvc := v.val.2.isLt
  have hwc := w.val.2.isLt
  dsimp only [brickBoundaryColumnCode] at hh
  dsimp only [OnBrickColumnBoundary] at hv hw
  have hcol : v.val.2.val = w.val.2.val := by split_ifs at hh <;> omega
  exact Subtype.ext (Prod.ext hrow (Fin.ext hcol))

end
end Erdos73
