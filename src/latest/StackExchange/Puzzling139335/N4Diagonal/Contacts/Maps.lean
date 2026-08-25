import StackExchange.Puzzling139335.N4Diagonal.Defs

/-!
# Coordinates of the two diagonal-reflection assignments

These are identities for the explicit placement functions. They do not
assert that any particular model has a chosen orientation parity.
-/

namespace Puzzling139335.N4Diagonal

open ThreeCorners

@[simp] theorem firstPlus_one_apply (p x : Plane) (θ : ℝ) :
    firstPlus 1 p θ x =
      !₂[1 + inner ℝ (ray θ) (x - p), inner ℝ (perpRay θ) (x - p)] := by
  ext i
  fin_cases i <;>
    simp [firstPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem firstPlus_three_apply (p x : Plane) (θ : ℝ) :
    firstPlus 3 p θ x =
      !₂[-inner ℝ (ray θ) (x - p), 1 - inner ℝ (perpRay θ) (x - p)] := by
  ext i
  fin_cases i <;>
    simp [firstPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem lastPlus_three_apply (q x : Plane) (β : ℝ) :
    lastPlus 3 q β x =
      !₂[-inner ℝ (perpRay β) (x - q), 1 + inner ℝ (ray β) (x - q)] := by
  ext i
  fin_cases i <;>
    simp [lastPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem lastMinus_three_apply (q x : Plane) (β : ℝ) :
    lastMinus 3 q β x =
      !₂[-inner ℝ (ray β) (x - q), 1 + inner ℝ (perpRay β) (x - q)] := by
  ext i
  fin_cases i <;>
    simp [lastMinus, lastPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem lastPlus_one_apply (q x : Plane) (β : ℝ) :
    lastPlus 1 q β x =
      !₂[1 + inner ℝ (perpRay β) (x - q), -inner ℝ (ray β) (x - q)] := by
  ext i
  fin_cases i <;>
    simp [lastPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

@[simp] theorem lastMinus_one_apply (q x : Plane) (β : ℝ) :
    lastMinus 1 q β x =
      !₂[1 + inner ℝ (ray β) (x - q), -inner ℝ (perpRay β) (x - q)] := by
  ext i
  fin_cases i <;>
    simp [lastMinus, lastPlus, SquareSymmetry.cornerFlipPoint, corner, Fin.ext_iff]

end Puzzling139335.N4Diagonal
