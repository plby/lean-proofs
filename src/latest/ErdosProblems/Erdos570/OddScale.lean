/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Scale arithmetic for the strengthened odd-cycle induction

The modern proof only needs two coarse separations in its middle-density
branch.  This file derives them from one transparent lower bound on
`sqrt m`, while keeping every statement in natural-number arithmetic.
-/

namespace Erdos570

/-- The square root of `2m` is at most twice the square root of `m`.
This deliberately coarse bound avoids all real-valued rounding choices. -/
theorem sqrt_two_mul_le_two_sqrt (m : ℕ) :
    Nat.sqrt (2 * m) ≤ 2 * Nat.sqrt m := by
  have hm := Nat.lt_succ_sqrt m
  have hsq : 2 * m < (2 * Nat.sqrt m + 1) * (2 * Nat.sqrt m + 1) := by
    nlinarith
  have hlt : Nat.sqrt (2 * m) < 2 * Nat.sqrt m + 1 :=
    Nat.sqrt_lt.mpr hsq
  omega

/-- The explicit square-root threshold used for the middle-density branch. -/
def oddScaleRoot (D k : ℕ) : ℕ := D * (8 * k + 1)

/-- Above `oddScaleRoot`, the linear error terms occupy at most `m/D`.
The equation for `q` records all square-root rounding explicitly. -/
theorem odd_scale_error_mul_le
    {D k m q : ℕ} (hq : q = Nat.sqrt (2 * m))
    (hscale : oddScaleRoot D k ≤ Nat.sqrt m) :
    D * (4 * (k * q) + Nat.sqrt m) ≤ m := by
  have hqle : q ≤ 2 * Nat.sqrt m := by
    rw [hq]
    exact sqrt_two_mul_le_two_sqrt m
  have herr : 4 * (k * q) + Nat.sqrt m ≤
      (8 * k + 1) * Nat.sqrt m := by
    have hmul := Nat.mul_le_mul_left (4 * k) hqle
    nlinarith
  calc
    D * (4 * (k * q) + Nat.sqrt m) ≤
        D * ((8 * k + 1) * Nat.sqrt m) := Nat.mul_le_mul_left D herr
    _ = oddScaleRoot D k * Nat.sqrt m := by
      simp [oddScaleRoot, mul_assoc]
    _ ≤ Nat.sqrt m * Nat.sqrt m :=
      Nat.mul_le_mul_right (Nat.sqrt m) hscale
    _ ≤ m := Nat.sqrt_le m

/-- A density deficit of at least `1/D`, together with the scale estimate,
gives the exact additive gap required by the random-partition argument. -/
theorem odd_gap_of_density
    {D k m n q : ℕ} (hD : 0 < D)
    (hdensity : D * n ≤ (D - 1) * m)
    (herror : D * (4 * (k * q) + Nat.sqrt m) ≤ m) :
    4 * (k * q) + Nat.sqrt m ≤ m - n := by
  let x := 4 * (k * q) + Nat.sqrt m
  have hDpred : D - 1 + 1 = D := Nat.sub_add_cancel hD
  have hsum : D * (n + x) ≤ D * m := by
    dsimp only [x]
    calc
      D * (n + (4 * (k * q) + Nat.sqrt m)) =
          D * n + D * (4 * (k * q) + Nat.sqrt m) := by ring
      _ ≤ (D - 1) * m + m := Nat.add_le_add hdensity herror
      _ = (D - 1) * m + 1 * m := by simp
      _ = (D - 1 + 1) * m := (Nat.add_mul _ _ _).symm
      _ = D * m := by rw [hDpred]
  have hnx : n + x ≤ m := Nat.le_of_mul_le_mul_left hsum hD
  exact Nat.le_sub_of_add_le (by simpa [x, add_comm] using hnx)

/-- The single threshold hypothesis supplies the precise gap used by
`oddMiddleRoom_of_gap`. -/
theorem odd_gap_of_scale_and_density
    {D k m n q : ℕ} (hD : 0 < D)
    (hq : q = Nat.sqrt (2 * m))
    (hscale : oddScaleRoot D k ≤ Nat.sqrt m)
    (hdensity : D * n ≤ (D - 1) * m) :
    4 * (k * q) + Nat.sqrt m ≤ m - n :=
  odd_gap_of_density hD hdensity (odd_scale_error_mul_le hq hscale)

end Erdos570
