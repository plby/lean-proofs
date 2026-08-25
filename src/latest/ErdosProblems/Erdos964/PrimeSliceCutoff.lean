import ErdosProblems.Erdos964.PrimeWeightedMultiples

/-!
# A uniform modulus cutoff for every prime slice

A single power bound on the squared sieve radius implies the required
cutoff after division by any positive smaller prime. Integer rounding is
accounted for by the factor two in the endpoint.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem div_le_modulusCutoff_div (U x p : ℕ) (hp : 0 < p) (hpx : p ≤ x)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hU : (U : ℝ) ≤ Real.rpow ((x : ℝ) / 2) θ) :
    U / p ≤ modulusCutoff θ (x / p) := by
  have hpp : (0 : ℝ) < p := by exact_mod_cast hp
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : 1 ≤ x / p := Nat.div_pos hpx hp
  have hround : x ≤ 2 * (p * (x / p)) := by
    have hrem := Nat.mod_lt x hp
    have hdecomp := Nat.mod_add_div x p
    have hmul := Nat.mul_le_mul_left p hq
    nlinarith
  have hroundR : (x : ℝ) / 2 ≤ p * (x / p : ℕ) := by
    have h : (x : ℝ) ≤ 2 * ((p : ℝ) * (x / p : ℕ)) := by exact_mod_cast hround
    linarith
  apply Nat.le_floor
  calc
    ((U / p : ℕ) : ℝ) ≤ (U : ℝ) / p := Nat.cast_div_le
    _ ≤ Real.rpow ((x : ℝ) / 2) θ / p := div_le_div_of_nonneg_right hU hpp.le
    _ ≤ Real.rpow ((p : ℝ) * (x / p : ℕ)) θ / p :=
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hroundR hθ) hpp.le
    _ = Real.rpow (p : ℝ) θ * Real.rpow (x / p : ℕ) θ / p := by
      simp only [Real.rpow_eq_pow, Real.mul_rpow (Nat.cast_nonneg p) (Nat.cast_nonneg (x / p))]
    _ ≤ (p : ℝ) * Real.rpow (x / p : ℕ) θ / p :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hpone hθ1)
          (Real.rpow_nonneg (Nat.cast_nonneg _) θ)) hpp.le
    _ = _ := by field_simp

end Erdos964
