/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RoughDivisorBound
import ErdosProblems.Erdos387.SubpowerComparable

/-!
# Reciprocal energy on the subpower scale

This specializes the elementary squarefull-energy estimate to the exact
powers of two used in the Erdős 387 development.  For values at most the
medium threshold, `L = 2 * ell * N^2` bounds the total prime multiplicity of
a product of `2*ell` rough coordinates.
-/

namespace Erdos387

open Filter

namespace SubpowerScale

def reciprocalEnergyDepth (N ell : ℕ) : ℕ := 2 * ell * N ^ 2

theorem comparableUpperLog_le_roughPower_mul_square
    (N k : ℕ) :
    comparableUpperLog N k ≤ roughPower N k * N ^ 2 := by
  unfold comparableUpperLog scalePower roughPower
  rw [show N ^ (2 * k + 5) = N ^ (2 * k + 3) * N ^ 2 by
    simpa using pow_add N (2 * k + 3) 2]
  unfold BPZScale.mediumExp BPZScale.xExp
  nlinarith [Nat.zero_le (3 ^ k * k ^ 100 * N ^ (2 * k + 3) * N ^ 2)]

theorem medium_pow_lt_z_pow_reciprocalEnergyDepth
    {N k ell : ℕ} (hN : 0 < N) (hk : 0 < k) :
    medium N k ^ (2 * ell) <
      z N k ^ (reciprocalEnergyDepth N ell + 1) := by
  rw [medium_eq_pow_two]
  unfold z
  rw [← pow_mul, ← pow_mul]
  apply (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr
  have hupper := comparableUpperLog_le_roughPower_mul_square N k
  have hrough := roughPower_pos hN hk
  unfold reciprocalEnergyDepth
  calc
    comparableUpperLog N k * (2 * ell) ≤
        (roughPower N k * N ^ 2) * (2 * ell) := by gcongr
    _ = roughPower N k * (2 * ell * N ^ 2) := by ring
    _ < roughPower N k * (2 * ell * N ^ 2 + 1) := by
      nlinarith

/-- Uniform reciprocal-energy estimate for any finite set of rough values
below the medium threshold. -/
theorem reciprocalHalfEnergy_card_le_medium_envelope
    {N k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (ell : ℕ) (U : Finset ℕ)
    (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ medium N k)
    (hUrough : ∀ u ∈ U, IsZRough (z N k) u) :
    (reciprocalEnergyTuples (reciprocalLeftHalf ell) U).card ≤
      medium N k ^ ell * 2 ^ reciprocalEnergyDepth N ell *
        (2 ^ reciprocalEnergyDepth N ell) ^ (2 * ell) := by
  apply reciprocalHalfEnergy_card_le_envelope ell U
  · exact two_le_z hN hk |>.trans_lt' (by omega)
  · exact hUpos
  · exact hUle
  · exact hUrough
  · exact medium_pow_lt_z_pow_reciprocalEnergyDepth hN hk

/-- Explicit finite threshold for absorbing the complete diagonal
squarefull-energy overhead into one copy of `base`. -/
theorem reciprocalEnergyOverhead_le_base
    {N k ell : ℕ}
    (hN : max 1 (2 * ell * (2 * ell + 1)) ≤ N) :
    2 ^ reciprocalEnergyDepth N ell *
        (2 ^ reciprocalEnergyDepth N ell) ^ (2 * ell) ≤
      base N k := by
  let C := 2 * ell * (2 * ell + 1)
  have hNone : 1 ≤ N := (le_max_left 1 C).trans hN
  have hCN : C ≤ N := (le_max_right 1 C).trans hN
  have hExp : reciprocalEnergyDepth N ell * (2 * ell + 1) ≤
      scalePower N k := by
    unfold reciprocalEnergyDepth scalePower
    dsimp [C] at hCN
    calc
      2 * ell * N ^ 2 * (2 * ell + 1) =
          (2 * ell * (2 * ell + 1)) * N ^ 2 := by ring
      _ ≤ N * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) hCN
      _ = N ^ 3 := by ring
      _ ≤ N ^ (2 * k + 5) :=
        Nat.pow_le_pow_right hNone (by omega)
  have hoverhead :
      2 ^ reciprocalEnergyDepth N ell *
          (2 ^ reciprocalEnergyDepth N ell) ^ (2 * ell) =
        2 ^ (reciprocalEnergyDepth N ell * (2 * ell + 1)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  rw [hoverhead]
  unfold base
  exact Nat.pow_le_pow_right (by omega) hExp

/-- For fixed moment order, the entire divisor-fibre loss is eventually
smaller than one copy of the subpower base. -/
theorem eventually_reciprocalEnergyOverhead_le_base
    {k : ℕ} (_hk : 0 < k) (ell : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      2 ^ reciprocalEnergyDepth N ell *
          (2 ^ reciprocalEnergyDepth N ell) ^ (2 * ell) ≤
        base N k := by
  filter_upwards [eventually_ge_atTop
    (max 1 (2 * ell * (2 * ell + 1)))] with N hN
  exact reciprocalEnergyOverhead_le_base hN

/-- Eventual `medium^ell * base` form of the energy estimate. -/
theorem eventually_reciprocalHalfEnergy_card_le_medium_mul_base
    {k : ℕ} (hk : 0 < k) (ell : ℕ) (U : ℕ → Finset ℕ)
    (hUpos : ∀ᶠ N : ℕ in atTop, ∀ u ∈ U N, 0 < u)
    (hUle : ∀ᶠ N : ℕ in atTop, ∀ u ∈ U N, u ≤ medium N k)
    (hUrough : ∀ᶠ N : ℕ in atTop,
      ∀ u ∈ U N, IsZRough (z N k) u) :
    ∀ᶠ N : ℕ in atTop,
      (reciprocalEnergyTuples (reciprocalLeftHalf ell) (U N)).card ≤
        medium N k ^ ell * base N k := by
  filter_upwards [eventually_ge_atTop 1,
      eventually_reciprocalEnergyOverhead_le_base hk ell,
      hUpos, hUle, hUrough] with N hN hover hpos hle hrough
  have hmul := Nat.mul_le_mul_left (medium N k ^ ell) hover
  exact (reciprocalHalfEnergy_card_le_medium_envelope
    (by omega) hk ell (U N) hpos hle hrough).trans (by
      simpa [mul_assoc] using hmul)

end SubpowerScale

end Erdos387
