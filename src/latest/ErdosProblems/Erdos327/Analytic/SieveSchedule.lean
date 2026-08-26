import ErdosProblems.Erdos327.Analytic.FactorialTailBound

/-!
# Exact natural-power sieve schedule

For the dyadic scale `X = 2^j`, the finite sieve uses

* `h = ⌊log₂(j+1)⌋+1`,
* `R = 128 h²`,
* `k = ⌊j/(16R)⌋`,
* `z = 2^k`.

This file begins the exact arithmetic verification of that schedule.
-/

namespace Erdos327.Analytic

/-- Discrete logarithmic height of a dyadic index. -/
def sieveHeight (j : ℕ) : ℕ :=
  Nat.log 2 (j + 1) + 1

/-- Bonferroni radius. -/
def sieveRadius (j : ℕ) : ℕ :=
  128 * sieveHeight j ^ 2

/-- Exponent of the prime cutoff. -/
def sieveCutoffExponent (j : ℕ) : ℕ :=
  j / (16 * sieveRadius j)

/-- Prime cutoff, chosen as an exact power of two. -/
def sieveCutoff (j : ℕ) : ℕ :=
  2 ^ sieveCutoffExponent j

/-- Dyadic outer scale. -/
def dyadicScale (j : ℕ) : ℕ :=
  2 ^ j

theorem sieveHeight_pos (j : ℕ) :
    0 < sieveHeight j := by
  unfold sieveHeight
  omega

theorem sieveRadius_pos (j : ℕ) :
    0 < sieveRadius j := by
  have hh := sieveHeight_pos j
  simp only [sieveRadius]
  exact Nat.mul_pos (by norm_num) (Nat.pow_pos hh)

/-- Exact lower half of the floor-logarithm bracket. -/
theorem pow_sieveHeight_sub_one_le (j : ℕ) :
    2 ^ (sieveHeight j - 1) ≤ j + 1 := by
  have h :=
    Nat.pow_log_le_self 2 (show j + 1 ≠ 0 by omega)
  simpa [sieveHeight] using h

/-- Exact upper half of the floor-logarithm bracket. -/
theorem lt_pow_sieveHeight (j : ℕ) :
    j + 1 < 2 ^ sieveHeight j := by
  have h :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two (j + 1)
  simpa [sieveHeight] using h

theorem sieveHeight_le_add_one (j : ℕ) :
    sieveHeight j ≤ j + 1 := by
  have h :=
    Nat.log_lt_self 2 (show j + 1 ≠ 0 by omega)
  unfold sieveHeight
  omega

/-- Once `j ≥ 32R`, the cutoff exponent is at least two. -/
theorem two_le_sieveCutoffExponent
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    2 ≤ sieveCutoffExponent j := by
  unfold sieveCutoffExponent
  have hR := sieveRadius_pos j
  apply (Nat.le_div_iff_mul_le
    (Nat.mul_pos (by norm_num) hR)).2
  omega

/-- Euclidean division gives the lower exponent inequality used for the
boundary term. -/
theorem sixteen_mul_radius_mul_cutoffExponent_le (j : ℕ) :
    16 * sieveRadius j * sieveCutoffExponent j ≤ j := by
  unfold sieveCutoffExponent
  have h :=
    Nat.div_mul_le_self j (16 * sieveRadius j)
  nlinarith

/-- Under the schedule dominance hypothesis, Euclidean division also gives
the reverse comparison with a factor two. -/
theorem lt_thirtytwo_mul_radius_mul_cutoffExponent
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    j < 32 * sieveRadius j * sieveCutoffExponent j := by
  let d := 16 * sieveRadius j
  let k := sieveCutoffExponent j
  have hd : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos (by norm_num) (sieveRadius_pos j)
  have hk2 : 2 ≤ k :=
    two_le_sieveCutoffExponent hdom
  have hdecomp : j % d + d * (j / d) = j :=
    Nat.mod_add_div j d
  have hmod : j % d < d := Nat.mod_lt j hd
  have hjlt : j < d * (k + 1) := by
    have hk : j / d = k := by
      rfl
    rw [hk] at hdecomp
    calc
      j = j % d + d * k := hdecomp.symm
      _ < d + d * k := Nat.add_lt_add_right hmod (d * k)
      _ = d * (k + 1) := by ring
  have hsucc : k + 1 ≤ 2 * k := by omega
  calc
    j < d * (k + 1) := hjlt
    _ ≤ d * (2 * k) := Nat.mul_le_mul_left d hsucc
    _ = 32 * sieveRadius j * sieveCutoffExponent j := by
      dsimp [d, k]
      ring

/-- The eighth power of `z^(2R)` lies below the dyadic scale. -/
theorem sieveCutoff_boundary_pow_eight_le (j : ℕ) :
    (sieveCutoff j ^ (2 * sieveRadius j)) ^ 8 ≤
      dyadicScale j := by
  have hexp :=
    sixteen_mul_radius_mul_cutoffExponent_le j
  unfold sieveCutoff dyadicScale
  rw [← pow_mul, ← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  nlinarith

/-- The separate `3^(2R)` factor in the boundary has the same eighth-power
bound once `j ≥ 32R`. -/
theorem three_boundary_pow_eight_le
    {j : ℕ} (hdom : 32 * sieveRadius j ≤ j) :
    ((3 : ℕ) ^ (2 * sieveRadius j)) ^ 8 ≤
      dyadicScale j := by
  unfold dyadicScale
  rw [← pow_mul]
  calc
    3 ^ (2 * sieveRadius j * 8) ≤
        4 ^ (2 * sieveRadius j * 8) :=
      Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (32 * sieveRadius j) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    _ ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) hdom

end Erdos327.Analytic
