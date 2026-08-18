/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterRed

/-!
# Elementary bounds for Hunter's random radial labels

The exact finite counting lemma asks for
`N^2 * K^Y < (K+1)^Y`.  The paper proves this by an exponential estimate.
Here we give a division-free natural-number version: each block of `K`
label coordinates contributes a factor of at least two, by Bernoulli's
inequality.
-/

namespace Erdos984

/-- A block of `K` factors gains a factor two when `K` is replaced by
`K+1`. -/
lemma two_mul_pow_self_le_succ_pow_self {K : ℕ} (hK : 0 < K) :
    2 * K ^ K ≤ (K + 1) ^ K := by
  have hbern := pow_add_mul_le_add_pow (R := ℕ) (a := K) (b := 1)
    (Nat.zero_le K) (by omega) K
  have hterm : K * K ^ (K - 1) = K ^ K := by
    rw [← pow_succ']
    congr 1
    omega
  calc
    2 * K ^ K = K ^ K + K * K ^ (K - 1) := by rw [hterm, two_mul]
    _ ≤ (K + 1) ^ K := by simpa [add_comm] using hbern

/-- Repeating the preceding block `L` times and then padding to `Y`
coordinates. -/
lemma two_pow_mul_pow_le_succ_pow
    {K L Y : ℕ} (hK : 0 < K) (hKL : K * L ≤ Y) :
    2 ^ L * K ^ Y ≤ (K + 1) ^ Y := by
  have hblock := Nat.pow_le_pow_left (two_mul_pow_self_le_succ_pow_self hK) L
  have hcore : 2 ^ L * K ^ (K * L) ≤ (K + 1) ^ (K * L) := by
    simpa only [mul_pow, pow_mul] using hblock
  let R := Y - K * L
  have hYR : K * L + R = Y := by
    dsimp [R]
    omega
  have hpad : K ^ R ≤ (K + 1) ^ R := by
    exact Nat.pow_le_pow_left (by omega) R
  calc
    2 ^ L * K ^ Y =
        (2 ^ L * K ^ (K * L)) * K ^ R := by
      rw [← hYR, pow_add]
      ac_rfl
    _ ≤ (K + 1) ^ (K * L) * (K + 1) ^ R :=
      Nat.mul_le_mul hcore hpad
    _ = (K + 1) ^ Y := by rw [← pow_add, hYR]

/-- A convenient exact replacement for the paper's exponential union
bound. -/
lemma radial_label_base_count_of_two_pow
    {N K L Y : ℕ} (hK : 0 < K) (hKL : K * L ≤ Y)
    (hN : N ^ 2 < 2 ^ L) :
    N ^ 2 * K ^ Y < (K + 1) ^ Y := by
  calc
    N ^ 2 * K ^ Y < 2 ^ L * K ^ Y :=
      Nat.mul_lt_mul_of_pos_right hN (pow_pos hK Y)
    _ ≤ (K + 1) ^ Y := two_pow_mul_pow_le_succ_pow hK hKL

end Erdos984
