/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.Elementary

/-!
# Discrete dyadic scales for Erdős problem 851

Using powers of two throughout makes the level-of-distribution and roughness
inequalities literal inequalities between natural-number powers.  The beta
sieve will use `distributionLevel J = 2^(J/4)` and will remove primes below
`roughCutoff S J = 2^(J/(8*S))` (apart from a fixed initial segment).
-/

namespace Erdos851

/-- The left endpoint of the `J`th dyadic shell. -/
def dyadicScale (J : ℕ) : ℕ := 2 ^ J

/-- The divisor level used for the interval congruence estimates. -/
def distributionLevel (J : ℕ) : ℕ := 2 ^ (J / 4)

/-- The moving upper endpoint of the medium-prime interval. -/
def roughCutoff (S J : ℕ) : ℕ := 2 ^ (J / (8 * S))

/-- The exponents used at scale `J`.  Their cardinality is exactly `J`. -/
def powIndices (J : ℕ) : Finset ℕ := Finset.range J

/-- The largest dyadic exponent whose power of two does not exceed `X`. -/
def logIndex (X : ℕ) : ℕ := Nat.log 2 X

@[simp] theorem card_powIndices (J : ℕ) : (powIndices J).card = J := by
  simp [powIndices]

@[simp] theorem dyadicInterval_scale_card (J : ℕ) :
    (dyadicInterval (dyadicScale J)).card = dyadicScale J := by
  simp [dyadicInterval, dyadicScale]
  omega

theorem pow_lt_dyadicScale_of_mem_powIndices {J k : ℕ}
    (hk : k ∈ powIndices J) :
    2 ^ k < dyadicScale J := by
  rw [powIndices, Finset.mem_range] at hk
  simpa [dyadicScale] using Nat.pow_lt_pow_right (by norm_num : 1 < 2) hk

theorem pow_lt_of_mem_dyadicInterval_of_mem_powIndices {J k a : ℕ}
    (ha : a ∈ dyadicInterval (dyadicScale J))
    (hk : k ∈ powIndices J) :
    2 ^ k < a := by
  have hka := pow_lt_dyadicScale_of_mem_powIndices hk
  have hXa : dyadicScale J < a := (Finset.mem_Ioc.mp ha).1
  exact hka.trans hXa

/-- The dyadic scale selected by `logIndex` lies below `X`. -/
theorem pow_logIndex_le {X : ℕ} (hX : 0 < X) :
    2 ^ logIndex X ≤ X := by
  exact Nat.pow_log_le_self 2 hX.ne'

/-- The next dyadic scale after `logIndex X` lies strictly above `X`. -/
theorem lt_pow_logIndex_succ {X : ℕ} (_hX : 0 < X) :
    X < 2 ^ (logIndex X + 1) := by
  simpa [logIndex, Nat.succ_eq_add_one] using
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X

/-- Every exponent selected at the logarithmic scale gives a power of two
bounded by the ambient interval scale. -/
theorem pow_le_of_mem_powIndices_logIndex {X k : ℕ} (hX : 0 < X)
    (hk : k ∈ powIndices (logIndex X)) :
    2 ^ k ≤ X := by
  exact (pow_lt_dyadicScale_of_mem_powIndices hk).le.trans
    (pow_logIndex_le hX)

/-- The beta-sieve cutoff raised to the stopping depth lies below the
divisor level. -/
theorem roughCutoff_pow_le_distributionLevel {S J : ℕ} (_hS : 0 < S) :
    roughCutoff S J ^ S ≤ distributionLevel J := by
  rw [roughCutoff, distributionLevel, ← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
  calc
    (J / (8 * S)) * S ≤ J / 8 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).2
      calc
        (J / (8 * S)) * S * 8 = (J / (8 * S)) * (8 * S) := by ring
        _ ≤ J := Nat.div_mul_le_self J (8 * S)
    _ ≤ J / 4 := Nat.div_le_div_left (by norm_num : 4 ≤ 8) (by norm_num)

/-- The square of the divisor level is still at most the square-root scale
`2^(J/2)`, which is negligible compared with `2^J`. -/
theorem distributionLevel_sq_le (J : ℕ) :
    distributionLevel J ^ 2 ≤ 2 ^ (J / 2) := by
  rw [distributionLevel, ← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num : 0 < 2)
  omega

/-- Once `J ≥ 16*S`, the moving cutoff is nontrivial. -/
theorem one_lt_roughCutoff {S J : ℕ} (hS : 0 < S)
    (hJ : 16 * S ≤ J) :
    1 < roughCutoff S J := by
  rw [roughCutoff]
  have hden : 0 < 8 * S := Nat.mul_pos (by norm_num) hS
  have hq : 2 ≤ J / (8 * S) := by
    apply (Nat.le_div_iff_mul_le hden).2
    omega
  exact one_lt_pow₀ (by norm_num) (by omega)

/-- The roughness cutoff is large enough that a number from the dyadic shell
cannot have more than `16*S` distinct prime factors above it. -/
theorem dyadic_residual_lt_roughCutoff_pow {S J a k : ℕ}
    (hS : 0 < S) (hJ : 16 * S ≤ J)
    (ha : a ∈ dyadicInterval (dyadicScale J)) :
    a - 2 ^ k < roughCutoff S J ^ (16 * S + 1) := by
  have haUpper : a ≤ 2 * dyadicScale J := (Finset.mem_Ioc.mp ha).2
  have hXa : dyadicScale J < a := (Finset.mem_Ioc.mp ha).1
  have hres : a - 2 ^ k < 2 ^ (J + 1) := by
    calc
      a - 2 ^ k < a := Nat.sub_lt (by
        exact Nat.zero_lt_of_lt hXa)
        (pow_pos (by norm_num) _)
      _ ≤ 2 * dyadicScale J := haUpper
      _ = 2 ^ (J + 1) := by simp [dyadicScale, pow_succ, Nat.mul_comm]
  rw [roughCutoff, ← pow_mul]
  refine hres.trans_le ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 ?_)
  have hden : 0 < 8 * S := Nat.mul_pos (by norm_num) hS
  let q := J / (8 * S)
  have hq : 2 ≤ q := by
    dsimp [q]
    apply (Nat.le_div_iff_mul_le hden).2
    omega
  have hJlt : J < 8 * S * (q + 1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ J hden
  calc
    J + 1 ≤ 8 * S * (q + 1) := hJlt
    _ ≤ q * (16 * S) := by
      nlinarith
    _ ≤ q * (16 * S + 1) := Nat.mul_le_mul_left q (Nat.le_succ _)

/-- Twice an arbitrary interval scale is below the roughness power selected
at its logarithmic scale.  The `32*S` budget absorbs the single dyadic gap. -/
theorem two_mul_lt_roughCutoff_logIndex_pow
    {S X : ℕ} (hS : 0 < S) (hX : 0 < X)
    (hJ : 16 * S ≤ logIndex X) :
    2 * X < roughCutoff S (logIndex X) ^ (32 * S + 1) := by
  have hscale : 2 * X < 2 ^ (logIndex X + 2) := by
    calc
      2 * X < 2 * 2 ^ (logIndex X + 1) := by
        have := lt_pow_logIndex_succ hX
        omega
      _ = 2 ^ (logIndex X + 2) := by
        rw [show logIndex X + 2 = (logIndex X + 1) + 1 by omega, pow_succ]
        ring
  rw [roughCutoff, ← pow_mul]
  refine hscale.trans_le ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 ?_)
  have hden : 0 < 8 * S := Nat.mul_pos (by norm_num) hS
  let q := logIndex X / (8 * S)
  have hq : 2 ≤ q := by
    dsimp [q]
    apply (Nat.le_div_iff_mul_le hden).2
    omega
  have hJlt : logIndex X < 8 * S * (q + 1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ (logIndex X) hden
  calc
    logIndex X + 2 ≤ 8 * S * (q + 1) + 1 := by omega
    _ ≤ q * (32 * S + 1) := by nlinarith

/-- The residual-size estimate on an arbitrary shell `(X,2X]`, using the
logarithmic exponent scale.  Doubling the factor budget from `16*S` to
`32*S` absorbs the gap between `X` and its preceding power of two. -/
theorem dyadic_residual_lt_roughCutoff_logIndex_pow
    {S X a k : ℕ} (hS : 0 < S) (hX : 0 < X)
    (hJ : 16 * S ≤ logIndex X)
    (ha : a ∈ dyadicInterval X) :
    a - 2 ^ k < roughCutoff S (logIndex X) ^ (32 * S + 1) := by
  have haUpper : a ≤ 2 * X := (Finset.mem_Ioc.mp ha).2
  have hXa : X < a := (Finset.mem_Ioc.mp ha).1
  have hres : a - 2 ^ k < 2 ^ (logIndex X + 2) := by
    calc
      a - 2 ^ k < a := Nat.sub_lt (Nat.zero_lt_of_lt hXa)
        (pow_pos (by norm_num) _)
      _ ≤ 2 * X := haUpper
      _ < 2 * 2 ^ (logIndex X + 1) := by
        have := lt_pow_logIndex_succ hX
        omega
      _ = 2 ^ (logIndex X + 2) := by
        rw [show logIndex X + 2 = (logIndex X + 1) + 1 by omega, pow_succ]
        ring
  rw [roughCutoff, ← pow_mul]
  refine hres.trans_le ((Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).2 ?_)
  have hden : 0 < 8 * S := Nat.mul_pos (by norm_num) hS
  let q := logIndex X / (8 * S)
  have hq : 2 ≤ q := by
    dsimp [q]
    apply (Nat.le_div_iff_mul_le hden).2
    omega
  have hJlt : logIndex X < 8 * S * (q + 1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ (logIndex X) hden
  calc
    logIndex X + 2 ≤ 8 * S * (q + 1) + 1 := by omega
    _ ≤ q * (32 * S + 1) := by nlinarith

end Erdos851
