/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RefinedLogarithmicSieve

/-!
# A subpower roughness scale

The paper takes `z` to be a small fixed power of `X` because `k` grows.
For the logically sufficient fixed-`B` specialization we instead let
`log X / log z = N^2`.  This preserves all fixed fractional-power divisor
thresholds while making a Brun support of depth `O(log log z)` subpower.
-/

namespace Erdos387

namespace SubpowerScale

def scalePower (N k : ℕ) : ℕ := N ^ (2 * k + 5)
def roughPower (N k : ℕ) : ℕ := BPZScale.xExp k * N ^ (2 * k + 3)
def base (N k : ℕ) : ℕ := 2 ^ scalePower N k

def X (N k : ℕ) : ℕ := BPZScale.X (base N k) k
def z (N k : ℕ) : ℕ := 2 ^ roughPower N k
def y (N k : ℕ) : ℕ := BPZScale.y (base N k) k
def medium (N k : ℕ) : ℕ := BPZScale.medium (base N k) k
def large (N k : ℕ) : ℕ := BPZScale.large (base N k) k
def secondMin (N k : ℕ) : ℕ := BPZScale.secondMin (base N k) k
def gap (N k : ℕ) : ℕ := BPZScale.gap (base N k) k

theorem X_eq_pow_two (N k : ℕ) :
    X N k = 2 ^ (BPZScale.xExp k * N ^ (2 * k + 5)) := by
  simp [X, BPZScale.X, base, scalePower, pow_mul, mul_comm]

theorem log_two_z (N k : ℕ) :
    Nat.log 2 (z N k) = roughPower N k := by
  unfold z
  exact Nat.log_pow (by norm_num) _

/-- A simple power-of-two upper envelope for the logarithm of the roughness
exponent. -/
theorem log_two_roughPower_le
    {N k : ℕ} :
    Nat.log 2 (roughPower N k) ≤
      (Nat.log 2 (BPZScale.xExp k) + 1) +
        (Nat.log 2 N + 1) * (2 * k + 3) := by
  let c := Nat.log 2 (BPZScale.xExp k) + 1
  let r := Nat.log 2 N + 1
  let s := 2 * k + 3
  have hxPow : BPZScale.xExp k ≤ 2 ^ c := by
    exact (Nat.lt_pow_succ_log_self (by norm_num)
      (BPZScale.xExp k)).le
  have hNPow : N ≤ 2 ^ r := by
    exact (Nat.lt_pow_succ_log_self (by norm_num) N).le
  have hpow : N ^ s ≤ (2 ^ r) ^ s := Nat.pow_le_pow_left hNPow s
  have hrough : roughPower N k ≤ 2 ^ (c + r * s) := by
    calc
      roughPower N k = BPZScale.xExp k * N ^ s := by rfl
      _ ≤ 2 ^ c * (2 ^ r) ^ s := Nat.mul_le_mul hxPow hpow
      _ = 2 ^ (c + r * s) := by rw [← pow_mul, ← pow_add]
  calc
    Nat.log 2 (roughPower N k) ≤ Nat.log 2 (2 ^ (c + r * s)) :=
      Nat.log_mono_right hrough
    _ = c + r * s := Nat.log_pow (by norm_num) _
    _ = (Nat.log 2 (BPZScale.xExp k) + 1) +
        (Nat.log 2 N + 1) * (2 * k + 3) := by rfl

/-- Fixed coefficient controlling the linear-in-`N` upper bound for the
logarithmic Brun depth. -/
def depthSlope (a b k : ℕ) : ℕ :=
  2 * (1 + b +
    a * (Nat.log 2 (BPZScale.xExp k) + 3) +
    a * (2 * k + 3)) + 1

theorem depthSlope_pos (a b k : ℕ) : 0 < depthSlope a b k := by
  simp [depthSlope]

/-- The chosen Brun depth is at most a fixed multiple of `N+1`. -/
theorem logarithmicBrunDepth_le_slope
    {a b N k : ℕ} (hN : 1 ≤ N) :
    PrimeReciprocal.logarithmicBrunDepth a b (z N k) ≤
      depthSlope a b k * (N + 1) := by
  let c := Nat.log 2 (BPZScale.xExp k) + 1
  let s := 2 * k + 3
  have hlogN : Nat.log 2 N + 1 ≤ N + 1 := by
    exact Nat.add_le_add_right (Nat.log_le_self 2 N) 1
  have hlogR : Nat.log 2 (Nat.log 2 (z N k)) ≤
      c + (N + 1) * s := by
    rw [log_two_z]
    exact (log_two_roughPower_le (N := N) (k := k)).trans (by
      dsimp [c, s]
      gcongr)
  have hcore :
      b + a * (Nat.log 2 (Nat.log 2 (z N k)) + 2) ≤
        (1 + b + a * (c + 2) + a * s) * (N + 1) := by
    calc
      b + a * (Nat.log 2 (Nat.log 2 (z N k)) + 2) ≤
          b + a * (c + (N + 1) * s + 2) := by gcongr
      _ = b + a * (c + 2) + a * s * (N + 1) := by ring
      _ ≤ (1 + b + a * (c + 2) + a * s) * (N + 1) := by
        have hOne : 1 ≤ N + 1 := by omega
        calc
          b + a * (c + 2) + a * s * (N + 1) ≤
              (b + a * (c + 2)) * (N + 1) +
                a * s * (N + 1) := by
            gcongr
            calc
              b + a * (c + 2) = (b + a * (c + 2)) * 1 := by simp
              _ ≤ (b + a * (c + 2)) * (N + 1) :=
                Nat.mul_le_mul_left _ hOne
          _ ≤ (1 + b + a * (c + 2)) * (N + 1) +
                a * s * (N + 1) := by
            gcongr
            omega
          _ = (1 + b + a * (c + 2) + a * s) * (N + 1) := by ring
  unfold PrimeReciprocal.logarithmicBrunDepth depthSlope
  dsimp [c, s] at hcore ⊢
  calc
    2 * (b + a * (Nat.log 2 (Nat.log 2 (z N k)) + 2)) + 1 ≤
        2 * ((1 + b + a * (Nat.log 2 (BPZScale.xExp k) + 1 + 2) +
          a * (2 * k + 3)) * (N + 1)) + 1 := by gcongr
    _ ≤ (2 * (1 + b + a * (Nat.log 2 (BPZScale.xExp k) + 3) +
          a * (2 * k + 3)) + 1) * (N + 1) := by
      have : 1 ≤ N + 1 := by omega
      nlinarith

/-- Once `N` dominates the fixed slope, the depth plus one is at most
`N²`. -/
theorem logarithmicBrunDepth_succ_le_square
    {a b N k : ℕ}
    (hN : 2 * (depthSlope a b k + 1) + 1 ≤ N) :
    PrimeReciprocal.logarithmicBrunDepth a b (z N k) + 1 ≤ N ^ 2 := by
  have hNOne : 1 ≤ N := by omega
  have hdepth := logarithmicBrunDepth_le_slope (a := a) (b := b)
    (k := k) hNOne
  have hSlope := depthSlope_pos a b k
  nlinarith [sq_nonneg (N - (depthSlope a b k + 1) : ℤ)]

/-- The entire Brun support is at most half the ambient scale. -/
theorem brunSupport_pow_le_half
    {a b N k : ℕ} (hk : 3 ≤ k)
    (hN : 2 * (depthSlope a b k + 1) + 1 ≤ N) :
    z N k ^ PrimeReciprocal.logarithmicBrunDepth a b (z N k) ≤
      X N k / 2 := by
  let L := PrimeReciprocal.logarithmicBrunDepth a b (z N k)
  let E := roughPower N k
  have hNOne : 1 ≤ N := by omega
  have hL := logarithmicBrunDepth_succ_le_square
    (a := a) (b := b) (k := k) hN
  have hEOne : 1 ≤ E := by
    dsimp [E, roughPower, BPZScale.xExp]
    have hkPos : 0 < k := by omega
    have hNPos : 0 < N := by omega
    have : 0 < 600 * 3 ^ k * k ^ 100 * N ^ (2 * k + 3) := by
      positivity
    omega
  have hExp : E * L + 1 ≤ BPZScale.xExp k * N ^ (2 * k + 5) := by
    calc
      E * L + 1 ≤ E * L + E := by gcongr
      _ = E * (L + 1) := by ring
      _ ≤ E * N ^ 2 := Nat.mul_le_mul_left E hL
      _ = BPZScale.xExp k * N ^ (2 * k + 5) := by
        dsimp [E, roughPower]
        rw [show N ^ (2 * k + 5) = N ^ (2 * k + 3) * N ^ 2 by
          simpa using pow_add N (2 * k + 3) 2]
        ring
  change (2 ^ E) ^ L ≤ X N k / 2
  rw [← pow_mul, X_eq_pow_two]
  simpa using BPZScale.coeff_mul_pow_le_half
    (t := 2) (B := 1) (e := E * L)
      (E := BPZScale.xExp k * N ^ (2 * k + 5))
      (by norm_num) (by norm_num) hExp

/-- The exact almost-prime scale comparisons are inherited unchanged from
the paper's integral threshold package. -/
theorem almostSecond_scale
    {B N k : ℕ} (hk : 3 ≤ k) (hB : 2 * B ≤ base N k) :
    B * y N k ^ (3 * k) * medium N k * secondMin N k ^ (k - 1) ≤
      X N k / 2 :=
  BPZScale.almostSecond_scale hk
    (Nat.succ_le_iff.mpr (pow_pos (by norm_num) _)) hB

theorem almostGap_scale
    {B N k : ℕ} (hk : 3 ≤ k) (hB : 2 * B ≤ base N k) :
    B * y N k ^ (3 * k) * (gap N k * secondMin N k) ^ k ≤
      X N k / 2 :=
  BPZScale.almostGap_scale hk
    (Nat.succ_le_iff.mpr (pow_pos (by norm_num) _)) hB

theorem large_switch_square_scale
    {N k : ℕ} (hk : 3 ≤ k) (hN : 1 ≤ N) :
    (X N k / (large N k + 1)) ^ 2 ≤ X N k / 2 :=
  BPZScale.large_switch_square_scale hk (by
    unfold base scalePower
    have hpowPos : 0 < N ^ (2 * k + 5) := pow_pos (by omega) _
    exact Nat.one_lt_pow hpowPos.ne' (by norm_num))

end SubpowerScale

end Erdos387
