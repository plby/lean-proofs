import ErdosProblems.Erdos556.Basic

/-!
# Explicit parameters for the hereditary density theorem

The fixed ratio `N ≤ 16 * k` is sufficient for the cycle Ramsey application.
Integer divisions supply linear deletion and degree parameters; all rounding
losses are absorbed by the displayed order bounds.
-/

namespace Erdos556

private theorem quadratic_budget_from_scale (ε B t N x : ℝ)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) (hN : 0 ≤ N)
    (hB : 4096 ≤ ε * B) (htB : B * t ≤ 2 * N) (hx : N ≤ 32 * x) :
    2 * t * N ≤ ε * x ^ 2 := by
  have h1 := mul_le_mul_of_nonneg_right hB (by positivity : 0 ≤ 2 * t * N)
  have h2 := mul_le_mul_of_nonneg_right htB (by positivity : 0 ≤ 2 * ε * N)
  have hsq : N ^ 2 ≤ (32 * x) ^ 2 := by gcongr
  have h3 := mul_le_mul_of_nonneg_left hsq hε
  nlinarith

private theorem self_le_twice_div_mul (N B : ℕ) (hB : 0 < B) (hN : B ≤ N) :
    N ≤ 2 * B * (N / B) := by
  have hb : 1 ≤ N / B := Nat.div_pos hN hB
  have hmod := Nat.mod_lt N hB
  have hsum := Nat.mod_add_div N B
  have hmul := Nat.mul_le_mul_left B hb
  nlinarith

theorem density_parameters (ε : ℝ) (hε : 0 < ε) (B N₀ N k : ℕ)
    (hB : 128 ≤ B) (hεB : 4096 ≤ ε * B)
    (hN : 195 * B ≤ N) (hN₀ : 64 * (N₀ + 2) ≤ N) (hk : N ≤ 16 * k) :
    ∃ b d : ℕ,
      N ≤ 64 * d ∧ N ≤ (2 * B) * b ∧
      ((2 * (b + 195) : ℕ) : ℝ) ≤ (k : ℝ) + ε * N / 2 ∧
      ((2 * (b + 195) : ℕ) : ℝ) * N ≤
        ε * ((k : ℝ) + ε * N / 2 - (2 * (b + 195) : ℕ)) ^ 2 ∧
      ((d + 2 * (b + 195) : ℕ) : ℝ) ≤ (k : ℝ) + ε * N / 2 ∧
      ((N₀ + (b + 195) + 2 : ℕ) : ℝ) ≤ (k : ℝ) + ε * N / 2 ∧
      (k : ℝ) + ε / 8 * N + (b + 197 : ℕ) ≤ (k : ℝ) + ε * N / 2 := by
  let b := N / B
  let d := N / 32
  let t := b + 195
  let r : ℝ := (k : ℝ) + ε * N / 2
  have hBpos : 0 < B := by omega
  have hBN : B ≤ N := by nlinarith
  have hdb : N ≤ (2 * B) * b := self_le_twice_div_mul N B hBpos hBN
  have hdd : N ≤ 64 * d := by dsimp [d]; omega
  have hBb : b * B ≤ N := Nat.div_mul_le_self _ _
  have hBt : B * t ≤ 2 * N := by dsimp [t]; nlinarith
  have hBtR : (B : ℝ) * t ≤ 2 * N := by exact_mod_cast hBt
  have hB128 : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have h64t : (64 : ℝ) * t ≤ N := by
    have h := mul_le_mul_of_nonneg_right hB128 (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
    nlinarith
  have hdN : (32 : ℝ) * d ≤ N := by
    have h : d * 32 ≤ N := Nat.div_mul_le_self _ _
    exact_mod_cast (by nlinarith : 32 * d ≤ N)
  have hkR : (N : ℝ) ≤ 16 * k := by exact_mod_cast hk
  have hrk : (k : ℝ) ≤ r := by dsimp [r]; exact le_add_of_nonneg_right (by positivity)
  have hdegree : (d : ℝ) + 2 * t ≤ r := by nlinarith
  have htR : (2 : ℝ) * t ≤ r := by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); linarith
  have hx : (N : ℝ) ≤ 32 * (r - 2 * t) := by nlinarith
  have hbudget := quadratic_budget_from_scale ε B t N (r - 2 * t) hε.le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hεB hBtR hx
  have hN₀R : (64 : ℝ) * ((N₀ : ℝ) + 2) ≤ N := by exact_mod_cast hN₀
  have horder : (N₀ : ℝ) + t + 2 ≤ r := by nlinarith
  have hBNR : (B : ℝ) ≤ N := by exact_mod_cast hBN
  have hεN : (4096 : ℝ) ≤ ε * N :=
    hεB.trans (mul_le_mul_of_nonneg_left hBNR hε.le)
  have h8t : (8 : ℝ) * t ≤ ε * N := by
    have h1 := mul_le_mul_of_nonneg_right (show (16 : ℝ) ≤ ε * B by linarith)
      (Nat.cast_nonneg t : (0 : ℝ) ≤ t)
    have h2 := mul_le_mul_of_nonneg_left hBtR hε.le
    nlinarith
  have hmargin : (k : ℝ) + ε / 8 * N + ((t : ℝ) + 2) ≤ r := by
    dsimp [r]
    nlinarith
  refine ⟨b, d, hdd, hdb, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_mul, Nat.cast_ofNat, r, t] using htR
  · simpa only [Nat.cast_mul, Nat.cast_ofNat, r, t] using hbudget
  · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, r, t] using hdegree
  · simpa only [Nat.cast_add, Nat.cast_ofNat, r, t] using horder
  · have heq : b + 197 = t + 2 := by dsimp [t]
    simpa only [heq, Nat.cast_add, Nat.cast_ofNat, r] using hmargin

#print axioms density_parameters

end Erdos556
