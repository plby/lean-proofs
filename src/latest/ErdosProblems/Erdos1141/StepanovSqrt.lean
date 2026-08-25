import ErdosProblems.Erdos1141.StepanovCharacterSum
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A square-root bound with a degree-dependent constant
-/

namespace Pollack17.Stepanov

open Polynomial

def simpleRootConstant (d : ℕ) : ℕ :=
  32 * (d + 1) + 64 * (d + 1) * (d + 2) + d

theorem sqrt_div_square_small (p c : ℕ) (hc : 0 < c) :
    c * (Nat.sqrt p / c) ^ 2 ≤ p := by
  have hdiv : c * (Nat.sqrt p / c) ≤ Nat.sqrt p := by
    simpa only [mul_comm] using Nat.div_mul_le_self (Nat.sqrt p) c
  have hc2 : c ≤ c ^ 2 := by nlinarith
  calc
    c * (Nat.sqrt p / c) ^ 2 ≤ c ^ 2 * (Nat.sqrt p / c) ^ 2 :=
      Nat.mul_le_mul_right _ hc2
    _ = (c * (Nat.sqrt p / c)) ^ 2 := by ring
    _ ≤ (Nat.sqrt p) ^ 2 := Nat.pow_le_pow_left hdiv 2
    _ ≤ p := Nat.sqrt_le' p

theorem modulus_le_sqrt_mul_div {p c : ℕ} (hp : 0 < p) (hc : 0 < c)
    (hB : 1 ≤ Nat.sqrt p / c) :
    (p : ℝ) ≤ 4 * c * ((Nat.sqrt p / c : ℕ) : ℝ) * Real.sqrt p := by
  let B := Nat.sqrt p / c
  have hmod := Nat.mod_add_div (Nat.sqrt p) c
  have hmodlt := Nat.mod_lt (Nat.sqrt p) hc
  have hfloor : Nat.sqrt p + 1 ≤ c * (B + 1) := by dsimp [B]; nlinarith
  have hnext : Nat.sqrt p + 1 ≤ 2 * c * B := by
    calc
      Nat.sqrt p + 1 ≤ c * (B + 1) := hfloor
      _ ≤ c * (2 * B) := Nat.mul_le_mul_left c (by omega)
      _ = _ := by ring
  have hpn : p ≤ 2 * c * B * (Nat.sqrt p + 1) := by
    calc
      p ≤ (Nat.sqrt p + 1) ^ 2 := (Nat.lt_succ_sqrt' p).le
      _ ≤ (2 * c * B) * (Nat.sqrt p + 1) := by
        simpa only [pow_two] using Nat.mul_le_mul_right (Nat.sqrt p + 1) hnext
  have hpr : (p : ℝ) ≤ 2 * c * B * ((Nat.sqrt p : ℝ) + 1) := by exact_mod_cast hpn
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hl2 : (Nat.sqrt p : ℝ) ^ 2 ≤ p := by exact_mod_cast Nat.sqrt_le' p
  have hl : (Nat.sqrt p : ℝ) ≤ Real.sqrt p := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.sqrt p)]
  calc
    (p : ℝ) ≤ 2 * c * B * ((Nat.sqrt p : ℝ) + 1) := hpr
    _ ≤ 2 * c * B * (2 * Real.sqrt p) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- A quadratic Weil estimate sufficient for Burgess moments.  The degree
is arbitrary and the only polynomial hypothesis is a simple root. -/
theorem abs_polynomialCharacterSum_le_sqrt
    {p : ℕ} [Fact p.Prime] (f : (ZMod p)[X]) {x₀ : ZMod p}
    (hf : f ≠ 0) (hroot : f.rootMultiplicity x₀ = 1) :
    |polynomialCharacterSum f| ≤ (simpleRootConstant f.natDegree : ℝ) * Real.sqrt p := by
  let d := f.natDegree
  let c := 16 * (d + 1)
  let B := Nat.sqrt p / c
  have hc : 0 < c := by dsimp [c]; positivity
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg _)
  have hs1 : 1 ≤ Real.sqrt (p : ℝ) := by nlinarith
  have hC : (simpleRootConstant d : ℝ) =
      2 * c + 4 * c * (d + 2) + d := by
    simp only [simpleRootConstant, c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  by_cases hlarge : 2 * c ≤ Nat.sqrt p
  · have hB2 : 2 ≤ B := (Nat.le_div_iff_mul_le hc).mpr (by simpa only [mul_comm] using hlarge)
    have hB : 1 ≤ B := by omega
    have hp2 : p ≠ 2 := by
      have hsp := Nat.sqrt_le_self p
      have hc16 : 16 ≤ c := by dsimp [c]; omega
      omega
    have hsmall : 16 * (f.natDegree + 1) * B ^ 2 ≤ p := sqrt_div_square_small p c hc
    have hraw := abs_polynomialCharacterSum_le_of_small_square f hf hroot hp2 hB hsmall
    have hpb : (p : ℝ) ≤ 4 * c * B * Real.sqrt p := modulus_le_sqrt_mul_div hp hc hB
    have hDB : (B : ℝ) ≤ (2 * B - 1 : ℕ) := by exact_mod_cast (show B ≤ 2 * B - 1 by omega)
    have hD0 : (0 : ℝ) < (2 * B - 1 : ℕ) := by exact_mod_cast (show 0 < 2 * B - 1 by omega)
    have hpD : (p : ℝ) ≤ 4 * c * (2 * B - 1 : ℕ) * Real.sqrt p := by
      apply hpb.trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hDB (by positivity)) hs0
    have hquot : (p : ℝ) * (d + 2) / (2 * B - 1 : ℕ) ≤
        4 * c * (d + 2) * Real.sqrt p := by
      apply (div_le_iff₀ hD0).mpr
      have h := mul_le_mul_of_nonneg_right hpD (show (0 : ℝ) ≤ d + 2 by positivity)
      nlinarith
    have hd : (d : ℝ) ≤ d * Real.sqrt p := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 (Nat.cast_nonneg d)
    calc
      |polynomialCharacterSum f| ≤ (p : ℝ) * (d + 2) / (2 * B - 1 : ℕ) + d := hraw
      _ ≤ 4 * c * (d + 2) * Real.sqrt p + d * Real.sqrt p := add_le_add hquot hd
      _ ≤ (simpleRootConstant d : ℝ) * Real.sqrt p := by
        rw [hC]
        have : 0 ≤ 2 * (c : ℝ) * Real.sqrt p := by positivity
        nlinarith
  · have hnext : Nat.sqrt p + 1 ≤ 2 * c := by omega
    have hpbound : p ≤ (2 * c) ^ 2 :=
      (Nat.lt_succ_sqrt' p).le.trans (Nat.pow_le_pow_left hnext 2)
    have hpboundR : (p : ℝ) ≤ (2 * c) ^ 2 := by exact_mod_cast hpbound
    have hsr : Real.sqrt (p : ℝ) ≤ 2 * c := by
      nlinarith [Nat.cast_nonneg (α := ℝ) c]
    have hpc : (p : ℝ) ≤ 2 * c * Real.sqrt p := by nlinarith
    calc
      |polynomialCharacterSum f| ≤ p := abs_polynomialCharacterSum_le_card f
      _ ≤ 2 * c * Real.sqrt p := hpc
      _ ≤ (simpleRootConstant d : ℝ) * Real.sqrt p := by
        rw [hC]
        apply mul_le_mul_of_nonneg_right _ hs0
        have : 0 ≤ 4 * (c : ℝ) * (d + 2) + d := by positivity
        linarith

end Pollack17.Stepanov
