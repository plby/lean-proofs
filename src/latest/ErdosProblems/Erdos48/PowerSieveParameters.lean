/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.BadRootIncidence
import ErdosProblems.Erdos822.PrimeReciprocal

/-!
# Integer-power parameters for the shifted-smooth sieve

Writing the main endpoint as `n^(240*L)` lets the exponent `L` also make the
smoothness exponent arbitrarily close to one half.  The smoothness cutoff is
`n^(120*L-6)`, the target lower size of a root--auxiliary product is
`n^(120*L-7)`, and the auxiliary interval has relative length `n`.  Its
reciprocal-prime mass is therefore of order `1/L`, uniformly in the dyadic
root block.
-/

namespace Erdos48

open Filter
open scoped Topology BigOperators

noncomputable section

def powerSieveX (n L : ℕ) : ℕ := n ^ (240 * L)

def powerSieveProductBase (n L : ℕ) : ℕ := n ^ (120 * L - 7)

def powerSieveSmoothBound (n L : ℕ) : ℕ := n ^ (120 * L - 6)

def powerSieveAuxScale (n _L : ℕ) : ℕ := n

def powerSieveAuxCore (n L Q : ℕ) : ℕ :=
  max (powerSieveProductBase n L / Q) (powerSieveAuxScale n L)

def powerSieveAuxLower (n L Q : ℕ) : ℕ :=
  2 * powerSieveAuxCore n L Q

def powerSieveAuxUpper (n L Q : ℕ) : ℕ :=
  powerSieveAuxCore n L Q * powerSieveAuxScale n L

def powerSieveAuxPrimes (n L Q : ℕ) : Finset ℕ :=
  (Finset.Ioc (powerSieveAuxLower n L Q)
    (powerSieveAuxUpper n L Q)).filter Nat.Prime

@[simp] theorem mem_powerSieveAuxPrimes {n L Q r : ℕ} :
    r ∈ powerSieveAuxPrimes n L Q ↔
      powerSieveAuxLower n L Q < r ∧
        r ≤ powerSieveAuxUpper n L Q ∧ r.Prime := by
  simp only [powerSieveAuxPrimes, Finset.mem_filter, Finset.mem_Ioc]
  tauto

theorem powerSieveProductBase_mul_auxScale
    {n L : ℕ} (hL : 1 ≤ L) :
    powerSieveProductBase n L * powerSieveAuxScale n L =
      powerSieveSmoothBound n L := by
  simp only [powerSieveProductBase, powerSieveAuxScale,
    powerSieveSmoothBound, ← pow_succ]
  congr 1
  omega

theorem powerSieveAuxCore_le_productBase
    {n L Q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    powerSieveAuxCore n L Q ≤ powerSieveProductBase n L := by
  rw [powerSieveAuxCore, max_le_iff]
  constructor
  · exact Nat.div_le_self _ _
  · simp only [powerSieveAuxScale, powerSieveProductBase]
    exact Nat.le_pow (by omega : 0 < 120 * L - 7)

theorem powerSieveAuxUpper_le_productBase_mul_scale
    {n L Q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    powerSieveAuxUpper n L Q ≤
      powerSieveProductBase n L * powerSieveAuxScale n L := by
  rw [powerSieveAuxUpper]
  exact Nat.mul_le_mul_right _
    (powerSieveAuxCore_le_productBase hn hL hQ)

theorem powerSieveAuxUpper_le_smoothBound
    {n L Q : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L) (hQ : 1 ≤ Q) :
    powerSieveAuxUpper n L Q ≤ powerSieveSmoothBound n L := by
  rw [← powerSieveProductBase_mul_auxScale hL]
  exact powerSieveAuxUpper_le_productBase_mul_scale hn hL hQ

theorem powerSieveAuxCore_pos
    {n L Q : ℕ} (hn : 1 ≤ n) :
    0 < powerSieveAuxCore n L Q := by
  rw [powerSieveAuxCore]
  exact lt_of_lt_of_le
    (Nat.zero_lt_one.trans_le hn)
    (le_max_right _ _)

theorem powerSieveAuxLower_lt_upper
    {n L Q : ℕ} (hn : 3 ≤ n) (hL : 1 ≤ L) :
    powerSieveAuxLower n L Q < powerSieveAuxUpper n L Q := by
  have hcore := powerSieveAuxCore_pos (n := n) (L := L) (Q := Q)
    (show 1 ≤ n by omega)
  have hscale : 2 < powerSieveAuxScale n L := by
    simpa only [powerSieveAuxScale] using (show 2 < n by omega)
  rw [powerSieveAuxLower, powerSieveAuxUpper]
  nlinarith

theorem powerSieveAuxPrimes_reciprocal_eq_interval
    (n L Q : ℕ) :
    (∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹) =
      Erdos822.reciprocalPrimeIntervalSum
        (powerSieveAuxLower n L Q + 1)
        (powerSieveAuxUpper n L Q) := by
  unfold powerSieveAuxPrimes Erdos822.reciprocalPrimeIntervalSum
  apply Finset.sum_congr
  · ext r
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
      Nat.mem_primesLE, Nat.add_sub_cancel]
    constructor
    · rintro ⟨⟨hlower, hupper⟩, hprime⟩
      refine ⟨⟨hupper, hprime⟩, ?_⟩
      rintro ⟨hle, -⟩
      omega
    · rintro ⟨⟨hupper, hprime⟩, hnotLower⟩
      refine ⟨⟨?_, hupper⟩, hprime⟩
      by_contra hnot
      exact hnotLower ⟨Nat.le_of_not_gt hnot, hprime⟩
  · intro r hr
    simp only [div_eq_mul_inv, one_mul]

/-- The auxiliary prime interval has reciprocal mass at least a fixed
multiple of `1/L`, simultaneously for every block parameter `Q`. -/
theorem eventually_powerSieveAuxPrimes_reciprocal_lower (L : ℕ)
    (hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℕ, 1 ≤ Q →
      (1 / (500 * (L : ℝ)) : ℝ) ≤
        ∑ r ∈ powerSieveAuxPrimes n L Q, (r : ℝ)⁻¹ := by
  obtain ⟨C, hC⟩ := Erdos822.exists_reciprocalPrimeIntervalSum_lower
  have hlarge : ∀ᶠ n : ℕ in atTop,
      1000 * (|C| + Real.log 3 + 1) ≤ Real.log (n : ℝ) :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hlarge, eventually_ge_atTop 3] with n hnLarge hn Q hQ
  let A := powerSieveAuxScale n L
  let R := powerSieveAuxCore n L Q
  let w := powerSieveAuxLower n L Q + 1
  let z := powerSieveAuxUpper n L Q
  have hn1 : 1 ≤ n := by omega
  have hRpos : 0 < R := powerSieveAuxCore_pos hn1
  have hAthree : 3 ≤ A := by
    simpa only [A, powerSieveAuxScale] using hn
  have hw : 2 ≤ w := by dsimp [w, powerSieveAuxLower]; omega
  have hwz : w ≤ z := by
    dsimp [w, z, powerSieveAuxLower, powerSieveAuxUpper]
    nlinarith
  have hbase := hC hw hwz
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogA : Real.log (A : ℝ) = Real.log (n : ℝ) := by
    dsimp [A, powerSieveAuxScale]
  have hlogApos : 0 < Real.log (A : ℝ) := by rw [hlogA]; positivity
  have hwLe : w ≤ 3 * R := by
    dsimp [w, powerSieveAuxLower]
    omega
  have hzEq : z = R * A := rfl
  have hratio : (A : ℝ) / 3 ≤ (z : ℝ) / (w : ℝ) := by
    have hwpos : (0 : ℝ) < w := by positivity
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hwpos]
    rw [hzEq, Nat.cast_mul]
    have hwCast : (w : ℝ) ≤ 3 * R := by exact_mod_cast hwLe
    nlinarith [show (0 : ℝ) < A by positivity]
  have hratioPos : (0 : ℝ) < (A : ℝ) / 3 := by positivity
  have hlogRatio :
      Real.log (A : ℝ) - Real.log 3 ≤
        Real.log ((z : ℝ) / (w : ℝ)) := by
    rw [← Real.log_div (by positivity : (A : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    exact Real.log_le_log hratioPos hratio
  have hzBound : z ≤ n ^ (120 * L) := by
    dsimp [z]
    exact (powerSieveAuxUpper_le_smoothBound hn1 hL hQ).trans
      (by
        simp only [powerSieveSmoothBound]
        exact pow_le_pow_right' hn1 (by omega))
  have hzPos : (0 : ℝ) < z := by
    exact_mod_cast (show 0 < z by
      dsimp [z, powerSieveAuxUpper]
      exact Nat.mul_pos hRpos (Nat.zero_lt_of_lt hAthree))
  have hlogz : Real.log (z : ℝ) ≤
      ((120 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
    calc
      Real.log (z : ℝ) ≤ Real.log ((n : ℝ) ^ (120 * L)) := by
        apply Real.log_le_log hzPos
        exact_mod_cast hzBound
      _ = ((120 * L : ℕ) : ℝ) * Real.log (n : ℝ) := by
        rw [Real.log_pow]
  have hCabs : C ≤ |C| := le_abs_self C
  have hmain : (1 / (500 * (L : ℝ)) : ℝ) ≤
      (Real.log ((z : ℝ) / (w : ℝ)) - C) /
        Real.log (z : ℝ) := by
    have hlogzPos : 0 < Real.log (z : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < z by omega))
    rw [le_div_iff₀ hlogzPos]
    have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hnBound :
        1000 * (|C| + Real.log 3 + 1) ≤ Real.log (n : ℝ) := hnLarge
    have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
    calc
      1 / (500 * (L : ℝ)) * Real.log (z : ℝ) ≤
          1 / (500 * (L : ℝ)) *
            (((120 * L : ℕ) : ℝ) * Real.log (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hlogz (by positivity)
      _ = (120 / 500 : ℝ) * Real.log (n : ℝ) := by
        push_cast
        field_simp
        <;> ring
      _ ≤ Real.log ((z : ℝ) / (w : ℝ)) - C := by
        nlinarith [abs_nonneg C]
  rw [powerSieveAuxPrimes_reciprocal_eq_interval]
  exact hmain.trans hbase

end

end Erdos48
