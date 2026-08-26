/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The central dyadic spatial bins retain asymptotically all logarithmic length.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SqrtScales

namespace Erdos521

open Filter
open scoped Topology

def mainBinSet (j : ℕ) : Finset ℕ := Finset.Ico (Nat.sqrt j) (j - Nat.sqrt j)

theorem mainBinSet_card_le (j : ℕ) : (mainBinSet j).card ≤ j := by
  simp only [mainBinSet, Nat.card_Ico]
  omega

theorem two_sqrt_le {j : ℕ} (hj : 4 ≤ j) : 2 * Nat.sqrt j ≤ j := by
  have hr : 2 ≤ Nat.sqrt j := Nat.le_sqrt.mpr hj
  nlinarith [Nat.sqrt_le' j]

theorem mainBinSet_card (j : ℕ) : (mainBinSet j).card = j - 2 * Nat.sqrt j := by
  simp only [mainBinSet, Nat.card_Ico, Nat.sub_sub]
  congr 1
  omega

theorem mainBinSet_card_ratio :
    Tendsto (fun j : ℕ ↦ ((mainBinSet j).card : ℝ) / j) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (nat_sqrt_div_tendsto_zero.const_mul 2)
  have h' : Tendsto (fun j : ℕ ↦ 1 - 2 * ((Nat.sqrt j : ℝ) / j)) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 4] with j hj
  have hj₀ : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  rw [mainBinSet_card, Nat.cast_sub (two_sqrt_le hj), Nat.cast_mul, Nat.cast_ofNat]
  field_simp

theorem mainBinSet_mem {j k : ℕ} (hk : k ∈ mainBinSet j) :
    Nat.sqrt j ≤ k ∧ k + 1 + Nat.sqrt j ≤ j := by
  have h := Finset.mem_Ico.mp hk
  omega

theorem eventually_linear_le_two_pow_sqrt (C : ℝ) :
    ∀ᶠ j : ℕ in atTop, C * (j : ℝ) ≤ (2 : ℝ) ^ Nat.sqrt j := by
  filter_upwards [eventually_two_pow_neg_sqrt_le (-2),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop C, eventually_ge_atTop 1]
    with j hpow hC hj
  have hj₀ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hsq : (j : ℝ) ^ 2 ≤ (2 : ℝ) ^ Nat.sqrt j := by
    have h : ((2 : ℝ) ^ Nat.sqrt j)⁻¹ ≤ ((j : ℝ) ^ 2)⁻¹ := by
      simpa only [Real.rpow_neg hj₀.le, Real.rpow_two] using hpow
    exact (inv_le_inv₀ (by positivity) (sq_pos_of_pos hj₀)).mp h
  exact (by nlinarith : C * (j : ℝ) ≤ (j : ℝ) ^ 2).trans hsq

end Erdos521
