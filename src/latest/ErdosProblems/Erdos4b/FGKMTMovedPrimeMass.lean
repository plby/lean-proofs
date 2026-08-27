/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRoughPowerTail
import ErdosProblems.Erdos4b.FGKMTCommonOffDiagonal
import Mathlib.Analysis.PSeries

/-!
# Elementary uniform bounds for the moved-prime masses

Comparison with all integers gives mass at most four and logarithmic
mass at most `16*k`. This modest polynomial loss is sufficient for the
stated error envelope and needs no additional prime-distribution result.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem sum_injective_labels_le_Ioc {p : α → ℕ} (hinj : Function.Injective p)
    {L N : ℕ} (hL : ∀ q, L < p q) (hN : ∀ q, p q ≤ N)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ q, f (p q)) ≤ ∑ n ∈ Finset.Ioc L N, f n := by
  classical
  rw [← Finset.sum_image (fun q _hq t _ht hqt => hinj hqt)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    obtain ⟨q, _hq, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Ioc.mpr ⟨hL q, hN q⟩
  · intro n _hn _hnot
    exact hf n

theorem sum_labels_inv_sq_le {p : α → ℕ} (hinj : Function.Injective p)
    {k : ℕ} (hk : 0 < k) (hrough : ∀ q, k ^ 2 < p q) :
    (∑ q, 1 / (p q : ℝ) ^ 2) ≤ 1 / (k : ℝ) ^ 2 := by
  let N := max (k ^ 2) (Finset.univ.sup p)
  have hN (q : α) : p q ≤ N := (Finset.le_sup (Finset.mem_univ q)).trans (le_max_right _ _)
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (k ^ 2) N, 1 / (n : ℝ) ^ 2 :=
      sum_injective_labels_le_Ioc hinj hrough hN _ (fun n => by positivity)
    _ ≤ ((k ^ 2 : ℕ) : ℝ)⁻¹ - (N : ℝ)⁻¹ := by
      simpa only [one_div] using sum_Ioc_inv_sq_le_sub (α := ℝ) (pow_ne_zero 2 hk.ne')
        (show k ^ 2 ≤ N from le_max_left _ _)
    _ ≤ _ := by
      simp only [Nat.cast_pow, one_div]
      exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg N))

theorem sum_labels_neg_three_halves_le {p : α → ℕ} (hinj : Function.Injective p)
    {k : ℕ} (hk : 0 < k) (hrough : ∀ q, k ^ 2 < p q) :
    (∑ q, (p q : ℝ) ^ (-3 / 2 : ℝ)) ≤ 2 / (k : ℝ) := by
  let N := Finset.univ.sup p
  exact (sum_injective_labels_le_Ioc hinj hrough (fun q => Finset.le_sup (Finset.mem_univ q))
    (fun n => (n : ℝ) ^ (-3 / 2 : ℝ)) (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
    (sum_Ioc_neg_three_halves_le hk N)

theorem movedPrimeWeight_le {k p : ℝ} (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    k ^ 2 / (p - k) ^ 2 ≤ 4 * k ^ 2 / p ^ 2 := by
  have hp0 : 0 < p := by nlinarith [sq_nonneg k]
  have hhalf : p / 2 ≤ p - k := by nlinarith
  calc
    _ ≤ k ^ 2 / (p / 2) ^ 2 := div_le_div_of_nonneg_left (sq_nonneg k)
      (by positivity) (pow_le_pow_left₀ (by positivity) hhalf 2)
    _ = _ := by ring

theorem movedPrimeWeight_log_le {k p : ℝ} (hk : 2 ≤ k) (hp : 2 * k ^ 2 < p) :
    k ^ 2 / (p - k) ^ 2 * Real.log p ≤ 8 * k ^ 2 * p ^ (-3 / 2 : ℝ) := by
  have hp1 : 1 ≤ p := by nlinarith
  have hp0 : 0 < p := zero_lt_one.trans_le hp1
  have hlog : Real.log p ≤ 2 * p ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ p ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
        Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 2)
      _ = _ := by ring
  have hpower : p ^ (1 / 2 : ℝ) / p ^ 2 = p ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast p 2, ← Real.rpow_sub hp0]
    norm_num
  calc
    _ ≤ (4 * k ^ 2 / p ^ 2) * (2 * p ^ (1 / 2 : ℝ)) :=
      mul_le_mul (movedPrimeWeight_le hk hp) hlog (Real.log_nonneg hp1) (by positivity)
    _ = 8 * k ^ 2 * (p ^ (1 / 2 : ℝ) / p ^ 2) := by ring
    _ = _ := by rw [hpower]

theorem movedPrimeMass_le_four {k : ℕ} (hk : 2 ≤ k) {p : α → ℕ}
    (hinj : Function.Injective p) (hrough : ∀ q, 2 * k ^ 2 < p q) :
    (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2) ≤ 4 := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  calc
    _ ≤ ∑ q, 4 * (k : ℝ) ^ 2 / (p q : ℝ) ^ 2 := Finset.sum_le_sum fun q _hq =>
      movedPrimeWeight_le (by exact_mod_cast hk) (by exact_mod_cast hrough q)
    _ = 4 * (k : ℝ) ^ 2 * ∑ q, 1 / (p q : ℝ) ^ 2 := by
      simp only [Finset.mul_sum, div_eq_mul_inv, one_mul]
    _ ≤ 4 * (k : ℝ) ^ 2 * (1 / (k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_labels_inv_sq_le hinj hk0 (fun q => by
        have h := hrough q; omega)) (by positivity)
    _ = 4 := by field_simp

theorem movedPrimeLogMass_le {k : ℕ} (hk : 2 ≤ k) {p : α → ℕ}
    (hinj : Function.Injective p) (hrough : ∀ q, 2 * k ^ 2 < p q) :
    (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2 * Real.log (p q)) ≤ 16 * k := by
  have hk0 : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  calc
    _ ≤ ∑ q, 8 * (k : ℝ) ^ 2 * (p q : ℝ) ^ (-3 / 2 : ℝ) :=
      Finset.sum_le_sum fun q _hq =>
        movedPrimeWeight_log_le (by exact_mod_cast hk) (by exact_mod_cast hrough q)
    _ = 8 * (k : ℝ) ^ 2 * ∑ q, (p q : ℝ) ^ (-3 / 2 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 8 * (k : ℝ) ^ 2 * (2 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_labels_neg_three_halves_le hinj hk0 (fun q => by
        have h := hrough q; omega)) (by positivity)
    _ = _ := by field_simp; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.movedPrimeMass_le_four
#print axioms Erdos4b.FGKMT.movedPrimeLogMass_le
