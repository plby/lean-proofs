/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Optimizing the prime cutoff in the combined global and congruence estimate.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.GlobalCongruence

namespace Erdos477.Counting

theorem exists_global_det_lower_sqrt_congruence (c : ℤ) (hc : c ≠ 0)
    (p : ℕ) [Fact p.Prime] (h6 : p.Coprime 6) (hpc : ¬ (p : ℤ) ∣ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s r : ℕ), 0 < s →
      ∀ (center : Fin 3 → ℤ),
      center 0 ^ 6 + center 1 ^ 6 - center 2 ^ 6 = c →
      ∀ (z : Fin s → Fin 3 → ℤ),
      (∀ j k, (p : ℤ) ^ r ∣ z j k - center k) →
      (∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c) →
      ∀ (F : Fin s → MvPolynomial (Fin 3) ℤ),
      (Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) ≠ 0) →
      Real.sqrt 2 / 3 * s * Real.sqrt s * (Real.log s + 2 * r * Real.log p) -
        C * s * Real.sqrt s - 3 * s * r * Real.log p ≤
      Real.log |((Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) : ℤ) : ℝ)| := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_global_det_lower_congruence c hc p h6 hpc
  let C := (2 : ℝ) / 3 * Real.sqrt 2 * (C₀ + Real.log 2) + 3 * Real.log 4
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro s r hs center hcenter z hres hz F hD
  have hm : 1 ≤ Nat.sqrt s := Nat.sqrt_pos.mpr hs
  have h := hbound (Nat.sqrt s) s r hm hs center hcenter z hres hz F hD
  have hroot : Real.sqrt (2 * (s : ℝ)) = Real.sqrt 2 * Real.sqrt s :=
    Real.sqrt_mul (by norm_num) _
  let A := (2 : ℝ) / 3 * s * Real.sqrt (2 * s)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hlog : A * (Real.log (s : ℝ) / 2 - Real.log 2 + r * Real.log p - C₀) ≤
      A * (Real.log (Nat.sqrt s : ℝ) + r * Real.log p - C₀) := by
    apply mul_le_mul_of_nonneg_left _ hA
    linarith only [log_natSqrt_lower s hs]
  have hcut : 3 * Real.log 4 * s * (Nat.sqrt s : ℝ) ≤
      3 * Real.log 4 * s * Real.sqrt s :=
    mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)
  calc
    _ = A * (Real.log (s : ℝ) / 2 - Real.log 2 + r * Real.log p - C₀) -
        3 * Real.log 4 * s * Real.sqrt s - 3 * s * r * Real.log p := by
      dsimp only [A, C]
      rw [hroot]
      ring
    _ ≤ A * (Real.log (Nat.sqrt s : ℝ) + r * Real.log p - C₀) -
        3 * s * (Real.log 4 * Nat.sqrt s + r * Real.log p) := by
      nlinarith only [hlog, hcut]
    _ ≤ _ := h

#print axioms exists_global_det_lower_sqrt_congruence
-- 'Erdos477.Counting.exists_global_det_lower_sqrt_congruence' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
