/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Choosing a square-root prime cutoff in the global determinant estimate.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.GlobalDeterminant

namespace Erdos477.Counting

lemma log_natSqrt_lower (s : ℕ) (hs : 0 < s) :
    Real.log (s : ℝ) / 2 - Real.log 2 ≤ Real.log (Nat.sqrt s : ℝ) := by
  have hm : 0 < Nat.sqrt s := Nat.sqrt_pos.mpr hs
  have hmR : (1 : ℝ) ≤ Nat.sqrt s := by exact_mod_cast hm
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hupper : Real.sqrt (s : ℝ) ≤ 2 * Nat.sqrt s := by
    have h := Real.real_sqrt_le_nat_sqrt_succ (a := s)
    linarith
  have hlog := Real.log_le_log (Real.sqrt_pos.mpr hsR) hupper
  rw [Real.log_sqrt hsR.le, Real.log_mul (by norm_num) (by positivity)] at hlog
  linarith

/-- A nonzero determinant on the sextic surface has the characteristic
`s^(3/2) log s` lower bound, with an error constant depending only on `c`. -/
theorem exists_global_det_lower_sqrt (c : ℤ) (hc : c ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℕ), 0 < s →
      ∀ (z : Fin s → Fin 3 → ℤ),
      (∀ j, z j 0 ^ 6 + z j 1 ^ 6 - z j 2 ^ 6 = c) →
      ∀ (F : Fin s → MvPolynomial (Fin 3) ℤ),
      (Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) ≠ 0) →
      Real.sqrt 2 / 3 * s * Real.sqrt s * Real.log s - C * s * Real.sqrt s ≤
      Real.log |((Matrix.det (Matrix.of fun i j => MvPolynomial.eval (z j) (F i)) : ℤ) : ℝ)| := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_global_det_lower c hc
  let C := (2 : ℝ) / 3 * Real.sqrt 2 * (C₀ + Real.log 2) + 3 * Real.log 4
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro s hs z hz F hD
  have hm : 1 ≤ Nat.sqrt s := Nat.sqrt_pos.mpr hs
  have h := hbound (Nat.sqrt s) s hm hs z hz F hD
  have hroot : Real.sqrt (2 * (s : ℝ)) = Real.sqrt 2 * Real.sqrt s :=
    Real.sqrt_mul (by norm_num) _
  let A := (2 : ℝ) / 3 * s * Real.sqrt (2 * s)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hlog : A * (Real.log (s : ℝ) / 2 - Real.log 2 - C₀) ≤
      A * (Real.log (Nat.sqrt s : ℝ) - C₀) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right (log_natSqrt_lower s hs) C₀) hA
  have hcut : 3 * Real.log 4 * s * (Nat.sqrt s : ℝ) ≤
      3 * Real.log 4 * s * Real.sqrt s :=
    mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by positivity)
  calc
    _ = A * (Real.log (s : ℝ) / 2 - Real.log 2 - C₀) -
        3 * Real.log 4 * s * Real.sqrt s := by
      dsimp only [A, C]
      rw [hroot]
      ring
    _ ≤ A * (Real.log (Nat.sqrt s : ℝ) - C₀) -
        3 * Real.log 4 * s * Nat.sqrt s := sub_le_sub hlog hcut
    _ ≤ _ := h

#print axioms exists_global_det_lower_sqrt
-- 'Erdos477.Counting.exists_global_det_lower_sqrt' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
