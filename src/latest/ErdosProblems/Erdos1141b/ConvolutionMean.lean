import ErdosProblems.Erdos1141b.Hyperbola
import BoundedGaps.BombieriVinogradov.Analytic.NonprincipalLFunctionAbel

/-!
# Mean values of the quadratic zeta convolution

The first estimate uses Pólya–Vinogradov. A later refinement will use the
short-sum estimate when the cutoff is below the square-root threshold.
-/

open scoped BigOperators

namespace Erdos1141b

open BoundedGaps.Maynard

lemma zetaMul_prefix_eq_sum_mul_div {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, χ.zetaMul n) =
      ∑ n ∈ Finset.Icc 1 X, χ (n : ZMod q) * (X / n : ℕ) := by
  rw [show Finset.Icc 1 X = Finset.Ioc 0 X by
    simpa using Finset.Icc_succ_left_eq_Ioc 0 X]
  simp only [DirichletCharacter.zetaMul]
  rw [mul_comm, ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := (Finset.mem_Ioc.mp hn).1.ne'
  simp only [toArithmeticFunction, ArithmeticFunction.coe_mk, hn0, if_false]

theorem norm_zetaMul_prefix_sub_main_le {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (X D : ℕ) (hD : 0 < D) (hDX : D ≤ X) :
    ‖(∑ n ∈ Finset.Icc 1 X, χ.zetaMul n) - (X : ℂ) * χ.LFunction 1‖ ≤
      (D : ℝ) + (8 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * X / D := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.le)
  have h := norm_sum_mul_div_sub_main_le (fun n ↦ χ (n : ZMod q))
    (fun n ↦ χ.norm_le_one n)
    (2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
    (4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / D) (χ.LFunction 1)
    (fun Y ↦ norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log hq χ hχ Y)
    X D hD hDX (norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le hq χ hχ D hD)
  rw [zetaMul_prefix_eq_sum_mul_div]
  apply h.trans
  calc
    _ ≤ (D : ℝ) + 2 * ((X : ℝ) / D) * (2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) +
        X * (4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / D) := by
      gcongr
      exact Nat.cast_div_le
    _ = _ := by ring

/-- The convolution has a square-root error with an explicit modulus-dependent constant. -/
theorem norm_zetaMul_prefix_sub_main_le_sqrt {q : ℕ} [NeZero q]
    (hq : 1 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (X : ℕ) :
    ‖(∑ n ∈ Finset.Icc 1 X, χ.zetaMul n) - (X : ℂ) * χ.LFunction 1‖ ≤
      (1 + 16 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * Real.sqrt (X : ℝ) := by
  by_cases hX : X = 0
  · subst X; simp
  have hXpos : 0 < X := Nat.pos_of_ne_zero hX
  let D := Nat.sqrt X
  have hD : 0 < D := Nat.sqrt_pos.mpr hXpos
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDone : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDhi : (D : ℝ) ≤ Real.sqrt (X : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hDlo : Real.sqrt (X : ℝ) ≤ 2 * D := by
    have h := Real.real_sqrt_lt_nat_sqrt_succ (a := X)
    change Real.sqrt (X : ℝ) < (D : ℝ) + 1 at h
    linarith
  have hquot : (X : ℝ) / D ≤ 2 * Real.sqrt (X : ℝ) := by
    apply (div_le_iff₀ hDr).mpr
    have h := mul_le_mul_of_nonneg_left hDlo (Real.sqrt_nonneg (X : ℝ))
    have hs := Real.sq_sqrt (Nat.cast_nonneg X)
    nlinarith
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq.le)
  apply (norm_zetaMul_prefix_sub_main_le hq χ hχ X D hD (Nat.sqrt_le_self X)).trans
  calc
    _ = (D : ℝ) + (8 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) * ((X : ℝ) / D) := by ring
    _ ≤ Real.sqrt (X : ℝ) + (8 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
        (2 * Real.sqrt (X : ℝ)) := by gcongr
    _ = _ := by ring

end Erdos1141b
