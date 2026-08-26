import ErdosProblems.Erdos1148.RealDirichletPositivity
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! # Finite Euler factors for a real character induced to a larger modulus -/

namespace Erdos1148.DukeArithmetic

theorem complexDirichletCharacter_changeLevel {m n : ℕ} (hmn : m ∣ n)
    (χ : DirichletCharacter ℝ m) :
    complexDirichletCharacter (χ.changeLevel hmn) =
      (complexDirichletCharacter χ).changeLevel hmn := by
  apply MulChar.ext
  intro a
  simp only [complexDirichletCharacter, MulChar.ringHomComp_apply,
    DirichletCharacter.changeLevel_eq_cast_of_dvd]

theorem realDirichletValue_changeLevel_one {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m ∣ n) (χ : DirichletCharacter ℝ m) (hχ : χ ≠ 1) :
    realDirichletValue (χ.changeLevel hmn) 1 = realDirichletValue χ 1 *
      ∏ p ∈ n.primeFactors, (1 - χ p / (p : ℝ)) := by
  have hchild : χ.changeLevel hmn ≠ 1 := (DirichletCharacter.changeLevel_eq_one_iff hmn).not.mpr hχ
  have hcomplex : complexDirichletCharacter χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (f := Complex.ofRealHom) Complex.ofReal_injective).mpr hχ
  apply Complex.ofReal_injective
  rw [realDirichletValue_one_eq_LFunction (χ.changeLevel hmn) hchild,
    complexDirichletCharacter_changeLevel,
    DirichletCharacter.LFunction_changeLevel hmn (complexDirichletCharacter χ) (Or.inl hcomplex),
    ← realDirichletValue_one_eq_LFunction χ hχ]
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  change (1 : ℂ) - (χ p : ℂ) * (p : ℂ) ^ (-(1 : ℂ)) = 1 - (χ p : ℂ) / (p : ℂ)
  rw [Complex.cpow_neg_one, div_eq_mul_inv]

theorem realDirichletValue_le_primeFactorLoss_mul_changeLevel {m n : ℕ} [NeZero m] [NeZero n]
    (hmn : m ∣ n) (χ : DirichletCharacter ℝ m) (hχ : χ ≠ 1) :
    realDirichletValue χ 1 ≤ (4 : ℝ) ^ n.primeFactors.card *
      realDirichletValue (χ.changeLevel hmn) 1 := by
  have hfactor : ∀ p ∈ n.primeFactors, (1 : ℝ) ≤ 4 * (1 - χ p / (p : ℝ)) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hχp : χ p ≤ 1 := (le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using χ.norm_le_one p)
    have hdiv : χ p / (p : ℝ) ≤ 1 / 2 := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  have hprod := Finset.one_le_prod hfactor
  rw [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  have h := mul_le_mul_of_nonneg_left hprod (realDirichletValue_one_pos χ hχ).le
  rw [mul_one] at h
  rw [realDirichletValue_changeLevel_one hmn χ hχ]
  exact h.trans_eq (mul_left_comm _ _ _)

end Erdos1148.DukeArithmetic
