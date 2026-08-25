import Util.Linnik.ExceptionalZeros

/-!
# Cancellation in the quadratic character pair

The principal character and the exceptional character occur together in
`chi, chi * chi1`.  Thus their pole and zero contributions cancel to first
order in `1 - beta`.
-/

namespace Linnik

open Complex
open scoped Classical

theorem quadratic_mul_right_cancel_self {q : ℕ}
    (chi1 chi : DirichletCharacter ℂ q) (hchi1 : chi1 ^ 2 = 1) :
    (chi * chi1) * chi1 = chi := by
  rw [mul_assoc, ← pow_two, hchi1, mul_one]

theorem quadratic_mul_eq_one_iff {q : ℕ}
    (chi1 chi : DirichletCharacter ℂ q) (hchi1 : chi1 ^ 2 = 1) :
    chi * chi1 = 1 ↔ chi = chi1 := by
  constructor
  · intro h
    calc
      chi = (chi * chi1) * chi1 := (quadratic_mul_right_cancel_self chi1 chi hchi1).symm
      _ = chi1 := by rw [h, one_mul]
  · intro h
    rw [h, ← pow_two, hchi1]

theorem quadratic_mul_eq_self_iff {q : ℕ}
    (chi1 chi : DirichletCharacter ℂ q) (hchi1 : chi1 ^ 2 = 1) :
    chi * chi1 = chi1 ↔ chi = 1 := by
  constructor
  · intro h
    calc
      chi = (chi * chi1) * chi1 := (quadratic_mul_right_cancel_self chi1 chi hchi1).symm
      _ = 1 := by rw [h, ← pow_two, hchi1]
  · intro h
    rw [h, one_mul]

theorem quadratic_pair_pole_sub_exceptional_eq {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (hchi1 : chi1 ≠ 1)
    (hsquare : chi1 ^ 2 = 1) (beta t : ℝ) (n : ℕ) :
    (principalPolePower chi t n + principalPolePower (chi * chi1) t n) -
      (removedExceptionalPower chi1 chi beta t n +
        removedExceptionalPower chi1 (chi * chi1) beta t n) =
    if chi = 1 ∨ chi = chi1 then
      (((1 : ℂ) + t * I) ^ n)⁻¹ -
        (if |t| ≤ 4 then ((((2 - beta : ℝ) : ℂ) + t * I) ^ n)⁻¹ else 0)
    else 0 := by
  have hcenter : (2 : ℂ) + t * I - 1 = (1 : ℂ) + t * I := by ring
  have hbeta : (2 : ℂ) + t * I - beta = ((2 - beta : ℝ) : ℂ) + t * I := by
    push_cast
    ring
  have hself : chi1 * chi1 = 1 := by simpa only [pow_two] using hsquare
  by_cases hchi₀ : chi = 1
  · subst chi
    simp [principalPolePower, removedExceptionalPower, hchi1, hchi1.symm, hcenter, hbeta]
  by_cases hchi₁ : chi = chi1
  · subst chi
    simp [principalPolePower, removedExceptionalPower, hchi1, hchi1.symm, hself, hcenter, hbeta]
  · have hprod₀ : chi * chi1 ≠ 1 := by
      intro h
      exact hchi₁ ((quadratic_mul_eq_one_iff chi1 chi hsquare).mp h)
    have hprod₁ : chi * chi1 ≠ chi1 := by
      intro h
      exact hchi₀ ((quadratic_mul_eq_self_iff chi1 chi hsquare).mp h)
    simp [principalPolePower, removedExceptionalPower, hchi₀, hchi₁, hprod₀, hprod₁]

theorem norm_quadratic_pair_pole_sub_exceptional_le {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (hchi1 : chi1 ≠ 1)
    (hsquare : chi1 ^ 2 = 1) {beta : ℝ} (hbeta : beta ≤ 1) (t : ℝ) (n : ℕ) :
    ‖(principalPolePower chi t n + principalPolePower (chi * chi1) t n) -
      (removedExceptionalPower chi1 chi beta t n +
        removedExceptionalPower chi1 (chi * chi1) beta t n)‖ ≤
      n * (1 - beta) + (1 / 4 : ℝ) ^ n := by
  rw [quadratic_pair_pole_sub_exceptional_eq chi1 chi hchi1 hsquare]
  split_ifs with hchi ht
  · exact (norm_principal_exceptional_power_difference_le hbeta t n).trans
      (le_add_of_nonneg_right (by positivity))
  · rw [sub_zero]
    exact (norm_principalPolePower_le_at_large_height (le_of_not_ge ht) n).trans
      (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hbeta)))
  · simp only [norm_zero]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hbeta)) (by positivity)

noncomputable def remainingZeroPowerSum {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ) (n : ℕ) : ℂ :=
  (remainingCharacterZeros chi1 chi beta t).sum
    (fun rho m ↦ (m : ℂ) / ((2 : ℂ) + t * I - rho) ^ n)

/-- The exceptional zero leaves a factor of its distance to one in the
real-part power-sum bound. -/
theorem exists_remaining_four_zeroPowerSum_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi1 chi : DirichletCharacter ℂ q), chi1 ≠ 1 → chi1 ^ 2 = 1 →
          ∀ beta : ℝ, 0 < beta → beta < 1 →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            ∀ (t : ℝ) (n : ℕ), 1 ≤ n →
              (remainingZeroPowerSum chi1 1 beta 0 n +
                remainingZeroPowerSum chi1 chi1 beta 0 n +
                remainingZeroPowerSum chi1 chi beta t n +
                remainingZeroPowerSum chi1 (chi * chi1) beta t n).re ≤
              2 * n * (1 - beta) +
                (64 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) + 2) / (3 : ℝ) ^ n := by
  obtain ⟨A, hA, hbound⟩ := exists_quadratic_four_zeroPowerSum_bound
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi1 chi hchi1 hsquare beta hbeta₀ hbeta₁ hzero t n hn
  have h := hbound q hq chi1 chi hsquare t n hn
  have hdecomp (psi : DirichletCharacter ℂ q) (u : ℝ) :
      zeroPowerSum psi u n = remainingZeroPowerSum chi1 psi beta u n +
        removedExceptionalPower chi1 psi beta u n :=
    zeroPowerSum_eq_remaining_add_exceptional chi1 psi hchi1 hbeta₀ hbeta₁ hzero u n
  rw [hdecomp, hdecomp, hdecomp, hdecomp] at h
  have hp₀ := norm_quadratic_pair_pole_sub_exceptional_le
    chi1 (1 : DirichletCharacter ℂ q) hchi1 hsquare hbeta₁.le 0 n
  simp only [one_mul] at hp₀
  have hp₁ := norm_quadratic_pair_pole_sub_exceptional_le
    chi1 chi hchi1 hsquare hbeta₁.le t n
  have hr₀ := (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hp₀)
  have hr₁ := (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans hp₁)
  have hquarter : (1 / 4 : ℝ) ^ n ≤ ((3 : ℝ) ^ n)⁻¹ := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  simp only [Complex.add_re, Complex.sub_re] at h hr₀ hr₁ ⊢
  linear_combination h + hr₀ + hr₁ + 2 * hquarter

end Linnik
