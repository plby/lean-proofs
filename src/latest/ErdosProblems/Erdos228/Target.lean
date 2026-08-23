import Mathlib.Analysis.Polynomial.Fourier
import Mathlib.Tactic

/-!
# Erdős Problem 228: polynomial and target interface

This file contains the finite-vector representation of a Littlewood polynomial
and the final conversion from the usual non-strict flatness theorem to the
strict, eventual statement used by the formal-conjectures specification.
-/

open Filter

namespace Erdos228

noncomputable section

/-! ## Littlewood polynomials from finite sign vectors -/

/-- The polynomial whose coefficient of `X ^ j` is `eps j`, for
`j : Fin (n + 1)`. -/
def signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ) : Polynomial ℂ :=
  ∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)

@[simp]
theorem coeff_signPoly_of_le (n i : ℕ) (eps : Fin (n + 1) → ℂ)
    (hi : i ≤ n) :
    (signPoly n eps).coeff i = eps ⟨i, Nat.lt_succ_iff.2 hi⟩ := by
  classical
  change (Polynomial.lcoeff ℂ i)
      (∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [Fintype.sum_eq_single ⟨i, Nat.lt_succ_iff.2 hi⟩]
  · rw [if_pos rfl]
  · intro b hb
    simp only [ite_eq_right_iff]
    intro hbi
    exact (hb (Fin.ext hbi)).elim

@[simp]
theorem coeff_signPoly_of_lt (n i : ℕ) (eps : Fin (n + 1) → ℂ)
    (hi : n < i) :
    (signPoly n eps).coeff i = 0 := by
  classical
  change (Polynomial.lcoeff ℂ i)
      (∑ j : Fin (n + 1), Polynomial.monomial j.1 (eps j)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [ite_eq_right_iff]
  intro hji
  omega

/-- A polynomial constructed from nonzero signs has the expected degree. -/
theorem degree_signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) :
    (signPoly n eps).degree = n := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro i hi
    exact coeff_signPoly_of_lt n i eps (by exact_mod_cast hi)
  · rw [coeff_signPoly_of_le n n eps (le_refl n)]
    rcases heps ⟨n, Nat.lt_succ_self n⟩ with h | h <;> rw [h] <;> norm_num

/-- All coefficients through the degree of a sign polynomial are signs. -/
theorem coeff_signPoly_isSign (n : ℕ) (eps : Fin (n + 1) → ℂ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) :
    ∀ i ≤ n, (signPoly n eps).coeff i = 1 ∨ (signPoly n eps).coeff i = -1 := by
  intro i hi
  rw [coeff_signPoly_of_le n i eps hi]
  exact heps _

@[simp]
theorem eval_signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ) (z : ℂ) :
    (signPoly n eps).eval z = ∑ j : Fin (n + 1), eps j * z ^ j.1 := by
  simp [signPoly, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

theorem norm_eps_eq_one {n : ℕ} {eps : Fin (n + 1) → ℂ}
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) (j : Fin (n + 1)) :
    ‖eps j‖ = 1 := by
  rcases heps j with h | h <;> rw [h] <;> norm_num

/-- A sign polynomial has precisely the exponents `0, ..., n` in its support. -/
theorem support_signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) :
    (signPoly n eps).support = Finset.range (n + 1) := by
  ext i
  simp only [Polynomial.mem_support_iff, Finset.mem_range]
  by_cases hi : i ≤ n
  · rw [coeff_signPoly_of_le n i eps hi]
    rcases heps ⟨i, Nat.lt_succ_iff.2 hi⟩ with h | h <;>
      simp [h, Nat.lt_succ_iff.2 hi]
  · have hni : n < i := Nat.lt_of_not_ge hi
    rw [coeff_signPoly_of_lt n i eps hni]
    exact iff_of_false (by simp) (by omega)

/-- Parseval's identity specializes to `n + 1` for a Littlewood polynomial
of degree `n`. -/
theorem parseval_signPoly (n : ℕ) (eps : Fin (n + 1) → ℂ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) :
    Real.circleAverage (fun z ↦ ‖(signPoly n eps).eval z‖ ^ 2) 0 1 = n + 1 := by
  rw [← Polynomial.sum_sq_norm_coeff_eq_circleAverage]
  rw [support_signPoly n eps heps]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ‖(signPoly n eps).coeff i‖ ^ 2 = (1 : ℝ) := by
    intro i hi
    rw [coeff_signPoly_of_le n i eps
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))]
    rw [norm_eps_eq_one heps]
    norm_num
  calc
    ∑ i ∈ Finset.range (n + 1), ‖(signPoly n eps).coeff i‖ ^ 2 =
        ∑ i ∈ Finset.range (n + 1), (1 : ℝ) := by
          apply Finset.sum_congr rfl hterm
    _ = n + 1 := by simp

/-- The triangle inequality gives the elementary `n + 1` upper bound on the
unit circle.  The flatness theorem improves this to order `sqrt n`. -/
theorem norm_eval_signPoly_le (n : ℕ) (eps : Fin (n + 1) → ℂ)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(signPoly n eps).eval z‖ ≤ n + 1 := by
  rw [eval_signPoly]
  calc
    ‖∑ j : Fin (n + 1), eps j * z ^ j.1‖ ≤
        ∑ j : Fin (n + 1), ‖eps j * z ^ j.1‖ := norm_sum_le _ _
    _ = ∑ _j : Fin (n + 1), (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_pow, norm_eps_eq_one heps, hz]
      simp
    _ = n + 1 := by simp

/-! ## Conversion of the standard flatness theorem to the target -/

/-- The usual non-strict, all-degrees formulation of the theorem of
Balister--Bollobás--Morris--Sahasrabudhe--Tiba. -/
def LittlewoodFlatCore : Prop :=
  ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    ∃ p : Polynomial ℂ, p.degree = n ∧
      (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        c * Real.sqrt n ≤ ‖p.eval z‖ ∧
        ‖p.eval z‖ ≤ C * Real.sqrt n

/-- Positive non-strict flatness constants yield the strict inequalities and
eventual quantifier in the exact formal-conjectures statement. -/
theorem target_of_core (hcore : LittlewoodFlatCore) :
    ∃ (c₁ : ℝ) (c₂ : ℝ), ∀ᶠ n : ℕ in Filter.atTop,
    ∃ p : Polynomial ℂ, p.degree = n ∧
    (∀ i ≤ n, p.coeff i = 1 ∨ p.coeff i = -1) ∧
    ∀ z : ℂ, ‖z‖ = 1 →
    ( √n < c₁ * ‖p.eval z‖ ∧ ‖p.eval z‖ < c₂ * √n ) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _
    rcases hcore with ⟨c, C, hc, hC, hflat⟩
    refine ⟨2 / c, 2 * C, ?_⟩
    rw [Filter.eventually_atTop]
    refine ⟨2, fun n hn ↦ ?_⟩
    rcases hflat n hn with ⟨p, hpdeg, hpcoeff, hpflat⟩
    refine ⟨p, hpdeg, hpcoeff, fun z hz ↦ ?_⟩
    rcases hpflat z hz with ⟨hlower, hupper⟩
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    constructor
    · have hcne : c ≠ 0 := ne_of_gt hc
      calc
        Real.sqrt n < 2 * Real.sqrt n := by linarith
        _ = (2 / c) * (c * Real.sqrt n) := by field_simp
        _ ≤ (2 / c) * ‖p.eval z‖ := by gcongr
    · calc
        ‖p.eval z‖ ≤ C * Real.sqrt n := hupper
        _ < (2 * C) * Real.sqrt n := by nlinarith
  · intro _
    trivial

end

end Erdos228
