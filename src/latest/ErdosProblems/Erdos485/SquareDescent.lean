import Mathlib

/-!
# Square descent for sparse polynomials

The key observation is that, in characteristic zero, squaring cannot hide the
least exponent outside a prescribed divisibility class.  If `n` is the least
exponent of `A` not divisible by `d`, all the interior summands in the
convolution formula for the coefficient of degree `n` vanish.  That
coefficient is therefore `2 * A.coeff 0 * A.coeff n`, which is nonzero.
-/

namespace Erdos485

open Polynomial

noncomputable section

/-- A polynomial whose support is contained in the multiples of `d` is a
polynomial in `X ^ d`.  The witness is obtained by dividing all exponents by
`d`. -/
theorem exists_eq_comp_X_pow_of_support_dvd
    {R : Type*} [CommSemiring R] (A : R[X]) (d : ℕ)
    (hdiv : ∀ n ∈ A.support, d ∣ n) :
    ∃ B : R[X], A = B.comp (X ^ d) := by
  classical
  let B : R[X] := ∑ n ∈ A.support, C (A.coeff n) * X ^ (n / d)
  refine ⟨B, ?_⟩
  calc
    A = ∑ n ∈ A.support, C (A.coeff n) * X ^ n :=
      A.as_sum_support_C_mul_X_pow
    _ = ∑ n ∈ A.support,
          (C (A.coeff n) * X ^ (n / d)).comp (X ^ d) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Polynomial.C_mul_comp, Polynomial.X_pow_comp]
      rw [← pow_mul, Nat.mul_div_cancel' (hdiv n hn)]
    _ = B.comp (X ^ d) := by
      dsimp only [B]
      rw [Polynomial.sum_comp]

/-- If a polynomial over a characteristic-zero field has nonzero constant
coefficient and every exponent occurring in its square is divisible by `d`,
then every exponent occurring in the polynomial itself is divisible by `d`.

This is the square-descent step used in the proof of Erdős Problem 485. -/
theorem square_support_dvd_imp_support_dvd
    {K : Type*} [Field K] [CharZero K]
    (A : K[X]) (d : ℕ) (hA0 : A.coeff 0 ≠ 0) (_hd : 0 < d)
    (hSq : ∀ n ∈ (A ^ 2).support, d ∣ n) :
    ∀ n ∈ A.support, d ∣ n := by
  classical
  by_contra h
  push Not at h
  let bad : Finset ℕ := A.support.filter fun n ↦ ¬d ∣ n
  have hbad : bad.Nonempty := by
    obtain ⟨n, hnA, hn⟩ := h
    exact ⟨n, by simp [bad, hnA, hn]⟩
  let n : ℕ := bad.min' hbad
  have hn_bad : n ∈ bad := Finset.min'_mem bad hbad
  have hnA : n ∈ A.support := (Finset.mem_filter.mp hn_bad).1
  have hnd : ¬d ∣ n := (Finset.mem_filter.mp hn_bad).2
  have hn0 : n ≠ 0 := by
    intro hn
    apply hnd
    simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hminimal {k : ℕ} (hk : k < n) (hkA : k ∈ A.support) : d ∣ k := by
    by_contra hkd
    have hkbad : k ∈ bad := by simp [bad, hkA, hkd]
    have hnk : n ≤ k := Finset.min'_le bad k hkbad
    omega
  have hinterior {k : ℕ} (hk : k ∈ Finset.range n) (hk0 : k ≠ 0) :
      A.coeff k * A.coeff (n - k) = 0 := by
    have hkn : k < n := Finset.mem_range.mp hk
    by_cases hkcoeff : A.coeff k = 0
    · simp [hkcoeff]
    have hkA : k ∈ A.support := Polynomial.mem_support_iff.mpr hkcoeff
    have hdk : d ∣ k := hminimal hkn hkA
    have hsub_lt : n - k < n := Nat.sub_lt hnpos (Nat.pos_of_ne_zero hk0)
    have hsubcoeff : A.coeff (n - k) = 0 := by
      by_contra hsubcoeff
      have hsubA : n - k ∈ A.support :=
        Polynomial.mem_support_iff.mpr hsubcoeff
      have hdsub : d ∣ n - k := hminimal hsub_lt hsubA
      apply hnd
      rw [← Nat.sub_add_cancel hkn.le]
      exact Nat.dvd_add hdsub hdk
    simp [hsubcoeff]
  have hcoeff : (A ^ 2).coeff n = 2 * A.coeff 0 * A.coeff n := by
    rw [pow_two, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ]
    have hfirst :
        (∑ k ∈ Finset.range n, A.coeff k * A.coeff (n - k)) =
          A.coeff 0 * A.coeff n := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k hk hk0
        exact hinterior hk hk0
      · simp [hnpos.ne']
    rw [hfirst]
    simp
    ring
  have hncoeff : A.coeff n ≠ 0 := Polynomial.mem_support_iff.mp hnA
  have hsqcoeff : (A ^ 2).coeff n ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hA0) hncoeff
  exact hnd (hSq n (Polynomial.mem_support_iff.mpr hsqcoeff))

/-- Composition form of `square_support_dvd_imp_support_dvd`: under the same
hypotheses, `A` is a polynomial in `X ^ d`. -/
theorem exists_eq_comp_X_pow_of_square_support_dvd
    {K : Type*} [Field K] [CharZero K]
    (A : K[X]) (d : ℕ) (hA0 : A.coeff 0 ≠ 0) (hd : 0 < d)
    (hSq : ∀ n ∈ (A ^ 2).support, d ∣ n) :
    ∃ B : K[X], A = B.comp (X ^ d) :=
  exists_eq_comp_X_pow_of_support_dvd A d
    (square_support_dvd_imp_support_dvd A d hA0 hd hSq)

end

end Erdos485
