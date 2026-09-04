import Mathlib
import ErdosProblems.Erdos485.Hajos
import ErdosProblems.Erdos485.SquareDescent

/-!
# Primitive normalization for Erdős Problem 485

This file records the support bookkeeping needed to replace a polynomial by
one whose square has nonzero constant coefficient and primitive exponent
set.  The normalization uses polynomial reversal to remove the initial
monomial and then the square-descent lemma.
-/

namespace Erdos485

open Polynomial

noncomputable section

/-- Substitution `X ↦ X^d`, for positive `d`, sends the support bijectively
to its dilation by `d`. -/
theorem support_comp_X_pow {R : Type*} [Semiring R] (p : R[X]) {d : ℕ} (hd : 0 < d) :
    (p.comp (X ^ d)).support = p.support.image (fun n ↦ d * n) := by
  rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def]
  ext k
  simp only [Polynomial.mem_support_iff, Polynomial.finsetSum_coeff, Finset.mem_image]
  constructor
  · intro hk
    obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    rw [← pow_mul, Polynomial.coeff_C_mul_X_pow] at hterm
    have hkn : k = d * n := by
      exact (ite_ne_right_iff.mp hterm).1
    exact ⟨n, Polynomial.mem_support_iff.mp hn, hkn.symm⟩
  · rintro ⟨n, hn, rfl⟩
    rw [Finset.sum_eq_single n]
    · rw [← pow_mul, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
      exact hn
    · intro m hm hmn
      have hne : d * n ≠ d * m := by
        exact fun h ↦ hmn (Nat.eq_of_mul_eq_mul_left hd h.symm)
      rw [← pow_mul, Polynomial.coeff_C_mul_X_pow, if_neg hne]
    · simp [hn]

/-- In particular, positive monomial substitution preserves support
cardinality. -/
theorem card_support_comp_X_pow {R : Type*} [Semiring R] (p : R[X]) {d : ℕ}
    (hd : 0 < d) :
    (p.comp (X ^ d)).support.card = p.support.card := by
  rw [support_comp_X_pow p hd]
  exact Finset.card_image_of_injective _ fun _ _ h ↦ Nat.eq_of_mul_eq_mul_left hd h

/-- The gcd of a dilated finite exponent set is dilated by the same factor. -/
theorem finset_gcd_image_mul_left (s : Finset ℕ) (d : ℕ) :
    (s.image (fun n ↦ d * n)).gcd id = d * s.gcd id := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
      simp [ih]

/-- Data supplied by primitive normalization.  `original` is retained in the
structure so later arguments can use the support-count equalities without
unfolding the construction. -/
structure PrimitiveNormalization {K : Type*} [Field K] [CharZero K]
    (P : K[X]) where
  /-- The polynomial after reversal, gcd extraction, and square descent. -/
  poly : K[X]
  /-- The common divisor extracted from the square's exponents. -/
  dilation : ℕ
  dilation_pos : 0 < dilation
  reversed_eq_comp : P.reverse = poly.comp (X ^ dilation)
  coeff_zero_ne : poly.coeff 0 ≠ 0
  two_le_support : 2 ≤ poly.support.card
  card_support_eq : poly.support.card = P.support.card
  card_sq_support_eq : (poly ^ 2).support.card = (P ^ 2).support.card
  three_le_sq_support : 3 ≤ (poly ^ 2).support.card
  primitive_sq_support : (poly ^ 2).support.gcd id = 1
  natDegree_sq : (poly ^ 2).natDegree = 2 * poly.natDegree

/-- Every polynomial with at least two terms admits primitive normalization.

Reversal removes its initial monomial (without changing any support count).
The gcd of the exponents in the reversed square is then extracted, and
square descent supplies the normalized polynomial. -/
theorem exists_primitiveNormalization {K : Type*} [Field K] [CharZero K]
    (P : K[X]) (hP : 2 ≤ P.support.card) :
    Nonempty (PrimitiveNormalization P) := by
  classical
  have hPne : P ≠ 0 := by
    intro h
    simp [h] at hP
  let A : K[X] := P.reverse
  have hA0 : A.coeff 0 ≠ 0 := by
    simpa [A] using Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hAcard : A.support.card = P.support.card := by
    exact card_support_reverse P
  have hAcard2 : 2 ≤ A.support.card := by omega
  have hAdeg : 0 < A.natDegree := by
    by_contra h
    have hdeg0 : A.natDegree = 0 := by omega
    have hsub : A.support ⊆ {0} := by
      intro n hn
      have hnle : n ≤ A.natDegree := Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hn)
      simp only [Finset.mem_singleton] at hnle ⊢
      omega
    have hcardle : A.support.card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    omega
  have hAne : A ≠ 0 := by
    exact fun h ↦ hA0 (by simp [h])
  have hAsqne : A ^ 2 ≠ 0 := pow_ne_zero _ hAne
  have hAsqdeg : 0 < (A ^ 2).natDegree := by
    rw [Polynomial.natDegree_pow]
    omega
  let d : ℕ := (A ^ 2).support.gcd id
  have hd0 : d ≠ 0 := by
    change (A ^ 2).support.gcd id ≠ 0
    rw [Finset.gcd_ne_zero_iff]
    exact ⟨(A ^ 2).natDegree,
      Polynomial.natDegree_mem_support_of_nonzero hAsqne, hAsqdeg.ne'⟩
  have hd : 0 < d := Nat.pos_of_ne_zero hd0
  have hdiv : ∀ n ∈ (A ^ 2).support, d ∣ n := by
    intro n hn
    exact Finset.gcd_dvd hn
  obtain ⟨B, hAB⟩ := exists_eq_comp_X_pow_of_square_support_dvd A d hA0 hd hdiv
  have hB0 : B.coeff 0 ≠ 0 := by
    have hcoeff : A.coeff 0 = B.coeff 0 := by
      calc
        A.coeff 0 = A.eval 0 := Polynomial.coeff_zero_eq_eval_zero A
        _ = (B.comp (X ^ d)).eval 0 := congrArg (Polynomial.eval 0) hAB
        _ = B.coeff 0 := by
          rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
            zero_pow hd.ne']
          exact (Polynomial.coeff_zero_eq_eval_zero B).symm
    exact hcoeff ▸ hA0
  have hBcard : B.support.card = P.support.card := by
    have hcompcard := card_support_comp_X_pow B hd
    rw [← hAB] at hcompcard
    exact hcompcard.symm.trans hAcard
  have hsqcomp : A ^ 2 = (B ^ 2).comp (X ^ d) := by
    rw [hAB]
    simp only [pow_two, Polynomial.mul_comp]
  have hAsqcardP : (A ^ 2).support.card = (P ^ 2).support.card := by
    have hrev : A ^ 2 = (P ^ 2).reverse := by
      simp only [A, pow_two, Polynomial.reverse_mul_of_domain]
    rw [hrev, card_support_reverse]
  have hBsqcard : (B ^ 2).support.card = (P ^ 2).support.card := by
    have hcompcard := card_support_comp_X_pow (B ^ 2) hd
    rw [← hsqcomp] at hcompcard
    exact hcompcard.symm.trans hAsqcardP
  have hprimitive : (B ^ 2).support.gcd id = 1 := by
    have hsupp : (A ^ 2).support =
        (B ^ 2).support.image (fun n ↦ d * n) := by
      rw [hsqcomp, support_comp_X_pow (B ^ 2) hd]
    have hgcd : d = d * (B ^ 2).support.gcd id := by
      calc
        d = (A ^ 2).support.gcd id := rfl
        _ = ((B ^ 2).support.image (fun n ↦ d * n)).gcd id := by rw [hsupp]
        _ = d * (B ^ 2).support.gcd id := finset_gcd_image_mul_left _ _
    have hone : 1 = (B ^ 2).support.gcd id := by
      apply Nat.eq_of_mul_eq_mul_left hd
      simpa using hgcd
    exact hone.symm
  exact ⟨{
    poly := B
    dilation := d
    dilation_pos := hd
    reversed_eq_comp := hAB
    coeff_zero_ne := hB0
    two_le_support := by rw [hBcard]; exact hP
    card_support_eq := hBcard
    card_sq_support_eq := hBsqcard
    three_le_sq_support := by
      apply three_le_sq_support_card_of_coeff_zero_ne hB0
      by_contra hdeg
      have hdeg0 : B.natDegree = 0 := by omega
      have hsub : B.support ⊆ {0} := by
        intro n hn
        have hnle : n ≤ B.natDegree := Polynomial.le_natDegree_of_ne_zero
          (Polynomial.mem_support_iff.mp hn)
        simp only [Finset.mem_singleton] at hnle ⊢
        omega
      have hcardle : B.support.card ≤ 1 := by simpa using Finset.card_le_card hsub
      rw [hBcard] at hcardle
      omega
    primitive_sq_support := hprimitive
    natDegree_sq := by simp [Polynomial.natDegree_pow] }⟩

/-- The increasing enumeration of the normalized square's support. -/
def PrimitiveNormalization.sqExponent {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) :
    Fin (N.poly ^ 2).support.card ↪o ℕ :=
  (N.poly ^ 2).support.orderEmbOfFin rfl

theorem PrimitiveNormalization.sqExponent_mem {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P)
    (i : Fin (N.poly ^ 2).support.card) :
    N.sqExponent i ∈ (N.poly ^ 2).support :=
  Finset.orderEmbOfFin_mem _ _ _

theorem PrimitiveNormalization.sqExponent_range {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) :
    Set.range N.sqExponent = (N.poly ^ 2).support :=
  Finset.range_orderEmbOfFin _ _

/-- The normalized polynomial is genuinely nonconstant. -/
theorem PrimitiveNormalization.natDegree_pos {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) : 0 < N.poly.natDegree := by
  by_contra hdeg
  have hdeg0 : N.poly.natDegree = 0 := by omega
  have hsub : N.poly.support ⊆ {0} := by
    intro n hn
    have hnle : n ≤ N.poly.natDegree := Polynomial.le_natDegree_of_ne_zero
      (Polynomial.mem_support_iff.mp hn)
    simp only [Finset.mem_singleton] at hnle ⊢
    omega
  have hcardle : N.poly.support.card ≤ 1 := by simpa using Finset.card_le_card hsub
  have hcardge : 2 ≤ N.poly.support.card := N.two_le_support
  omega

/-- The top exponent in the normalized square is twice the degree of the
normalized polynomial. -/
theorem PrimitiveNormalization.topExponent_eq {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (N : PrimitiveNormalization P) :
    (N.poly ^ 2).natDegree = 2 * N.poly.natDegree :=
  N.natDegree_sq

end

end Erdos485
