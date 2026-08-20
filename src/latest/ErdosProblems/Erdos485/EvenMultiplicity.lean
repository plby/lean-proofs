import Mathlib

/-!
# Even root multiplicities after the one-variable specialization

This file contains the univariate bridge in the squarefree-gap argument for
Erdős Problem 485.  A specialized square identity makes every nonzero root
of the squarefree cofactor occur with even multiplicity.  The weighted Euler
derivative has enough multiplicity at those roots, while its extra factor `X`
handles the root at zero.
-/

namespace Erdos485

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- A cleared Laurent square identity forces the cofactor to have even
multiplicity at every nonzero root.

The two powers of `X` allow either sign of the Laurent exponent after
clearing denominators.  They contribute no multiplicity at a nonzero point;
the remaining identity says that the multiplicity of `h` is a difference of
two even numbers. -/
theorem even_rootMultiplicity_of_X_pow_mul_sq_eq_C_mul_X_pow_mul_sq_mul
    (A B h : K[X]) (u v : ℕ) {c : K}
    (hA : A ≠ 0) (hB : B ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0)
    (hsq : X ^ u * A ^ 2 = C c * X ^ v * B ^ 2 * h) :
    ∀ a : K, a ≠ 0 → Even (h.rootMultiplicity a) := by
  classical
  intro a ha
  have hXu : (X : K[X]) ^ u ≠ 0 := pow_ne_zero u X_ne_zero
  have hXv : (X : K[X]) ^ v ≠ 0 := pow_ne_zero v X_ne_zero
  have hA2 : A * A ≠ 0 := mul_ne_zero hA hA
  have hB2 : B * B ≠ 0 := mul_ne_zero hB hB
  have hleft : X ^ u * (A * A) ≠ (0 : K[X]) := mul_ne_zero hXu hA2
  have hcX : C c * X ^ v ≠ (0 : K[X]) :=
    mul_ne_zero (C_ne_zero.mpr hc) hXv
  have hcXB : (C c * X ^ v) * (B * B) ≠ (0 : K[X]) :=
    mul_ne_zero hcX hB2
  have hright : ((C c * X ^ v) * (B * B)) * h ≠ (0 : K[X]) :=
    mul_ne_zero hcXB hh
  have hXua : Polynomial.rootMultiplicity a ((X : K[X]) ^ u) = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    simp only [Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero u ha
  have hXva : Polynomial.rootMultiplicity a ((X : K[X]) ^ v) = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    simp only [Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero v ha
  have hm := congrArg (Polynomial.rootMultiplicity a) hsq
  simp only [pow_two] at hm
  rw [Polynomial.rootMultiplicity_mul hleft,
    Polynomial.rootMultiplicity_mul hA2,
    Polynomial.rootMultiplicity_mul hright,
    Polynomial.rootMultiplicity_mul hcXB,
    Polynomial.rootMultiplicity_mul hcX,
    Polynomial.rootMultiplicity_mul hB2,
    Polynomial.rootMultiplicity_C, hXua, hXva] at hm
  refine ⟨A.rootMultiplicity a - B.rootMultiplicity a, ?_⟩
  omega

/-- The common form of the preceding lemma when no power of `X` occurs on
the left-hand side. -/
theorem even_rootMultiplicity_of_sq_eq_C_mul_X_pow_mul_sq_mul
    (A B h : K[X]) (v : ℕ) {c : K}
    (hA : A ≠ 0) (hB : B ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0)
    (hsq : A ^ 2 = C c * X ^ v * B ^ 2 * h) :
    ∀ a : K, a ≠ 0 → Even (h.rootMultiplicity a) := by
  simpa using
    even_rootMultiplicity_of_X_pow_mul_sq_eq_C_mul_X_pow_mul_sq_mul
      A B h 0 v hA hB hh hc (by simpa using hsq)

section AlgebraicallyClosed

variable [IsAlgClosed K] [CharZero K]

/-- If all nonzero roots of `h` have even multiplicity, then `h` divides the
square of its Euler derivative `X * h.derivative`.

At a nonzero root of multiplicity `2e`, differentiation leaves multiplicity
`2e - 1`, which is enough after squaring.  At zero, the factor `X` restores
the multiplicity lost by differentiation.  The explicit split at zero is the
point that prevents the usual informal multiplicity argument from omitting a
case. -/
theorem dvd_sq_X_mul_derivative_of_even_nonzero_rootMultiplicity
    {h : K[X]} (hh : h ≠ 0)
    (heven : ∀ a : K, a ≠ 0 → Even (h.rootMultiplicity a)) :
    h ∣ (X * h.derivative) ^ 2 := by
  classical
  by_cases hd : h.derivative = 0
  · simp [hd]
  have hX : (X : K[X]) ≠ 0 := X_ne_zero
  have hE : X * h.derivative ≠ (0 : K[X]) := mul_ne_zero hX hd
  have hE2 : (X * h.derivative) ^ 2 ≠ (0 : K[X]) := pow_ne_zero 2 hE
  have hEmul : (X * h.derivative) * (X * h.derivative) ≠ (0 : K[X]) :=
    mul_ne_zero hE hE
  rw [IsAlgClosed.dvd_iff_roots_le_roots hh hE2, Multiset.le_iff_count]
  intro a
  simp only [Polynomial.count_roots]
  rw [pow_two, Polynomial.rootMultiplicity_mul hEmul,
    Polynomial.rootMultiplicity_mul hE]
  by_cases ha0 : a = 0
  · subst a
    have hXm : Polynomial.rootMultiplicity 0 (X : K[X]) = 1 := by
      simpa using
        (Polynomial.rootMultiplicity_X_sub_C_self (R := K) (x := (0 : K)))
    rw [hXm]
    by_cases hroot : h.IsRoot 0
    · rw [Polynomial.derivative_rootMultiplicity_of_root hroot]
      have hpos : 0 < h.rootMultiplicity 0 :=
        (Polynomial.rootMultiplicity_pos hh).mpr hroot
      omega
    · rw [Polynomial.rootMultiplicity_eq_zero hroot]
      omega
  · have hXm : Polynomial.rootMultiplicity a (X : K[X]) = 0 := by
      rw [show (X : K[X]) = X - C (0 : K) by simp,
        Polynomial.rootMultiplicity_X_sub_C]
      simp [ha0]
    rw [hXm, zero_add]
    by_cases hroot : h.IsRoot a
    · rw [Polynomial.derivative_rootMultiplicity_of_root hroot]
      have hpos : 0 < h.rootMultiplicity a :=
        (Polynomial.rootMultiplicity_pos hh).mpr hroot
      obtain ⟨e, he⟩ := heven a ha0
      omega
    · rw [Polynomial.rootMultiplicity_eq_zero hroot]
      omega

/-- Combined cleared-identity form of the univariate bridge.  This is the
statement consumed by the squarefree-gap proof after the chain-rule
specialization has identified the weighted Euler derivative with
`X * h.derivative`. -/
theorem dvd_sq_X_mul_derivative_of_X_pow_mul_sq_eq_C_mul_X_pow_mul_sq_mul
    (A B h : K[X]) (u v : ℕ) {c : K}
    (hA : A ≠ 0) (hB : B ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0)
    (hsq : X ^ u * A ^ 2 = C c * X ^ v * B ^ 2 * h) :
    h ∣ (X * h.derivative) ^ 2 :=
  dvd_sq_X_mul_derivative_of_even_nonzero_rootMultiplicity hh
    (even_rootMultiplicity_of_X_pow_mul_sq_eq_C_mul_X_pow_mul_sq_mul
      A B h u v hA hB hh hc hsq)

/-- Combined form without a monomial factor on the left. -/
theorem dvd_sq_X_mul_derivative_of_sq_eq_C_mul_X_pow_mul_sq_mul
    (A B h : K[X]) (v : ℕ) {c : K}
    (hA : A ≠ 0) (hB : B ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0)
    (hsq : A ^ 2 = C c * X ^ v * B ^ 2 * h) :
    h ∣ (X * h.derivative) ^ 2 :=
  dvd_sq_X_mul_derivative_of_even_nonzero_rootMultiplicity hh
    (even_rootMultiplicity_of_sq_eq_C_mul_X_pow_mul_sq_mul
      A B h v hA hB hh hc hsq)

end AlgebraicallyClosed

section ArbitraryCharacteristicZeroField

variable [CharZero K]

/-- Descent form of the Euler-divisibility lemma over an arbitrary
characteristic-zero field.  Its hypothesis states the multiplicity condition
after mapping to the algebraic closure, where it detects every irreducible
factor of `h`, including factors having no root over `K` itself. -/
theorem dvd_sq_X_mul_derivative_of_map_even_nonzero_rootMultiplicity
    {h : K[X]} (hh : h ≠ 0)
    (heven : ∀ a : AlgebraicClosure K, a ≠ 0 →
      Even ((h.map (algebraMap K (AlgebraicClosure K))).rootMultiplicity a)) :
    h ∣ (X * h.derivative) ^ 2 := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hhm : h.map ι ≠ 0 := Polynomial.map_ne_zero (f := ι) hh
  have hdiv : h.map ι ∣
      (X * (h.map ι).derivative) ^ 2 :=
    dvd_sq_X_mul_derivative_of_even_nonzero_rootMultiplicity hhm (by
      simpa only [ι] using heven)
  have hdivMap : h.map ι ∣ ((X * h.derivative) ^ 2).map ι := by
    simpa only [Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.derivative_map] using hdiv
  exact (Polynomial.map_dvd_map' ι).mp hdivMap

/-- The complete cleared-identity bridge over any characteristic-zero field.
The proof maps the identity to the algebraic closure, applies the
root-multiplicity argument there, and descends divisibility along the
injective coefficient map. -/
theorem dvd_sq_X_mul_derivative_of_X_pow_mul_sq_eq_C_mul_X_pow_mul_sq_mul_charZero
    (A B h : K[X]) (u v : ℕ) {c : K}
    (hA : A ≠ 0) (hB : B ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0)
    (hsq : X ^ u * A ^ 2 = C c * X ^ v * B ^ 2 * h) :
    h ∣ (X * h.derivative) ^ 2 := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hAm : A.map ι ≠ 0 := Polynomial.map_ne_zero (f := ι) hA
  have hBm : B.map ι ≠ 0 := Polynomial.map_ne_zero (f := ι) hB
  have hhm : h.map ι ≠ 0 := Polynomial.map_ne_zero (f := ι) hh
  have hcm : ι c ≠ 0 := by
    intro hzero
    apply hc
    apply ι.injective
    simpa using hzero
  have hsqMap : X ^ u * (A.map ι) ^ 2 =
      C (ι c) * X ^ v * (B.map ι) ^ 2 * h.map ι := by
    have := congrArg (fun p : K[X] ↦ p.map ι) hsq
    simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_C] using this
  have hdiv : h.map ι ∣ (X * (h.map ι).derivative) ^ 2 :=
    dvd_sq_X_mul_derivative_of_X_pow_mul_sq_eq_C_mul_X_pow_mul_sq_mul
      (A.map ι) (B.map ι) (h.map ι) u v hAm hBm hhm hcm hsqMap
  have hdivMap : h.map ι ∣ ((X * h.derivative) ^ 2).map ι := by
    simpa only [Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.derivative_map] using hdiv
  exact (Polynomial.map_dvd_map' ι).mp hdivMap

/-- Arbitrary-field version with no monomial factor on the left. -/
theorem dvd_sq_X_mul_derivative_of_sq_eq_C_mul_X_pow_mul_sq_mul_charZero
    (A B h : K[X]) (v : ℕ) {c : K}
    (hA : A ≠ 0) (hB : B ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0)
    (hsq : A ^ 2 = C c * X ^ v * B ^ 2 * h) :
    h ∣ (X * h.derivative) ^ 2 := by
  simpa using
    dvd_sq_X_mul_derivative_of_X_pow_mul_sq_eq_C_mul_X_pow_mul_sq_mul_charZero
      A B h 0 v hA hB hh hc (by simpa using hsq)

end ArbitraryCharacteristicZeroField

end

end Erdos485
