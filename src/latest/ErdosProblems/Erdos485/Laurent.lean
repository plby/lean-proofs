import Mathlib.Algebra.Polynomial.Laurent

/-!
# Laurent-polynomial support and square descent for Erdős Problem 485

This file isolates the elementary bookkeeping with integer exponents used in
the Laurent-polynomial part of the proof.  In particular, it records that
multiplication by a nonzero scalar monomial merely translates support, gives
an exact formula for the least exponent of a product, and compares square
roots across a scalar Laurent monomial.
-/

namespace Erdos485

open LaurentPolynomial
open scoped LaurentPolynomial

noncomputable section

section Support

variable {K : Type*} [Field K]

/-- Multiplication by a nonzero scalar Laurent monomial translates support. -/
theorem support_C_mul_T_mul (f : K[T;T⁻¹]) {c : K} (hc : c ≠ 0) (r : ℤ) :
    (C c * T r * f).coeff.support =
      f.coeff.support.map (addLeftEmbedding r) := by
  rw [← single_eq_C_mul_T]
  exact AddMonoidAlgebra.support_coeff_single_mul f c
    (fun y ↦ by simp [hc]) r

/-- A nonzero scalar Laurent monomial does not change the number of terms. -/
theorem card_support_C_mul_T_mul (f : K[T;T⁻¹]) {c : K} (hc : c ≠ 0) (r : ℤ) :
    (C c * T r * f).coeff.support.card = f.coeff.support.card := by
  rw [support_C_mul_T_mul f hc r, Finset.card_map]

/-- In particular, multiplication by a Laurent power preserves term count. -/
theorem card_support_T_mul (f : K[T;T⁻¹]) (r : ℤ) :
    (T r * f).coeff.support.card = f.coeff.support.card := by
  simpa only [map_one, one_mul] using
    card_support_C_mul_T_mul f (one_ne_zero : (1 : K) ≠ 0) r

end Support

section LeastExponent

variable {K : Type*} [Field K]

/-- The least exponent occurring in a nonzero Laurent polynomial. -/
def leastExponent (f : K[T;T⁻¹]) (hf : f ≠ 0) : ℤ :=
  f.coeff.support.min' (by
    rw [Finsupp.support_nonempty_iff]
    simpa only [ne_eq, AddMonoidAlgebra.coeff_eq_zero] using hf)

/-- The least exponent of a product is the sum of the least exponents. -/
theorem leastExponent_mul (f g : K[T;T⁻¹]) (hf : f ≠ 0) (hg : g ≠ 0) :
    leastExponent (f * g) (mul_ne_zero hf hg) =
      leastExponent f hf + leastExponent g hg := by
  let a := leastExponent f hf
  let b := leastExponent g hg
  have hfa : a ∈ f.coeff.support := by
    exact Finset.min'_mem _ _
  have hgb : b ∈ g.coeff.support := by
    exact Finset.min'_mem _ _
  have hamin : ∀ x ∈ f.coeff.support, a ≤ x := by
    intro x hx
    exact Finset.min'_le _ x hx
  have hbmin : ∀ y ∈ g.coeff.support, b ≤ y := by
    intro y hy
    exact Finset.min'_le _ y hy
  have hunique : UniqueAdd f.coeff.support g.coeff.support a b := by
    intro x y hx hy hxy
    have hax := hamin x hx
    have hby := hbmin y hy
    omega
  have habcoeff : (f * g).coeff (a + b) = f.coeff a * g.coeff b :=
    AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hunique
  have habmem : a + b ∈ (f * g).coeff.support := by
    rw [Finsupp.mem_support_iff, habcoeff]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp hfa) (Finsupp.mem_support_iff.mp hgb)
  apply le_antisymm
  · exact Finset.min'_le _ (a + b) habmem
  · apply Finset.le_min'
    intro z hz
    have hz' := AddMonoidAlgebra.support_coeff_mul_subset f g hz
    simp only [Finset.mem_add] at hz'
    obtain ⟨x, hx, y, hy, rfl⟩ := hz'
    exact add_le_add (hamin x hx) (hbmin y hy)

/-- The coefficient at the least exponent of a nonzero Laurent polynomial. -/
def leastCoeff (f : K[T;T⁻¹]) (hf : f ≠ 0) : K :=
  f.coeff (leastExponent f hf)

/-- The least coefficient is nonzero. -/
theorem leastCoeff_ne_zero (f : K[T;T⁻¹]) (hf : f ≠ 0) :
    leastCoeff f hf ≠ 0 := by
  unfold leastCoeff
  apply Finsupp.mem_support_iff.mp
  exact Finset.min'_mem _ _

/-- The coefficient at the least exponent of a product is the product of the
two least coefficients. -/
theorem leastCoeff_mul (f g : K[T;T⁻¹]) (hf : f ≠ 0) (hg : g ≠ 0) :
    leastCoeff (f * g) (mul_ne_zero hf hg) = leastCoeff f hf * leastCoeff g hg := by
  let a := leastExponent f hf
  let b := leastExponent g hg
  have hamin : ∀ x ∈ f.coeff.support, a ≤ x := by
    intro x hx
    exact Finset.min'_le _ x hx
  have hbmin : ∀ y ∈ g.coeff.support, b ≤ y := by
    intro y hy
    exact Finset.min'_le _ y hy
  have hunique : UniqueAdd f.coeff.support g.coeff.support a b := by
    intro x y hx hy hxy
    have hax := hamin x hx
    have hby := hbmin y hy
    omega
  unfold leastCoeff
  rw [leastExponent_mul f g hf hg]
  exact AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hunique

/-- The least exponent of a nonzero scalar Laurent monomial is its monomial
exponent. -/
theorem leastExponent_C_mul_T {c : K} (hc : c ≠ 0) (r : ℤ) :
    leastExponent (C c * T r)
      (mul_ne_zero ((map_ne_zero C).2 hc) (isUnit_T r).ne_zero) = r := by
  have hsupp := support_C_mul_T_mul (1 : K[T;T⁻¹]) hc r
  simp only [mul_one] at hsupp
  have hsupp' : (C c * T r).coeff.support = {r} := by
    simpa using hsupp
  unfold leastExponent
  simpa only [hsupp', Finset.min'_singleton]

/-- The least coefficient of a nonzero scalar Laurent monomial is its scalar. -/
theorem leastCoeff_C_mul_T {c : K} (hc : c ≠ 0) (r : ℤ) :
    leastCoeff (C c * T r)
      (mul_ne_zero ((map_ne_zero C).2 hc) (isUnit_T r).ne_zero) = c := by
  unfold leastCoeff
  rw [leastExponent_C_mul_T hc r]
  calc
    (C c * T r).coeff r = (AddMonoidAlgebra.single r c : K[T;T⁻¹]).coeff r :=
      congrArg (fun F : K[T;T⁻¹] ↦ F.coeff r) (single_eq_C_mul_T c r).symm
    _ = c := Finsupp.single_eq_same

/-- Translating by a nonzero scalar Laurent monomial adds its exponent to the
least exponent. -/
theorem leastExponent_C_mul_T_mul (f : K[T;T⁻¹]) (hf : f ≠ 0)
    {c : K} (hc : c ≠ 0) (r : ℤ) :
    leastExponent (C c * T r * f)
      (mul_ne_zero (mul_ne_zero ((map_ne_zero C).2 hc) (isUnit_T r).ne_zero) hf) =
      r + leastExponent f hf := by
  have hmono : C c * T r ≠ (0 : K[T;T⁻¹]) :=
    mul_ne_zero ((map_ne_zero C).2 hc) (isUnit_T r).ne_zero
  calc
    leastExponent (C c * T r * f) _ =
        leastExponent (C c * T r) hmono + leastExponent f hf :=
      leastExponent_mul (C c * T r) f hmono hf
    _ = r + leastExponent f hf := by rw [leastExponent_C_mul_T hc r]

/-- Equality of nonzero Laurent polynomials preserves their least exponent. -/
theorem leastExponent_eq_of_eq {f g : K[T;T⁻¹]} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : f = g) : leastExponent f hf = leastExponent g hg := by
  subst g
  rfl

/-- Equality of nonzero Laurent polynomials preserves their least
coefficient. -/
theorem leastCoeff_eq_of_eq {f g : K[T;T⁻¹]} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : f = g) : leastCoeff f hf = leastCoeff g hg := by
  subst g
  rfl

/-- The valuation comparison used in the square-root argument: if two
squares differ by a nonzero scalar monomial of exponent `r`, their least
exponents satisfy `2ℓ(A) = r + 2ℓ(B)`. -/
theorem twice_leastExponent_eq_of_sq_eq_C_mul_T_mul_sq
    (A B : K[T;T⁻¹]) (hA : A ≠ 0) (hB : B ≠ 0)
    {c : K} (hc : c ≠ 0) (r : ℤ)
    (h : A ^ 2 = C c * T r * B ^ 2) :
    leastExponent A hA + leastExponent A hA =
      r + (leastExponent B hB + leastExponent B hB) := by
  have hA2 : A ^ 2 ≠ 0 := pow_ne_zero _ hA
  have hB2 : B ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hmono : C c * T r ≠ (0 : K[T;T⁻¹]) :=
    mul_ne_zero ((map_ne_zero C).2 hc) (isUnit_T r).ne_zero
  have hrhs : C c * T r * B ^ 2 ≠ (0 : K[T;T⁻¹]) :=
    mul_ne_zero hmono hB2
  have he := leastExponent_eq_of_eq hA2 hrhs h
  calc
    leastExponent A hA + leastExponent A hA = leastExponent (A ^ 2) hA2 := by
      simpa only [pow_two] using (leastExponent_mul A A hA hA).symm
    _ = leastExponent (C c * T r * B ^ 2) hrhs := he
    _ = r + leastExponent (B ^ 2) hB2 := by
      exact leastExponent_C_mul_T_mul (B ^ 2) hB2 hc r
    _ = r + (leastExponent B hB + leastExponent B hB) := by
      congr 1
      simpa only [pow_two] using leastExponent_mul B B hB hB

end LeastExponent

section SquareRoot

variable {K : Type*} [Field K]

/-- If two nonzero Laurent-polynomial squares differ by a nonzero scalar
monomial, its exponent is even and the roots differ by a scalar monomial.

The scalar is nonzero.  This is the precise Laurent cancellation statement
used after specializing the bivariate identity in the proof of Problem 485.
-/
theorem eq_C_mul_T_mul_of_sq_eq_C_mul_T_mul_sq
    (A B : K[T;T⁻¹]) (hA : A ≠ 0) (hB : B ≠ 0)
    {c : K} (hc : c ≠ 0) (r : ℤ)
    (h : A ^ 2 = C c * T r * B ^ 2) :
    ∃ s : ℤ, ∃ u : K, r = s + s ∧ u ≠ 0 ∧ A = C u * T s * B := by
  have hval := twice_leastExponent_eq_of_sq_eq_C_mul_T_mul_sq A B hA hB hc r h
  let s : ℤ := leastExponent A hA - leastExponent B hB
  have hrs : r = s + s := by
    dsimp [s]
    omega
  have hA2 : A ^ 2 ≠ 0 := pow_ne_zero _ hA
  have hB2 : B ^ 2 ≠ 0 := pow_ne_zero _ hB
  have hmono : C c * T r ≠ (0 : K[T;T⁻¹]) :=
    mul_ne_zero ((map_ne_zero C).2 hc) (isUnit_T r).ne_zero
  have hrhs : C c * T r * B ^ 2 ≠ (0 : K[T;T⁻¹]) :=
    mul_ne_zero hmono hB2
  have hcoeff :
      leastCoeff A hA * leastCoeff A hA =
        c * (leastCoeff B hB * leastCoeff B hB) := by
    calc
      leastCoeff A hA * leastCoeff A hA = leastCoeff (A ^ 2) hA2 := by
        simpa only [pow_two] using (leastCoeff_mul A A hA hA).symm
      _ = leastCoeff (C c * T r * B ^ 2) hrhs :=
        leastCoeff_eq_of_eq hA2 hrhs h
      _ = leastCoeff (C c * T r) hmono * leastCoeff (B ^ 2) hB2 :=
        leastCoeff_mul (C c * T r) (B ^ 2) hmono hB2
      _ = c * leastCoeff (B ^ 2) hB2 := by rw [leastCoeff_C_mul_T hc r]
      _ = c * (leastCoeff B hB * leastCoeff B hB) := by
        congr 1
        simpa only [pow_two] using leastCoeff_mul B B hB hB
  let u : K := leastCoeff A hA / leastCoeff B hB
  have hu0 : u ≠ 0 := by
    exact div_ne_zero (leastCoeff_ne_zero A hA) (leastCoeff_ne_zero B hB)
  have huSq : u ^ 2 = c := by
    dsimp [u]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 (leastCoeff_ne_zero B hB))).2
    simpa only [pow_two] using hcoeff
  let D : K[T;T⁻¹] := C u * T s * B
  have hsq : A ^ 2 = D ^ 2 := by
    rw [h]
    dsimp [D]
    rw [hrs, T_add]
    rw [← huSq, map_pow]
    ring
  rcases eq_or_eq_neg_of_sq_eq_sq A D hsq with hAD | hAD
  · exact ⟨s, u, hrs, hu0, hAD⟩
  · refine ⟨s, -u, hrs, neg_ne_zero.mpr hu0, ?_⟩
    rw [hAD]
    dsimp [D]
    simp only [map_neg]
    ring

end SquareRoot

section OrdinaryNormalization

open Polynomial

variable {K : Type*} [Field K]

private theorem toLaurent_trunc_of_nonnegative_support (F : K[T;T⁻¹])
    (hF : ∀ z ∈ F.coeff.support, 0 ≤ z) :
    Polynomial.toLaurent (trunc F) = F := by
  have hrange : (F.coeff.support : Set ℤ) ⊆ Set.range (fun n : ℕ ↦ (n : ℤ)) := by
    intro z hz
    refine ⟨z.toNat, ?_⟩
    exact Int.toNat_of_nonneg (hF z hz)
  apply AddMonoidAlgebra.coeff_injective
  rw [Polynomial.toLaurent_apply]
  change Finsupp.mapDomain (fun n : ℕ ↦ (n : ℤ))
      (Finsupp.comapDomain (fun n : ℕ ↦ (n : ℤ)) F.coeff
        Nat.cast_injective.injOn) = F.coeff
  exact Finsupp.mapDomain_comapDomain _ Nat.cast_injective F.coeff hrange

/-- Shift a nonzero Laurent polynomial by the negative of its least exponent.
The result is the Laurent image of an ordinary polynomial, whose constant
coefficient is nonzero and whose number of terms is unchanged. -/
theorem exists_polynomial_normalization (f : K[T;T⁻¹]) (hf : f ≠ 0) :
    ∃ G : K[X],
      G.coeff 0 ≠ 0 ∧
      Polynomial.toLaurent G = T (-leastExponent f hf) * f ∧
      G.support.card = f.coeff.support.card := by
  let ell : ℤ := leastExponent f hf
  let F : K[T;T⁻¹] := T (-ell) * f
  have hF0 : F ≠ 0 := mul_ne_zero (isUnit_T (-ell)).ne_zero hf
  have hsupport : F.coeff.support =
      f.coeff.support.map (addLeftEmbedding (-ell)) := by
    dsimp [F]
    simpa only [map_one, one_mul] using
      support_C_mul_T_mul f (one_ne_zero : (1 : K) ≠ 0) (-ell)
  have hnonnegative : ∀ z ∈ F.coeff.support, 0 ≤ z := by
    intro z hz
    rw [hsupport] at hz
    obtain ⟨x, hx, hxz⟩ := Finset.mem_map.mp hz
    change -ell + x = z at hxz
    have hellx : ell ≤ x := by
      dsimp [ell]
      exact Finset.min'_le _ x hx
    omega
  let G : K[X] := trunc F
  have hto : Polynomial.toLaurent G = F := by
    exact toLaurent_trunc_of_nonnegative_support F hnonnegative
  have hleastF : leastExponent F hF0 = 0 := by
    dsimp [F]
    calc
      leastExponent (T (-ell) * f) _ =
          leastExponent (LaurentPolynomial.C (1 : K) * T (-ell) * f)
            (mul_ne_zero
              (mul_ne_zero ((map_ne_zero LaurentPolynomial.C).2 one_ne_zero)
                (isUnit_T (-ell)).ne_zero) hf) := by
              simp only [map_one, one_mul]
      _ = -ell + leastExponent f hf :=
        leastExponent_C_mul_T_mul f hf one_ne_zero (-ell)
      _ = 0 := by dsimp [ell]; omega
  have hG0 : G.coeff 0 ≠ 0 := by
    have hleastCoeff := leastCoeff_ne_zero F hF0
    unfold leastCoeff at hleastCoeff
    rw [hleastF] at hleastCoeff
    intro hzero
    apply hleastCoeff
    have hcoeff := congrArg (fun H : K[T;T⁻¹] ↦ H.coeff 0) hto
    rw [← hcoeff]
    apply Finsupp.notMem_support_iff.mp
    rw [LaurentPolynomial.support_coeff_toLaurent]
    simpa [Polynomial.mem_support_iff] using hzero
  refine ⟨G, hG0, ?_, ?_⟩
  · simpa [F, ell] using hto
  · calc
      G.support.card = (Polynomial.toLaurent G).coeff.support.card := by
        rw [LaurentPolynomial.support_coeff_toLaurent, Finset.card_map]
      _ = F.coeff.support.card := by rw [hto]
      _ = f.coeff.support.card := by
        dsimp [F]
        exact card_support_T_mul f (-ell)

end OrdinaryNormalization

section PolynomialDescent

open Polynomial

variable {K : Type*} [Field K]

/-- Laurent-support form of the divisibility hypothesis in polynomial square
descent.  It lets callers that have converted a polynomial identity to
Laurent polynomials feed the result to
`square_support_dvd_imp_support_dvd` or its composition-form corollary. -/
theorem square_support_dvd_of_toLaurent_square_support_dvd
    (A : K[X]) (q : ℕ)
    (hSq : ∀ z ∈ (Polynomial.toLaurent (A ^ 2)).coeff.support, (q : ℤ) ∣ z) :
    ∀ n ∈ (A ^ 2).support, q ∣ n := by
  intro n hn
  have hnL : (n : ℤ) ∈ (Polynomial.toLaurent (A ^ 2)).coeff.support := by
    rw [LaurentPolynomial.support_coeff_toLaurent]
    simpa using hn
  exact_mod_cast hSq (n : ℤ) hnL

end PolynomialDescent

end

end Erdos485
