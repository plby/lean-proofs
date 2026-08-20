import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IrelandRosen.Theorem1.EisensteinReciprocity

/-!
# Odd-prime power reciprocity for the Elliott tail

This file is the foundationally clean reciprocity interface used in the odd-prime
exponent case.  The key point is that one does not need a chosen prime ideal
to be principal.  If a primary element `alpha` has

`(alpha) = P * C`,

where `P` is the chosen prime above the rational modulus and `C` is a fixed
ideal-class correction, Eisenstein reciprocity gives

`(alpha / q)_ell = (q / P)_ell + (q / C)_ell`.

Thus `q` is an `ell`-th power at `P` exactly when the integer-denominator
symbol of `alpha` is the fixed correction symbol at `C`.  Once `P` is
identified with the degree-one residue field `ZMod r`, this is exactly the
ordinary statement that `q` is an `ell`-th power modulo the rational prime
`r`.
-/

namespace Erdos980.ElliottTail.OddPowerReciprocity

open scoped NumberField

open BernoulliRegular
open BernoulliRegular.Furtwaengler
open BernoulliRegular.Reflection.ResidueSymbol.PowerResidue

variable {ell : ℕ} [Fact ell.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-- Existence of an `n`-th root is transported by a ring equivalence. -/
theorem exists_pow_eq_iff_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (n : ℕ) (a : R) :
    (∃ x : R, x ^ n = a) ↔ ∃ y : S, y ^ n = e a := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨e x, ?_⟩
    rw [← map_pow, hx]
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    simpa using hy

/-- In a residue field, a nonzero ring element is an `n`-th power iff its
canonically associated unit is an `n`-th power. -/
theorem quotient_exists_pow_iff_unit_exists_pow
    {R : Type*} [CommRing R]
    {P : Ideal R} [P.IsMaximal]
    {a : R} (ha : a ∉ P) {n : ℕ} (hn : n ≠ 0) :
    (∃ x : R ⧸ P, x ^ n = Ideal.Quotient.mk P a) ↔
      ∃ y : (R ⧸ P)ˣ, quotientUnitOfNotMem P a ha = y ^ n := by
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hmk : Ideal.Quotient.mk P a ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact ha
  constructor
  · rintro ⟨x, hx⟩
    have hxne : x ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow hn] at hx
      exact hmk hx.symm
    let y : (R ⧸ P)ˣ := Units.mk0 x hxne
    refine ⟨y, ?_⟩
    apply Units.ext
    simpa [quotientUnitOfNotMem, y] using hx.symm
  · rintro ⟨y, hy⟩
    refine ⟨(y : R ⧸ P), ?_⟩
    have hval := congrArg (fun u : (R ⧸ P)ˣ => (u : R ⧸ P)) hy
    simpa [quotientUnitOfNotMem] using hval.symm

/-- The canonical local symbol depends only on the numerator's residue class
modulo its prime denominator.  This is stated for the total canonical symbol,
so no good-prime hypotheses are needed. -/
theorem primeSymbol_eq_of_sub_mem
    {a b : 𝓞 K} {P : Ideal (𝓞 K)} (hab : a - b ∈ P) :
    pthSymbolAtPrime_canonical (p := ell) (K := K) a P =
      pthSymbolAtPrime_canonical (p := ell) (K := K) b P := by
  have hmem : a ∈ P ↔ b ∈ P := by
    constructor
    · intro ha
      have hb : b = a - (a - b) := by ring
      rw [hb]
      exact P.sub_mem ha hab
    · intro hb
      have ha : a = (a - b) + b := by ring
      rw [ha]
      exact P.add_mem hab hb
  by_cases hbot : P = ⊥
  · subst P
    simp [pthSymbolAtPrime_canonical_eq_zero_of_eq_bot]
  haveI : NeZero P := ⟨hbot⟩
  by_cases hmax : P.IsMaximal
  · letI : P.IsMaximal := hmax
    letI : P.IsPrime := hmax.isPrime
    by_cases ha : a ∈ P
    · have hb : b ∈ P := hmem.mp ha
      rw [pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax ha,
        pthSymbolAtPrime_canonical_eq_zero_of_mem hbot hmax hb]
    · have hb : b ∉ P := fun hbmem => ha (hmem.mpr hbmem)
      by_cases hdiv : ell ∣ Fintype.card (𝓞 K ⧸ P) - 1
      · by_cases hellmem : (ell : 𝓞 K) ∈ P
        · rw [pthSymbolAtPrime_canonical_eq_zero_of_p_mem
              hbot hmax ha hdiv hellmem,
            pthSymbolAtPrime_canonical_eq_zero_of_p_mem
              hbot hmax hb hdiv hellmem]
        · rw [pthSymbolAtPrime_canonical_eq_primeExponent
              hbot hmax ha hdiv hellmem,
            pthSymbolAtPrime_canonical_eq_primeExponent
              hbot hmax hb hdiv hellmem]
          simp only [primeExponent]
          congr 1
          apply Units.ext
          exact Ideal.Quotient.mk_eq_mk_iff_sub_mem a b |>.mpr hab
      · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_dvd hbot hmax ha hdiv,
          pthSymbolAtPrime_canonical_eq_zero_of_not_dvd hbot hmax hb hdiv]
  · rw [pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal a hbot hmax,
      pthSymbolAtPrime_canonical_eq_zero_of_not_isMaximal b hbot hmax]

/-- The ideal-level canonical symbol depends only on the numerator modulo its
ideal denominator. -/
theorem idealSymbol_eq_of_sub_mem
    {a b : 𝓞 K} {I : Ideal (𝓞 K)} (hab : a - b ∈ I) :
    pthSymbolAtIdeal_canonical (p := ell) (K := K) a I =
      pthSymbolAtIdeal_canonical (p := ell) (K := K) b I := by
  simp only [pthSymbolAtIdeal_canonical]
  congr 1
  apply Multiset.map_congr rfl
  intro P hP
  apply primeSymbol_eq_of_sub_mem
  have hle : I ≤ P := by
    rw [← Ideal.dvd_iff_le]
    exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
  exact hle hab

/-- The integer-denominator Eisenstein symbol factors through the finite
residue ring `O_K / (q)`: congruent primary generators give the same symbol.
This is the precise finite residue-class (hence ray-class) restriction used
after reciprocity. -/
theorem integerSymbol_eq_of_sub_mem_rationalIntIdeal
    {a b : 𝓞 K} (q : ℤ)
    (hab : a - b ∈ rationalIntIdeal (K := K) q) :
    pthSymbolAtInt_canonical (p := ell) (K := K) a q =
      pthSymbolAtInt_canonical (p := ell) (K := K) b q := by
  exact idealSymbol_eq_of_sub_mem hab

/-- Quotient-ring formulation of
`integerSymbol_eq_of_sub_mem_rationalIntIdeal`. -/
theorem integerSymbol_eq_of_residue_eq
    {a b : 𝓞 K} (q : ℤ)
    (hab : Ideal.Quotient.mk (rationalIntIdeal (K := K) q) a =
      Ideal.Quotient.mk (rationalIntIdeal (K := K) q) b) :
    pthSymbolAtInt_canonical (p := ell) (K := K) a q =
      pthSymbolAtInt_canonical (p := ell) (K := K) b q := by
  apply integerSymbol_eq_of_sub_mem_rationalIntIdeal q
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mp hab

/-- A nonzero rational integer generates a nonzero ideal in the cyclotomic
ring of integers. -/
theorem rationalIntIdeal_ne_bot_of_ne_zero
    {q : ℤ} (hq : q ≠ 0) :
    rationalIntIdeal (K := K) q ≠ ⊥ := by
  rw [rationalIntIdeal, Ne, Ideal.span_singleton_eq_bot]
  simpa only [map_zero] using
    (FaithfulSMul.algebraMap_injective ℤ (𝓞 K)).ne hq

/-- The residue ring through which the integer symbol factors is finite.
Together with `integerSymbol_eq_of_residue_eq`, this records literally that
only finitely many residue (and therefore ray) classes can occur for each
fixed nonzero test integer. -/
theorem finite_rationalIntResidueRing
    {q : ℤ} (hq : q ≠ 0) :
    Finite (𝓞 K ⧸ rationalIntIdeal (K := K) q) := by
  letI : NeZero (rationalIntIdeal (K := K) q) :=
    ⟨rationalIntIdeal_ne_bot_of_ne_zero hq⟩
  infer_instance

/-- The exact Eisenstein-reciprocity bridge, with an ideal-class correction.

The correction ideal `C` is allowed to depend on the (finite) ideal or ray
class of `P`, but not on the test integer `q`.  The left side is the local
`ell`-th-power condition at `P`; the right side involves the residue of the
primary generator `alpha` modulo the rational ideal `(q)` and the fixed
correction symbol `(q / C)_ell`. -/
theorem localPower_iff_integerSymbol_eq_correction
    (hellOdd : Odd ell)
    {P C : Ideal (𝓞 K)} [hPprime : P.IsPrime] [hPmax : P.IsMaximal]
    (hPne : P ≠ ⊥) (hCne : C ≠ ⊥)
    {alpha : 𝓞 K}
    (halphaPrimary : FLT37.IsPrimary ell (K := K) alpha)
    (halphaPrimeToEll : IsPrimeToP (p := ell) (K := K) alpha)
    (halphaFactor : Ideal.span ({alpha} : Set (𝓞 K)) = P * C)
    {q : ℕ}
    (hqCoprime : IsCoprimeToPAndAlphaInt
      (p := ell) (K := K) (q : ℤ) alpha)
    (hqNotMem : (q : 𝓞 K) ∉ P)
    (hellDvd : ell ∣ Ideal.absNorm P - 1)
    (hellNotMem : (ell : 𝓞 K) ∉ P) :
    (∃ y : (𝓞 K ⧸ P)ˣ,
        quotientUnitOfNotMem P (q : 𝓞 K) hqNotMem = y ^ ell) ↔
      pthSymbolAtInt_canonical (p := ell) (K := K) alpha (q : ℤ) =
        pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K) C := by
  letI : NeZero P := ⟨hPne⟩
  have hellDvd' : ell ∣ Fintype.card (𝓞 K ⧸ P) - 1 := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply,
      ← Ideal.absNorm_apply]
    exact hellDvd
  have hrec :
      pthSymbolAtInt_canonical (p := ell) (K := K) alpha (q : ℤ) =
        pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K)
          (Ideal.span ({alpha} : Set (𝓞 K))) := by
    simpa using
      (IrelandRosen.eisensteinReciprocity_theorem1
        ell hellOdd K (q : ℤ) halphaPrimary halphaPrimeToEll hqCoprime)
  have hprime :
      pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K) P =
        pthSymbolAtPrime_canonical (p := ell) (K := K) (q : 𝓞 K) P :=
    pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical
      (p := ell) (K := K) (q : 𝓞 K) hPne
  have hdecomp :
      pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K)
          (Ideal.span ({alpha} : Set (𝓞 K))) =
        pthSymbolAtPrime_canonical (p := ell) (K := K) (q : 𝓞 K) P +
          pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K) C := by
    rw [halphaFactor,
      pthSymbolAtIdeal_canonical_mul_ideal (p := ell) (K := K)
        (q : 𝓞 K) hPne hCne,
      hprime]
  have hlocal :
      pthSymbolAtPrime_canonical (p := ell) (K := K) (q : 𝓞 K) P = 0 ↔
        ∃ y : (𝓞 K ⧸ P)ˣ,
          quotientUnitOfNotMem P (q : 𝓞 K) hqNotMem = y ^ ell :=
    pthSymbolAtPrime_canonical_eq_zero_iff_residue_isPow
      (p := ell) (K := K) hPne hPmax hqNotMem hellDvd' hellNotMem
  constructor
  · intro hpow
    have hzero := hlocal.mpr hpow
    calc
      pthSymbolAtInt_canonical (p := ell) (K := K) alpha (q : ℤ) =
          pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K)
            (Ideal.span ({alpha} : Set (𝓞 K))) := hrec
      _ = pthSymbolAtPrime_canonical (p := ell) (K := K) (q : 𝓞 K) P +
          pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K) C := hdecomp
      _ = pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K) C := by
        rw [hzero, zero_add]
  · intro heq
    have hadd :
        pthSymbolAtPrime_canonical (p := ell) (K := K) (q : 𝓞 K) P +
            pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K) C =
          0 + pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K) C := by
      rw [zero_add]
      calc
        _ = pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K)
              (Ideal.span ({alpha} : Set (𝓞 K))) := hdecomp.symm
        _ = pthSymbolAtInt_canonical (p := ell) (K := K) alpha (q : ℤ) := hrec.symm
        _ = _ := heq
    have hzero :
        pthSymbolAtPrime_canonical (p := ell) (K := K) (q : 𝓞 K) P = 0 :=
      add_right_cancel hadd
    exact hlocal.mp hzero

/-- Rational-prime form of `localPower_iff_integerSymbol_eq_correction`.

The explicit residue-field equivalence is the data saying that the chosen
prime `P` has degree one over the rational prime `r`.  Consequently the left
side is literally the ordinary congruence condition in `ZMod r`, rather than
an isomorphic local-field reformulation. -/
theorem zmodPower_iff_integerSymbol_eq_correction
    (hellOdd : Odd ell)
    {r q : ℕ}
    {P C : Ideal (𝓞 K)} [hPprime : P.IsPrime] [hPmax : P.IsMaximal]
    (hPne : P ≠ ⊥) (hCne : C ≠ ⊥)
    (residueEquiv : ZMod r ≃+* (𝓞 K ⧸ P))
    {alpha : 𝓞 K}
    (halphaPrimary : FLT37.IsPrimary ell (K := K) alpha)
    (halphaPrimeToEll : IsPrimeToP (p := ell) (K := K) alpha)
    (halphaFactor : Ideal.span ({alpha} : Set (𝓞 K)) = P * C)
    (hqCoprime : IsCoprimeToPAndAlphaInt
      (p := ell) (K := K) (q : ℤ) alpha)
    (hqNotMem : (q : 𝓞 K) ∉ P)
    (hellDvd : ell ∣ Ideal.absNorm P - 1)
    (hellNotMem : (ell : 𝓞 K) ∉ P) :
    (∃ b : ZMod r, b ^ ell = (q : ZMod r)) ↔
      pthSymbolAtInt_canonical (p := ell) (K := K) alpha (q : ℤ) =
        pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K) C := by
  have hellNe : ell ≠ 0 := (Fact.out : ell.Prime).ne_zero
  have hmap :
      residueEquiv (q : ZMod r) = Ideal.Quotient.mk P (q : 𝓞 K) := by
    simp
  calc
    (∃ b : ZMod r, b ^ ell = (q : ZMod r)) ↔
        ∃ x : 𝓞 K ⧸ P, x ^ ell = residueEquiv (q : ZMod r) :=
      exists_pow_eq_iff_ringEquiv residueEquiv ell (q : ZMod r)
    _ ↔ ∃ x : 𝓞 K ⧸ P, x ^ ell = Ideal.Quotient.mk P (q : 𝓞 K) := by
      rw [hmap]
    _ ↔ ∃ y : (𝓞 K ⧸ P)ˣ,
        quotientUnitOfNotMem P (q : 𝓞 K) hqNotMem = y ^ ell :=
      quotient_exists_pow_iff_unit_exists_pow hqNotMem hellNe
    _ ↔ _ := localPower_iff_integerSymbol_eq_correction
      hellOdd hPne hCne halphaPrimary halphaPrimeToEll halphaFactor
      hqCoprime hqNotMem hellDvd hellNotMem

end Erdos980.ElliottTail.OddPowerReciprocity
