import ErdosProblems.Erdos980.ElliottTail.Definitions
import ErdosProblems.Erdos980.ElliottTail.OddPrimeTensorBridge
import ErdosProblems.Erdos980.ElliottTail.OddSymbolCollision
import ErdosProblems.Erdos980.ElliottTail.RayPrincipalizationHeight
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# The rational-prime to ray-generator encoding for the odd medium range

This file supplies the literal arithmetic encoding which precedes the
number-field sieve in Elliott's odd-prime argument.  An exceptional rational
prime is lifted, by Going Up, to a prime ideal in the cyclotomic field.  Its
inertia degree is one (eligibility says that the rational prime is `1` modulo
the exponent), hence its ideal norm is the original rational prime.  Finite
ray principalization with archimedean control then attaches a primary
generator and a member of the fixed finite correction family.

The final results record two points which are important for counting:

* every auxiliary integer below the exceptional cutoff is an `ell`-th power
  modulo the rational conductor;
* the map from exceptional rational primes to pairs `(correction, generator)`
  is injective.  Thus passing to corrected generators loses no cardinality.
-/

open scoped NumberField nonZeroDivisors BigOperators

namespace Erdos980.ElliottTail.OddMediumRayEncoding

noncomputable section

open BernoulliRegular
open BernoulliRegular.Furtwaengler
open NumberField
open NumberFieldLargerSieve
open OddPowerReciprocity
open OddPrimeTensorBridge
open OddSymbolCollision
open RayPrincipalization
open RayPrincipalizationHeight

variable (ell : ℕ) [Fact ell.Prime]
  (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

local notation "lambdaIdeal" =>
  Ideal.span ({FLT37.zetaSubOne ell K} : Set (𝓞 K))

/-! ## A canonical degree-one prime above an eligible rational prime -/

/-- The rational prime ideal `(p)` in `ℤ`. -/
def integerPrimeIdeal (p : ℕ) : Ideal ℤ :=
  Ideal.span ({(p : ℤ)} : Set ℤ)

theorem integerPrimeIdeal_isPrime {p : ℕ} (hp : p.Prime) :
    (integerPrimeIdeal p).IsPrime := by
  rw [integerPrimeIdeal]
  exact (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)

/-- A fixed prime of the cyclotomic integer ring above `(p)`. -/
noncomputable def primeIdealAbove (p : ℕ) (hp : p.Prime) : Ideal (𝓞 K) := by
  letI : (integerPrimeIdeal p).IsPrime := integerPrimeIdeal_isPrime hp
  exact (Classical.choice (integerPrimeIdeal p).nonempty_primesOver).1

theorem primeIdealAbove_isPrime (p : ℕ) (hp : p.Prime) :
    (primeIdealAbove K p hp).IsPrime := by
  letI : (integerPrimeIdeal p).IsPrime := integerPrimeIdeal_isPrime hp
  exact (Classical.choice (integerPrimeIdeal p).nonempty_primesOver).2.1

theorem primeIdealAbove_liesOver (p : ℕ) (hp : p.Prime) :
    (primeIdealAbove K p hp).LiesOver (integerPrimeIdeal p) := by
  letI : (integerPrimeIdeal p).IsPrime := integerPrimeIdeal_isPrime hp
  exact (Classical.choice (integerPrimeIdeal p).nonempty_primesOver).2.2

theorem not_dvd_exponent_of_eligible {p : ℕ} (hp : Eligible ell p) :
    ¬ p ∣ ell := by
  intro hdiv
  have hpeq : p = ell :=
    (Nat.prime_dvd_prime_iff_eq hp.1 (Fact.out : ell.Prime)).mp hdiv
  subst p
  have hmod := hp.2
  simpa [Nat.ModEq, (Fact.out : ell.Prime).ne_zero,
    Nat.mod_eq_of_lt (Fact.out : ell.Prime).one_lt] using hmod

theorem primeIdealAbove_inertiaDeg_eq_one {p : ℕ}
    (hp : Eligible ell p) :
    (primeIdealAbove K p hp.1).inertiaDeg ℤ = 1 := by
  let P := primeIdealAbove K p hp.1
  letI : P.IsPrime := primeIdealAbove_isPrime K p hp.1
  letI : Fact p.Prime := ⟨hp.1⟩
  letI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [integerPrimeIdeal] using
      primeIdealAbove_liesOver K p hp.1
  have hcast : (p : ZMod ell) = 1 := by
    simpa only [Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff p 1 ell).mpr hp.2
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
    (p := p) (K := K) P (not_dvd_exponent_of_eligible ell hp),
    hcast, orderOf_one]

theorem absNorm_primeIdealAbove {p : ℕ} (hp : Eligible ell p) :
    Ideal.absNorm (primeIdealAbove K p hp.1) = p := by
  let P := primeIdealAbove K p hp.1
  letI : P.IsPrime := primeIdealAbove_isPrime K p hp.1
  letI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [integerPrimeIdeal] using
      primeIdealAbove_liesOver K p hp.1
  have hpow := Ideal.pow_inertiaDeg p P
  rw [primeIdealAbove_inertiaDeg_eq_one ell K hp, pow_one] at hpow
  exact hpow.symm

theorem primeIdealAbove_ne_bot {p : ℕ} (hp : Eligible ell p) :
    primeIdealAbove K p hp.1 ≠ ⊥ := by
  intro hbot
  have hnorm := absNorm_primeIdealAbove ell K hp
  rw [hbot, Ideal.absNorm_bot] at hnorm
  exact hp.1.ne_zero hnorm.symm

/-- The residue field of the selected degree-one prime is canonically a
copy of `ZMod p`. -/
noncomputable def primeIdealAboveResidueEquiv {p : ℕ}
    (hp : Eligible ell p) :
    ZMod p ≃+* (𝓞 K ⧸ primeIdealAbove K p hp.1) := by
  let P := primeIdealAbove K p hp.1
  letI : Fact p.Prime := ⟨hp.1⟩
  letI : P.IsMaximal :=
    (primeIdealAbove_isPrime K p hp.1).isMaximal
      (primeIdealAbove_ne_bot ell K hp)
  letI : P.IsPrime := primeIdealAbove_isPrime K p hp.1
  letI : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
    simpa [integerPrimeIdeal] using primeIdealAbove_liesOver K p hp.1
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Finite (𝓞 K ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (primeIdealAbove_ne_bot ell K hp)
  have hp_mem_base : (p : ℤ) ∈ Ideal.span ({(p : ℤ)} : Set ℤ) :=
    Ideal.subset_span (by simp)
  have hp_mem : (p : 𝓞 K) ∈ P := by
    simpa using ((Ideal.mem_of_liesOver (P := P)
      (p := Ideal.span ({(p : ℤ)} : Set ℤ)) (p : ℤ)).mp hp_mem_base)
  have hp_zero : (p : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hp_mem
  letI : CharP (𝓞 K ⧸ P) p :=
    (CharP.charP_iff_prime_eq_zero hp.1).2 hp_zero
  let i : ZMod p →+* (𝓞 K ⧸ P) := ZMod.castHom dvd_rfl _
  have hcard : Nat.card (𝓞 K ⧸ P) = p := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact absNorm_primeIdealAbove ell K hp
  have hi_bij : Function.Bijective i :=
    (Nat.bijective_iff_injective_and_card i).2
      ⟨i.injective, by rw [Nat.card_zmod, hcard]⟩
  exact RingEquiv.ofBijective i hi_bij

@[simp] theorem primeIdealAboveResidueEquiv_intCast {p : ℕ}
    (hp : Eligible ell p) (q : ℤ) :
    primeIdealAboveResidueEquiv ell K hp (q : ZMod p) =
      Ideal.Quotient.mk (primeIdealAbove K p hp.1) (q : 𝓞 K) := by
  simp [primeIdealAboveResidueEquiv]

/-- The chosen degree-one prime, packaged as a nonzero ideal. -/
noncomputable def nonzeroPrimeIdealAbove {p : ℕ} (hp : Eligible ell p) :
    (Ideal (𝓞 K))⁰ :=
  ⟨primeIdealAbove K p hp.1, by
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    change primeIdealAbove K p hp.1 ≠ ⊥
    exact primeIdealAbove_ne_bot ell K hp⟩

theorem nonzeroPrimeIdealAbove_isPrime {p : ℕ} (hp : Eligible ell p) :
    ((nonzeroPrimeIdealAbove ell K hp : (Ideal (𝓞 K))⁰) :
      Ideal (𝓞 K)).IsPrime :=
  primeIdealAbove_isPrime K p hp.1

theorem nonzeroPrimeIdealAbove_isMaximal {p : ℕ} (hp : Eligible ell p) :
    ((nonzeroPrimeIdealAbove ell K hp : (Ideal (𝓞 K))⁰) :
      Ideal (𝓞 K)).IsMaximal :=
  (nonzeroPrimeIdealAbove_isPrime ell K hp).isMaximal
    (primeIdealAbove_ne_bot ell K hp)

theorem lambdaIdeal_ne_bot : lambdaIdeal ≠ ⊥ := by
  intro h
  exact FLT37.zetaSubOne_ne_zero ell K
    (Ideal.span_singleton_eq_bot.mp h)

private theorem primaryRayModulus_ne_bot :
    lambdaIdeal ^ (2 * ell) ≠ ⊥ :=
  pow_ne_zero _ (lambdaIdeal_ne_bot ell K)

noncomputable local instance :
    Finite (𝓞 K ⧸ lambdaIdeal ^ (2 * ell)) :=
  Ring.HasFiniteQuotients.finiteQuotient
    (primaryRayModulus_ne_bot ell K)

noncomputable local instance :
    Fintype (𝓞 K ⧸ lambdaIdeal ^ (2 * ell)) :=
  Fintype.ofFinite _

noncomputable local instance :
    Fintype (CyclotomicRayCorrectionIndex ell K) :=
  Fintype.ofFinite _

noncomputable local instance : DecidableEq (𝓞 K) := Classical.decEq _

theorem absNorm_lambdaIdeal (hodd : Odd ell) :
    Ideal.absNorm lambdaIdeal = ell := by
  have hell2 : ell ≠ 2 := by
    rintro rfl
    rcases hodd with ⟨k, hk⟩
    omega
  rw [Ideal.absNorm_span_singleton,
    FLT37.zetaSubOne_norm_int ell K hell2]
  simp

theorem lambda_coprime_primeIdealAbove {p : ℕ} (hp : Eligible ell p)
    (hodd : Odd ell) :
    lambdaIdeal ⊔ primeIdealAbove K p hp.1 = ⊤ := by
  let P := primeIdealAbove K p hp.1
  have hne : lambdaIdeal ≠ P := by
    intro heq
    have hn := congrArg Ideal.absNorm heq
    rw [absNorm_lambdaIdeal ell K hodd,
      absNorm_primeIdealAbove ell K hp] at hn
    exact (not_dvd_exponent_of_eligible ell hp) (hn ▸ dvd_rfl)
  have hLmax :
      (Ideal.span ({FLT37.zetaSubOne ell K} : Set (𝓞 K))).IsMaximal :=
    (Ideal.isPrime_of_prime
      (Ideal.prime_span_singleton_iff.mpr
        (FLT37.zetaSubOne_prime ell K))).isMaximal
      (lambdaIdeal_ne_bot ell K)
  letI : (Ideal.span
      ({FLT37.zetaSubOne ell K} : Set (𝓞 K))).IsMaximal := hLmax
  letI : P.IsMaximal := nonzeroPrimeIdealAbove_isMaximal ell K hp
  exact Ideal.isCoprime_iff_sup_eq.mp
    (Ideal.isCoprime_of_isMaximal hne)

/-! ## The exact exceptional-prime source -/

/-- Exceptional rational primes, as a finite subtype. -/
abbrev ExceptionalPrime (t x : ℕ) := ↑(exceptionalPrimes ell t x)

theorem exceptionalPrime_eligible (t x : ℕ)
    (p : ExceptionalPrime ell t x) : Eligible ell p.1 :=
  eligible_of_mem_exceptionalPrimes (Fact.out : ell.Prime).two_le p.2

/-- The degree-one prime ideal attached to an exceptional rational prime. -/
noncomputable def exceptionalPrimeIdeal (t x : ℕ)
    (p : ExceptionalPrime ell t x) : (Ideal (𝓞 K))⁰ :=
  nonzeroPrimeIdealAbove ell K (exceptionalPrime_eligible ell t x p)

theorem exceptionalPrimeIdeal_absNorm (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    Ideal.absNorm (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)) = p.1 :=
  absNorm_primeIdealAbove ell K (exceptionalPrime_eligible ell t x p)

theorem exceptionalPrimeIdeal_isPrime (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)).IsPrime :=
  nonzeroPrimeIdealAbove_isPrime ell K (exceptionalPrime_eligible ell t x p)

theorem exceptionalPrimeIdeal_isMaximal (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)).IsMaximal :=
  nonzeroPrimeIdealAbove_isMaximal ell K (exceptionalPrime_eligible ell t x p)

/-- Degree-one residue equivalence for an exceptional conductor. -/
noncomputable def exceptionalPrimeResidueEquiv (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    ZMod p.1 ≃+*
      (𝓞 K ⧸ (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K))) :=
  primeIdealAboveResidueEquiv ell K
    (exceptionalPrime_eligible ell t x p)

@[simp] theorem exceptionalPrimeResidueEquiv_intCast (t x : ℕ)
    (p : ExceptionalPrime ell t x) (q : ℤ) :
    exceptionalPrimeResidueEquiv ell K t x p (q : ZMod p.1) =
      Ideal.Quotient.mk
        (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)) (q : 𝓞 K) := by
  change primeIdealAboveResidueEquiv ell K
      (exceptionalPrime_eligible ell t x p) (q : ZMod p.1) =
    Ideal.Quotient.mk
      (primeIdealAbove K p.1 (exceptionalPrime_eligible ell t x p).1)
      (q : 𝓞 K)
  exact primeIdealAboveResidueEquiv_intCast ell K
    (exceptionalPrime_eligible ell t x p) q

theorem exceptionalPrimeIdeal_coprime_lambda (hodd : Odd ell)
    (t x : ℕ) (p : ExceptionalPrime ell t x) :
    lambdaIdeal ⊔ (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)) = ⊤ :=
  lambda_coprime_primeIdealAbove ell K
    (exceptionalPrime_eligible ell t x p) hodd

/-! ## Auxiliary local powers forced by exceptionality -/

/-- Every natural number at most the exceptional cutoff is an `ell`-th
power modulo an exceptional conductor.  The case `q = 0` is separated so
that the unit condition in the definition of a nonresidue is used only when
it is valid. -/
theorem exists_auxiliaryPow_of_le_cutoff (t x : ℕ)
    (p : ExceptionalPrime ell t x) (q : ℕ) (hqt : q ≤ t) :
    ∃ b : ZMod p.1, b ^ ell = (q : ZMod p.1) := by
  classical
  by_cases hq0 : q = 0
  · subst q
    exact ⟨0, by simp [(Fact.out : ell.Prime).ne_zero]⟩
  have helig := exceptionalPrime_eligible ell t x p
  have hpMem := mem_exceptionalPrimes.mp p.2
  have hqleast : q < leastKthPowerNonresidue ell p.1 :=
    hqt.trans_lt hpMem.2.2
  have hleastp : leastKthPowerNonresidue ell p.1 < p.1 :=
    leastKthPowerNonresidue_lt (Fact.out : ell.Prime).two_le helig
  have hqp : q < p.1 := hqleast.trans hleastp
  have hpdvd : ¬ p.1 ∣ q :=
    Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hq0) hqp
  have hcop : q.Coprime p.1 :=
    Nat.coprime_comm.mp (helig.1.coprime_iff_not_dvd.mpr hpdvd)
  have hunit : IsUnit (q : ZMod p.1) :=
    (ZMod.isUnit_iff_coprime q p.1).mpr hcop
  have hnot := not_kthPowerNonresidue_of_lt_least
    (Fact.out : ell.Prime).two_le helig hqleast
  by_contra hpow
  exact hnot ⟨hunit, hpow⟩

/-- Finite-family form of `exists_auxiliaryPow_of_le_cutoff`, stated in
the exact candidate API used by the odd tensor bridge. -/
theorem exceptionalPrimes_subset_simultaneousLocalPowerCandidates
    {Q : Type*} [Fintype Q] (q : Q → ℕ) (hq : ∀ s, q s ≤ t) :
    (Finset.univ : Finset (ExceptionalPrime ell t x)) ⊆
      simultaneousLocalPowerCandidates ell Finset.univ
        (fun p : ExceptionalPrime ell t x ↦ p.1) q := by
  classical
  intro p hp
  rw [mem_simultaneousLocalPowerCandidates]
  exact ⟨hp, fun s ↦ exists_auxiliaryPow_of_le_cutoff ell t x p (q s) (hq s)⟩

/-! ## Height-controlled primary generators -/

/-- One uniform archimedean constant for all corrected generators in the
fixed cyclotomic field. -/
noncomputable def rayHeightConstant : ℝ :=
  Classical.choose
    (exists_primary_generator_mul_cyclotomicRayCorrection_height ell K)

theorem rayHeightConstant_spec :
    0 < rayHeightConstant ell K ∧
      ∀ (P : (Ideal (𝓞 K))⁰),
        lambdaIdeal ⊔ (P : Ideal (𝓞 K)) = ⊤ →
        ∃ (i : CyclotomicRayCorrectionIndex ell K) (a : 𝓞 K),
          FLT37.IsPrimary ell (K := K) a ∧
          IsPrimeToP (p := ell) (K := K) a ∧
          Ideal.span {a} = (P : Ideal (𝓞 K)) *
            cyclotomicRayCorrection ell K i ∧
          ∀ φ : K →+* ℂ,
            ‖φ (a : K)‖ ≤ rayHeightConstant ell K *
              (Ideal.absNorm (P : Ideal (𝓞 K)) : ℝ) ^
                ((Module.finrank ℚ K : ℝ)⁻¹) :=
  Classical.choose_spec
    (exists_primary_generator_mul_cyclotomicRayCorrection_height ell K)

theorem exists_exceptionalHeightGenerator (hodd : Odd ell)
    (t x : ℕ) (p : ExceptionalPrime ell t x) :
    ∃ (i : CyclotomicRayCorrectionIndex ell K) (a : 𝓞 K),
      FLT37.IsPrimary ell (K := K) a ∧
      IsPrimeToP (p := ell) (K := K) a ∧
      Ideal.span {a} =
        (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)) *
          cyclotomicRayCorrection ell K i ∧
      ∀ φ : K →+* ℂ,
        ‖φ (a : K)‖ ≤ rayHeightConstant ell K *
          (p.1 : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) := by
  obtain ⟨i, a, hprimary, hprime, hspan, hheight⟩ :=
    (rayHeightConstant_spec ell K).2
      (exceptionalPrimeIdeal ell K t x p)
      (exceptionalPrimeIdeal_coprime_lambda ell K hodd t x p)
  refine ⟨i, a, hprimary, hprime, hspan, ?_⟩
  intro φ
  simpa only [exceptionalPrimeIdeal_absNorm] using hheight φ

/-- The correction index selected together with the height-controlled
primary generator of an exceptional prime. -/
noncomputable def heightCorrectionIndex (hodd : Odd ell) (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    CyclotomicRayCorrectionIndex ell K :=
  Classical.choose (exists_exceptionalHeightGenerator ell K hodd t x p)

/-- The height-controlled primary generator attached to an exceptional
rational prime. -/
noncomputable def heightPrimaryGenerator (hodd : Odd ell) (t x : ℕ)
    (p : ExceptionalPrime ell t x) : 𝓞 K :=
  Classical.choose
    (Classical.choose_spec
      (exists_exceptionalHeightGenerator ell K hodd t x p))

theorem heightPrimaryGenerator_spec (hodd : Odd ell) (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    FLT37.IsPrimary ell (K := K)
        (heightPrimaryGenerator ell K hodd t x p) ∧
      IsPrimeToP (p := ell) (K := K)
        (heightPrimaryGenerator ell K hodd t x p) ∧
      Ideal.span ({heightPrimaryGenerator ell K hodd t x p} : Set (𝓞 K)) =
        (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)) *
          cyclotomicRayCorrection ell K
            (heightCorrectionIndex ell K hodd t x p) ∧
      ∀ φ : K →+* ℂ,
        ‖φ (heightPrimaryGenerator ell K hodd t x p : K)‖ ≤
          rayHeightConstant ell K *
            (p.1 : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) :=
  Classical.choose_spec
    (Classical.choose_spec
      (exists_exceptionalHeightGenerator ell K hodd t x p))

/-- The correction-tagged generator.  Retaining the finite correction tag
is exactly what makes the conductor encoding injective. -/
noncomputable def encodedExceptionalPrime (hodd : Odd ell) (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    CyclotomicRayCorrectionIndex ell K × 𝓞 K :=
  (heightCorrectionIndex ell K hodd t x p,
    heightPrimaryGenerator ell K hodd t x p)

theorem encodedExceptionalPrime_injective (hodd : Odd ell) (t x : ℕ) :
    Function.Injective (encodedExceptionalPrime ell K hodd t x) := by
  intro p q hpq
  have hi : heightCorrectionIndex ell K hodd t x p =
      heightCorrectionIndex ell K hodd t x q := congrArg Prod.fst hpq
  have ha : heightPrimaryGenerator ell K hodd t x p =
      heightPrimaryGenerator ell K hodd t x q := congrArg Prod.snd hpq
  have hprod :
      (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)) *
          cyclotomicRayCorrection ell K
            (heightCorrectionIndex ell K hodd t x p) =
        (exceptionalPrimeIdeal ell K t x q : Ideal (𝓞 K)) *
          cyclotomicRayCorrection ell K
            (heightCorrectionIndex ell K hodd t x p) := by
    calc
      _ = Ideal.span
          ({heightPrimaryGenerator ell K hodd t x p} : Set (𝓞 K)) :=
        (heightPrimaryGenerator_spec ell K hodd t x p).2.2.1.symm
      _ = Ideal.span
          ({heightPrimaryGenerator ell K hodd t x q} : Set (𝓞 K)) := by
        rw [ha]
      _ = (exceptionalPrimeIdeal ell K t x q : Ideal (𝓞 K)) *
          cyclotomicRayCorrection ell K
            (heightCorrectionIndex ell K hodd t x p) := by
        rw [hi]
        exact (heightPrimaryGenerator_spec ell K hodd t x q).2.2.1
  have hP : (exceptionalPrimeIdeal ell K t x p : Ideal (𝓞 K)) =
      (exceptionalPrimeIdeal ell K t x q : Ideal (𝓞 K)) := by
    exact mul_right_cancel₀
      (cyclotomicRayCorrection_ne_bot ell K
        (heightCorrectionIndex ell K hodd t x p)) hprod
  apply Subtype.ext
  have hn := congrArg Ideal.absNorm hP
  simpa only [exceptionalPrimeIdeal_absNorm] using hn

/-- The finite set of correction-tagged height-controlled generators. -/
noncomputable def encodedExceptionalPrimes (hodd : Odd ell) (t x : ℕ) :
    Finset (CyclotomicRayCorrectionIndex ell K × 𝓞 K) := by
  classical
  exact Finset.univ.image (encodedExceptionalPrime ell K hodd t x)

theorem card_encodedExceptionalPrimes (hodd : Odd ell) (t x : ℕ) :
    (encodedExceptionalPrimes ell K hodd t x).card =
      (exceptionalPrimes ell t x).card := by
  classical
  rw [encodedExceptionalPrimes,
    Finset.card_image_of_injective _
      (encodedExceptionalPrime_injective ell K hodd t x)]
  simp

/-! ## Exact correction and full-residue cells -/

/-- Full residues of the selected height-controlled generator at a finite
family of rational integer moduli. -/
noncomputable def heightGeneratorResidueCode
    {Q : Type*} (q : Q → ℕ) (hodd : Odd ell) (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    RationalResidueTensor (K := K) Q q :=
  rationalResidueCode (K := K) q
    (heightPrimaryGenerator ell K hodd t x p)

/-- Exceptional conductors carrying one fixed ray-correction index. -/
noncomputable def exceptionalCorrectionFiber (hodd : Odd ell) (t x : ℕ)
    (i : CyclotomicRayCorrectionIndex ell K) :
    Finset (ExceptionalPrime ell t x) := by
  classical
  exact finiteCorrectionFiber Finset.univ
    (heightCorrectionIndex ell K hodd t x) i

@[simp] theorem mem_exceptionalCorrectionFiber (hodd : Odd ell) (t x : ℕ)
    (i : CyclotomicRayCorrectionIndex ell K)
    (p : ExceptionalPrime ell t x) :
    p ∈ exceptionalCorrectionFiber ell K hodd t x i ↔
      heightCorrectionIndex ell K hodd t x p = i := by
  classical
  simp [exceptionalCorrectionFiber, finiteCorrectionFiber]

/-- Within one fixed correction fibre, the height-controlled generator map
is injective. -/
theorem heightPrimaryGenerator_injectiveOn_correctionFiber
    (hodd : Odd ell) (t x : ℕ)
    (i : CyclotomicRayCorrectionIndex ell K) :
    Set.InjOn (heightPrimaryGenerator ell K hodd t x)
      (exceptionalCorrectionFiber ell K hodd t x i :
        Set (ExceptionalPrime ell t x)) := by
  intro p hp q hq ha
  apply encodedExceptionalPrime_injective ell K hodd t x
  apply Prod.ext
  · exact (mem_exceptionalCorrectionFiber ell K hodd t x i p).mp hp |>.trans
      ((mem_exceptionalCorrectionFiber ell K hodd t x i q).mp hq).symm
  · exact ha

/-- Cardinality is preserved when one fixed correction fibre is projected
to its generators. -/
theorem card_heightPrimaryGenerator_image_correctionFiber
    (hodd : Odd ell) (t x : ℕ)
    (i : CyclotomicRayCorrectionIndex ell K) :
    ((exceptionalCorrectionFiber ell K hodd t x i).image
      (heightPrimaryGenerator ell K hodd t x)).card =
        (exceptionalCorrectionFiber ell K hodd t x i).card := by
  classical
  exact Finset.card_image_iff.mpr
    (heightPrimaryGenerator_injectiveOn_correctionFiber ell K hodd t x i)

/-- Full residue codes which actually occur in one correction fibre. -/
noncomputable def allowedFullResidueCodes
    {Q : Type*} [Fintype Q] (q : Q → ℕ)
    (hodd : Odd ell) (t x : ℕ)
    (i : CyclotomicRayCorrectionIndex ell K) :
    Finset (RationalResidueTensor (K := K) Q q) := by
  classical
  exact (exceptionalCorrectionFiber ell K hodd t x i).image
    (heightGeneratorResidueCode ell K q hodd t x)

/-- One literal full-residue cell inside a fixed correction fibre. -/
noncomputable def exceptionalFullResidueCell
    {Q : Type*} [Fintype Q] (q : Q → ℕ)
    (hodd : Odd ell) (t x : ℕ)
    (i : CyclotomicRayCorrectionIndex ell K)
    (c : RationalResidueTensor (K := K) Q q) :
    Finset (ExceptionalPrime ell t x) := by
  classical
  exact (exceptionalCorrectionFiber ell K hodd t x i).filter
    (fun p ↦ heightGeneratorResidueCode ell K q hodd t x p = c)

@[simp] theorem mem_exceptionalFullResidueCell
    {Q : Type*} [Fintype Q] (q : Q → ℕ)
    (hodd : Odd ell) (t x : ℕ)
    (i : CyclotomicRayCorrectionIndex ell K)
    (c : RationalResidueTensor (K := K) Q q)
    (p : ExceptionalPrime ell t x) :
    p ∈ exceptionalFullResidueCell ell K q hodd t x i c ↔
      heightCorrectionIndex ell K hodd t x p = i ∧
        heightGeneratorResidueCode ell K q hodd t x p = c := by
  classical
  simp [exceptionalFullResidueCell]

/-- The exact union of all allowed correction-indexed full residue cells. -/
noncomputable def allowedFullResidueCellUnion
    {Q : Type*} [Fintype Q] (q : Q → ℕ)
    (hodd : Odd ell) (t x : ℕ) :
    Finset (ExceptionalPrime ell t x) := by
  classical
  letI : Fintype (CyclotomicRayCorrectionIndex ell K) := Fintype.ofFinite _
  exact Finset.univ.biUnion fun i ↦
    (allowedFullResidueCodes ell K q hodd t x i).biUnion fun c ↦
      exceptionalFullResidueCell ell K q hodd t x i c

/-- Every exceptional rational prime lies in the exact allowed full-cell
union, and conversely that union contains no extraneous conductor. -/
theorem allowedFullResidueCellUnion_eq_univ
    {Q : Type*} [Fintype Q] (q : Q → ℕ)
    (hodd : Odd ell) (t x : ℕ) :
    allowedFullResidueCellUnion ell K q hodd t x = Finset.univ := by
  classical
  letI : Fintype (CyclotomicRayCorrectionIndex ell K) := Fintype.ofFinite _
  ext p
  simp only [allowedFullResidueCellUnion, Finset.mem_biUnion,
    Finset.mem_univ, iff_true]
  refine ⟨heightCorrectionIndex ell K hodd t x p, trivial, ?_⟩
  refine ⟨heightGeneratorResidueCode ell K q hodd t x p, ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨p, (mem_exceptionalCorrectionFiber ell K hodd t x _ p).mpr rfl, rfl⟩
  · exact (mem_exceptionalFullResidueCell ell K q hodd t x _ _ p).mpr
      ⟨rfl, rfl⟩

/-- The full-cell union has exactly the number of original exceptional
rational primes. -/
theorem card_allowedFullResidueCellUnion
    {Q : Type*} [Fintype Q] (q : Q → ℕ)
    (hodd : Odd ell) (t x : ℕ) :
    (allowedFullResidueCellUnion ell K q hodd t x).card =
      (exceptionalPrimes ell t x).card := by
  rw [allowedFullResidueCellUnion_eq_univ]
  simp

end

end Erdos980.ElliottTail.OddMediumRayEncoding
