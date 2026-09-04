import ErdosProblems.Erdos980.ElliottTail.OddInertTensorCells
import ErdosProblems.Erdos980.ElliottTail.OddFilteredInertPrimes
import ErdosProblems.Erdos980.ElliottTail.OddMediumCoordinateBridge
import ErdosProblems.Erdos980.ElliottTail.OddPowerReciprocity
import ErdosProblems.Erdos980.ElliottTail.RationalPrimeGeneratorBridge

/-!
# Exceptional balanced generators in inert tensor cells

This file is the lossless arithmetic membership layer between rational
exceptional primes and the exact finite cells of `OddInertTensorCells`.
The two normalizations of the corrected generator are both retained:

* the primary generator is used in Eisenstein reciprocity;
* the balanced generator is used in the fixed correction-ideal lattice.

After fixing the finite correction index and the finite balancing-unit tag,
all exceptional balanced generators have the same local `ell`-power class
at every selected inert auxiliary prime.  The final finite image is
injective, so passing from rational primes to balanced lattice generators
does not lose cardinality.
-/

open scoped BigOperators NumberField nonZeroDivisors

noncomputable section

namespace Erdos980.ElliottTail.OddInertGeneratorMembership

open Function NumberField Ideal
open BernoulliRegular
open BernoulliRegular.Furtwaengler
open BernoulliRegular.Reflection.ResidueSymbol.PowerResidue
open NumberFieldLargerSieve
open OddInertAuxiliaryPrimes
open OddInertTensorCells
open OddPowerReciprocity
open RationalPrimeGeneratorBridge
open OddMediumCoordinateBridge
open RayPrincipalization
open RayPrincipalizationHeight
open LocalNormEuler
open IdealGeneratorCongruenceCount

variable (ell : ℕ) [Fact ell.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-! ## Equality of symbols is equality of power classes -/

/-- The finite-field exponent is precisely the quotient map modulo
`ell`-th powers, expressed in `ZMod ell`.  This form avoids choosing an
isomorphism between the abstract quotient and `ZMod ell`. -/
theorem powerClass_eq_iff_finiteFieldExponent_eq
    {k : Type*} [Field k] [Fintype k]
    (zeta : kˣ) (hzeta : IsPrimitiveRoot zeta ell)
    (hdiv : ell ∣ Fintype.card k - 1) (x y : kˣ) :
    powerClass ell x = powerClass ell y ↔
      finiteFieldExponent zeta hzeta hdiv x =
        finiteFieldExponent zeta hzeta hdiv y := by
  let : NeZero ell := ⟨(Fact.out : ell.Prime).ne_zero⟩
  constructor
  · intro hclass
    have hmem : x / y ∈ (powMonoidHom ell : kˣ →* kˣ).range := by
      exact (QuotientGroup.eq_iff_div_mem).mp hclass
    obtain ⟨z, hz⟩ := hmem
    have hzero : finiteFieldExponent zeta hzeta hdiv (x / y) = 0 :=
      finiteFieldExponent_eq_zero_of_isPow zeta hzeta hdiv
        ⟨z, hz.symm⟩
    have hmul := finiteFieldExponent_mul zeta hzeta hdiv (x / y) y
    simpa [hzero] using hmul
  · intro hexp
    have hmul := finiteFieldExponent_mul zeta hzeta hdiv (x / y) y
    have hzero : finiteFieldExponent zeta hzeta hdiv (x / y) = 0 := by
      apply add_right_cancel (b := finiteFieldExponent zeta hzeta hdiv y)
      calc
        finiteFieldExponent zeta hzeta hdiv (x / y) +
              finiteFieldExponent zeta hzeta hdiv y =
            finiteFieldExponent zeta hzeta hdiv ((x / y) * y) := hmul.symm
        _ = finiteFieldExponent zeta hzeta hdiv x := by simp
        _ = finiteFieldExponent zeta hzeta hdiv y := hexp
        _ = 0 + finiteFieldExponent zeta hzeta hdiv y := by simp
    obtain ⟨z, hz⟩ :=
      (finiteFieldExponent_eq_zero_iff_isPow zeta hzeta hdiv (x / y)).mp hzero
    apply (QuotientGroup.eq_iff_div_mem).mpr
    exact ⟨z, hz.symm⟩

/-- The rational modulus of an inert auxiliary prime is maximal. -/
theorem inertAuxiliaryRationalModulusIdeal_isMaximal
    {t q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t) :
    (rationalModulusIdeal K q).IsMaximal := by
  have hprime : (rationalModulusIdeal K q).IsPrime := by
    simpa [rationalModulusIdeal] using
      inertAuxiliaryPrimes_span_isPrime ell (K := K) hq
  exact hprime.isMaximal (rationalModulusIdeal_ne_bot
    (inertAuxiliaryPrimes_prime ell hq).ne_zero)

/-- At an inert rational prime, equality of canonical integer-denominator
symbols is exactly equality of the local unit power classes. -/
theorem integerSymbol_eq_iff_powerClass_eq
    {t q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t)
    {a b : 𝓞 K}
    (ha : a ∉ rationalModulusIdeal K q)
    (hb : b ∉ rationalModulusIdeal K q)
    (hellNotMem : (ell : 𝓞 K) ∉ rationalModulusIdeal K q) :
    pthSymbolAtInt_canonical (p := ell) (K := K) a (q : ℤ) =
        pthSymbolAtInt_canonical (p := ell) (K := K) b (q : ℤ) ↔
      powerClass ell
          (@quotientUnitOfNotMem _ _ (rationalModulusIdeal K q)
            (inertAuxiliaryRationalModulusIdeal_isMaximal ell K hq) a ha) =
        powerClass ell
          (@quotientUnitOfNotMem _ _ (rationalModulusIdeal K q)
            (inertAuxiliaryRationalModulusIdeal_isMaximal ell K hq) b hb) := by
  let P : Ideal (𝓞 K) := rationalModulusIdeal K q
  have hPprime : P.IsPrime := by
    simpa [P, rationalModulusIdeal] using
      inertAuxiliaryPrimes_span_isPrime ell (K := K) hq
  have hPne : P ≠ ⊥ := by
    simpa [P] using rationalModulusIdeal_ne_bot
      (K := K) (inertAuxiliaryPrimes_prime ell hq).ne_zero
  have hPmax : P.IsMaximal := hPprime.isMaximal hPne
  let : P.IsPrime := hPprime
  let : P.IsMaximal := hPmax
  let : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  let : Finite (𝓞 K ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient hPne
  let : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hdivNat : ell ∣ Nat.card ((𝓞 K ⧸ P)ˣ) := by
    have h := inertAuxiliaryPrimes_ell_dvd_quotient_units_natCard
      ell (K := K) hq
    change ell ∣ Nat.card ((𝓞 K ⧸ P)ˣ) at h
    exact h
  have hdiv : ell ∣ Fintype.card (𝓞 K ⧸ P) - 1 := by
    rw [Nat.card_units, Nat.card_eq_fintype_card] at hdivNat
    exact hdivNat
  have hden : rationalIntIdeal (K := K) (q : ℤ) = P := by
    simp [P, rationalIntIdeal, rationalModulusIdeal]
  rw [pthSymbolAtInt_canonical_eq_atIdeal,
    pthSymbolAtInt_canonical_eq_atIdeal, hden,
    pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical a hPne,
    pthSymbolAtIdeal_canonical_prime_eq_pthSymbolAtPrime_canonical b hPne,
    pthSymbolAtPrime_canonical_eq_primeExponent hPne hPmax ha hdiv hellNotMem,
    pthSymbolAtPrime_canonical_eq_primeExponent hPne hPmax hb hdiv hellNotMem]
  change finiteFieldExponent
      (canonicalResidueZetaP (p := ell) (K := K) P)
      (canonicalResidueZetaP_isPrimitiveRoot hPne hellNotMem) hdiv
      (quotientUnitOfNotMem P a ha) =
      finiteFieldExponent
        (canonicalResidueZetaP (p := ell) (K := K) P)
        (canonicalResidueZetaP_isPrimitiveRoot hPne hellNotMem) hdiv
        (quotientUnitOfNotMem P b hb) ↔ _
  exact (powerClass_eq_iff_finiteFieldExponent_eq ell
    (canonicalResidueZetaP (p := ell) (K := K) P)
    (canonicalResidueZetaP_isPrimitiveRoot hPne hellNotMem) hdiv
    (quotientUnitOfNotMem P a ha)
    (quotientUnitOfNotMem P b hb)).symm

/-! ## Exceptional-prime encoding and finite fibres -/

/-- Exceptional rational conductors as a finite subtype. -/
abbrev ExceptionalPrime (t x : ℕ) := ↑(exceptionalPrimes ell t x)

theorem exceptionalPrime_eligible (t x : ℕ)
    (p : ExceptionalPrime ell t x) : Eligible ell p.1 :=
  eligible_of_mem_exceptionalPrimes (Fact.out : ell.Prime).two_le p.2

/-- The balanced principalization data chosen for an exceptional prime. -/
noncomputable def exceptionalGeneratorData (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    BoundedGeneratorEncodingData ell K p.1 :=
  boundedGeneratorEncodingData ell K
    (exceptionalPrime_eligible ell t x p)

/-- The finite correction/unit tag of an exceptional prime. -/
noncomputable def exceptionalGeneratorTag (t x : ℕ)
    (p : ExceptionalPrime ell t x) :
    CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K :=
  ((exceptionalGeneratorData ell K t x p).correctionIndex,
    (exceptionalGeneratorData ell K t x p).unitResidueIndex)

/-- One correction/unit fibre of the exceptional rational primes. -/
noncomputable def exceptionalGeneratorFiber (t x : ℕ)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :
    Finset (ExceptionalPrime ell t x) := by
  classical
  exact Finset.univ.filter fun p ↦
    exceptionalGeneratorTag ell K t x p = tag

@[simp] theorem mem_exceptionalGeneratorFiber
    {t x : ℕ}
    {tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K}
    {p : ExceptionalPrime ell t x} :
    p ∈ exceptionalGeneratorFiber ell K t x tag ↔
      exceptionalGeneratorTag ell K t x p = tag := by
  classical
  rw [exceptionalGeneratorFiber, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    exact ⟨by simpa using p.2, h⟩

/-- The balanced algebraic integer attached to an exceptional conductor. -/
noncomputable def exceptionalBalancedGenerator (t x : ℕ)
    (p : ExceptionalPrime ell t x) : 𝓞 K :=
  (exceptionalGeneratorData ell K t x p).balancedGenerator

/-- Within a fixed finite tag, the balanced generator remembers the
rational conductor. -/
theorem exceptionalBalancedGenerator_injective_on_fiber
    {t x : ℕ}
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :
    Set.InjOn (exceptionalBalancedGenerator ell K t x)
      (exceptionalGeneratorFiber ell K t x tag : Set
        (ExceptionalPrime ell t x)) := by
  classical
  intro p hp q hq hpq
  have htagp : exceptionalGeneratorTag ell K t x p = tag := by
    exact (mem_exceptionalGeneratorFiber (ell := ell) (K := K)).mp hp
  have htagq : exceptionalGeneratorTag ell K t x q = tag := by
    exact (mem_exceptionalGeneratorFiber (ell := ell) (K := K)).mp hq
  let S := exceptionalPrimes ell t x
  let hS : ∀ r ∈ S, Eligible ell r := fun r hr ↦
    eligible_of_mem_exceptionalPrimes (Fact.out : ell.Prime).two_le hr
  apply encodeEligibleFinset_injective ell K S hS
  have htag : exceptionalGeneratorTag ell K t x p =
      exceptionalGeneratorTag ell K t x q := htagp.trans htagq.symm
  have henc :
      ((exceptionalGeneratorData ell K t x p).correctionIndex,
        (exceptionalGeneratorData ell K t x p).unitResidueIndex,
        (exceptionalGeneratorData ell K t x p).balancedGenerator) =
      ((exceptionalGeneratorData ell K t x q).correctionIndex,
        (exceptionalGeneratorData ell K t x q).unitResidueIndex,
        (exceptionalGeneratorData ell K t x q).balancedGenerator) := by
    rw [Prod.mk.injEq, Prod.mk.injEq]
    exact ⟨congrArg (fun z ↦ z.1) htag,
      congrArg (fun z ↦ z.2) htag, hpq⟩
  simpa only [encodeEligibleFinset, exceptionalGeneratorData] using henc

/-- The finite balanced-generator image of one tag fibre. -/
noncomputable def exceptionalBalancedGeneratorImage
    (t x : ℕ)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :
    Finset (𝓞 K) := by
  classical
  exact (exceptionalGeneratorFiber ell K t x tag).image
    (exceptionalBalancedGenerator ell K t x)

/-- The conductor-to-generator map loses no cardinality on a fixed tag. -/
theorem card_exceptionalBalancedGeneratorImage
    (t x : ℕ)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :
    (exceptionalBalancedGeneratorImage ell K t x tag).card =
      (exceptionalGeneratorFiber ell K t x tag).card := by
  classical
  rw [exceptionalBalancedGeneratorImage,
    Finset.card_image_iff.mpr]
  intro p hp q hq hpq
  exact exceptionalBalancedGenerator_injective_on_fiber
    ell K tag hp hq hpq

/-! ## Arithmetic support of the auxiliary symbols -/

/-- Coprimality with the norm of a nonzero correction ideal implies ideal
coprimality with the corresponding rational scalar modulus. -/
theorem rationalModulusIdeal_coprime_correction
    (J : (Ideal (𝓞 K))⁰) (q : ℕ)
    (hcop : q.Coprime (Ideal.absNorm (J : Ideal (𝓞 K)))) :
    IsCoprime (rationalModulusIdeal K q) (J : Ideal (𝓞 K)) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  apply Ideal.absNorm_eq_one_iff.mp
  have hJdiv : Ideal.absNorm
      (rationalModulusIdeal K q ⊔ (J : Ideal (𝓞 K))) ∣
      Ideal.absNorm (J : Ideal (𝓞 K)) :=
    Ideal.absNorm_dvd_absNorm_of_le le_sup_right
  have hqdiv : Ideal.absNorm
      (rationalModulusIdeal K q ⊔ (J : Ideal (𝓞 K))) ∣
      q ^ Module.finrank ℤ (𝓞 K) := by
    have h := Ideal.absNorm_dvd_absNorm_of_le
      (show rationalModulusIdeal K q ≤
        rationalModulusIdeal K q ⊔ (J : Ideal (𝓞 K)) from le_sup_left)
    simpa only [rationalModulusIdeal, Ideal.absNorm_span_natCast] using h
  have hnormCop : (Ideal.absNorm (J : Ideal (𝓞 K))).Coprime
      (q ^ Module.finrank ℤ (𝓞 K)) := hcop.symm.pow_right _
  apply Nat.dvd_one.mp
  rw [← hnormCop.gcd_eq_one]
  exact Nat.dvd_gcd hJdiv hqdiv

/-- A prime ideal of absolute norm `p` has residue field canonically
equivalent to `ZMod p`. -/
noncomputable def residueEquivOfPrimeAbsNorm
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 K))
    (hPprime : P.IsPrime) (hPnorm : Ideal.absNorm P = p) :
    ZMod p ≃+* (𝓞 K ⧸ P) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hPnorm
    exact hp.ne_zero hPnorm.symm
  letI : P.IsMaximal := hPprime.isMaximal hPne
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Finite (𝓞 K ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient hPne
  have hpMem : (p : 𝓞 K) ∈ P := by
    rw [← hPnorm]
    exact P.absNorm_mem
  have hpZero : (p : 𝓞 K ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P),
      Ideal.Quotient.eq_zero_iff_mem]
    exact hpMem
  letI : CharP (𝓞 K ⧸ P) p :=
    (CharP.charP_iff_prime_eq_zero hp).2 hpZero
  let residueMap : ZMod p →+* (𝓞 K ⧸ P) := ZMod.castHom dvd_rfl _
  have hcard : Nat.card (𝓞 K ⧸ P) = p := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hPnorm]
  exact RingEquiv.ofBijective residueMap
    ((Nat.bijective_iff_injective_and_card residueMap).2
      ⟨residueMap.injective, by rw [Nat.card_zmod, hcard]⟩)

/-- Every selected auxiliary prime is an `ell`-th power modulo an
exceptional conductor. -/
theorem exists_auxiliaryPow_of_mem_exceptional
    {t x : ℕ} (p : ExceptionalPrime ell t x)
    {q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t) :
    ∃ b : ZMod p.1, b ^ ell = (q : ZMod p.1) := by
  classical
  have helig := exceptionalPrime_eligible ell t x p
  have hpMem := mem_exceptionalPrimes.mp p.2
  have hqleast : q < leastKthPowerNonresidue ell p.1 :=
    (inertAuxiliaryPrimes_lt ell hq).trans hpMem.2.2
  have hleastp : leastKthPowerNonresidue ell p.1 < p.1 :=
    leastKthPowerNonresidue_lt (Fact.out : ell.Prime).two_le helig
  have hqp : q < p.1 := hqleast.trans hleastp
  have hpdvd : ¬ p.1 ∣ q :=
    Nat.not_dvd_of_pos_of_lt (inertAuxiliaryPrimes_prime ell hq).pos hqp
  have hcop : q.Coprime p.1 :=
    Nat.coprime_comm.mp (helig.1.coprime_iff_not_dvd.mpr hpdvd)
  have hunit : IsUnit (q : ZMod p.1) :=
    (ZMod.isUnit_iff_coprime q p.1).mpr hcop
  have hnot := not_kthPowerNonresidue_of_lt_least
    (Fact.out : ell.Prime).two_le helig hqleast
  by_contra hpow
  exact hnot ⟨hunit, hpow⟩

/-- An auxiliary prime smaller than the exceptional cutoff does not lie in
the selected conductor prime ideal. -/
theorem auxiliary_not_mem_exceptionalPrimeIdeal
    {t x : ℕ} (p : ExceptionalPrime ell t x)
    {q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t) :
    (q : 𝓞 K) ∉
      ((exceptionalGeneratorData ell K t x p).primeIdeal : Ideal (𝓞 K)) := by
  intro hmem
  let data := exceptionalGeneratorData ell K t x p
  have hdvdZ := Ideal.absNorm_dvd_norm_of_mem hmem
  have hdvd : p.1 ∣ q ^ Module.finrank ℤ (𝓞 K) := by
    rw [data.primeIdeal_absNorm, Algebra.norm_natCast] at hdvdZ
    exact_mod_cast hdvdZ
  have hpdivq := (exceptionalPrime_eligible ell t x p).1.dvd_of_dvd_pow hdvd
  have hqleast : q < leastKthPowerNonresidue ell p.1 :=
    (inertAuxiliaryPrimes_lt ell hq).trans
      (mem_exceptionalPrimes.mp p.2).2.2
  have hqp := hqleast.trans
    (leastKthPowerNonresidue_lt (Fact.out : ell.Prime).two_le
      (exceptionalPrime_eligible ell t x p))
  exact (Nat.not_dvd_of_pos_of_lt
    (inertAuxiliaryPrimes_prime ell hq).pos hqp) hpdivq

/-- The exponent prime is also absent from the exceptional conductor ideal. -/
theorem exponent_not_mem_exceptionalPrimeIdeal
    {t x : ℕ} (p : ExceptionalPrime ell t x) :
    (ell : 𝓞 K) ∉
      ((exceptionalGeneratorData ell K t x p).primeIdeal : Ideal (𝓞 K)) := by
  intro hmem
  let data := exceptionalGeneratorData ell K t x p
  have hdvdZ := Ideal.absNorm_dvd_norm_of_mem hmem
  have hdvd : p.1 ∣ ell ^ Module.finrank ℤ (𝓞 K) := by
    rw [data.primeIdeal_absNorm, Algebra.norm_natCast] at hdvdZ
    exact_mod_cast hdvdZ
  exact (eligible_not_dvd_exponent ell
    (exceptionalPrime_eligible ell t x p))
      ((exceptionalPrime_eligible ell t x p).1.dvd_of_dvd_pow hdvd)

private theorem not_mem_of_coprime_span
    {R : Type*} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤)
    {a : R} (hcop : IsCoprime I (Ideal.span ({a} : Set R))) :
    a ∉ I := by
  intro ha
  have hle : Ideal.span ({a} : Set R) ≤ I :=
    (Ideal.span_singleton_le_iff_mem I).mpr ha
  have hsup := Ideal.isCoprime_iff_sup_eq.mp hcop
  rw [sup_eq_left.mpr hle] at hsup
  exact hI hsup

/-- The rational auxiliary ideal is coprime to both the exceptional prime
ideal and its fixed correction; hence neither corrected generator vanishes
in the auxiliary residue field. -/
theorem exceptionalGenerators_not_mem_auxiliary
    {t x : ℕ} (p : ExceptionalPrime ell t x)
    {q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t)
    (hcopCorrection : q.Coprime (Ideal.absNorm
      (cyclotomicRayCorrection ell K
        (exceptionalGeneratorData ell K t x p).correctionIndex))) :
    let data := exceptionalGeneratorData ell K t x p
    data.primaryGenerator ∉ rationalModulusIdeal K q ∧
      data.balancedGenerator ∉ rationalModulusIdeal K q := by
  let data := exceptionalGeneratorData ell K t x p
  let Pq : Ideal (𝓞 K) := rationalModulusIdeal K q
  let P : Ideal (𝓞 K) := data.primeIdeal
  let C : (Ideal (𝓞 K))⁰ :=
    ⟨cyclotomicRayCorrection ell K data.correctionIndex,
      mem_nonZeroDivisors_iff_ne_zero.mpr
        (cyclotomicRayCorrection_ne_bot ell K data.correctionIndex)⟩
  have hPqprime : Pq.IsPrime := by
    simpa [Pq, rationalModulusIdeal] using
      inertAuxiliaryPrimes_span_isPrime ell (K := K) hq
  have hPqne : Pq ≠ ⊥ := by
    simpa [Pq] using rationalModulusIdeal_ne_bot
      (K := K) (inertAuxiliaryPrimes_prime ell hq).ne_zero
  have hPqmax : Pq.IsMaximal := hPqprime.isMaximal hPqne
  have hPprime : P.IsPrime := data.primeIdeal_isPrime
  have hPne : P ≠ ⊥ := nonZeroDivisors.coe_ne_zero data.primeIdeal
  have hPmax : P.IsMaximal := hPprime.isMaximal hPne
  have hneq : Pq ≠ P := by
    intro heq
    have hqmem : (q : 𝓞 K) ∈ Pq := by
      exact Ideal.subset_span (Set.mem_singleton _)
    have hqmemP : (q : 𝓞 K) ∈ P := by
      rw [← heq]
      exact hqmem
    exact auxiliary_not_mem_exceptionalPrimeIdeal ell K p hq
      hqmemP
  let : Pq.IsMaximal := hPqmax
  let : P.IsMaximal := hPmax
  have hcopP : IsCoprime Pq P :=
    Ideal.isCoprime_of_isMaximal hneq
  have hcopC : IsCoprime Pq (C : Ideal (𝓞 K)) :=
    rationalModulusIdeal_coprime_correction K C q hcopCorrection
  have hcopProd : IsCoprime Pq (P * (C : Ideal (𝓞 K))) :=
    hcopP.mul_right hcopC
  change data.primaryGenerator ∉ Pq ∧ data.balancedGenerator ∉ Pq
  constructor
  · apply not_mem_of_coprime_span hPqmax.ne_top
    simpa [P, C, data.primaryGenerator_span] using hcopProd
  · apply not_mem_of_coprime_span hPqmax.ne_top
    simpa [P, C, data.balancedGenerator_span] using hcopProd

/-- Full integer-reciprocity support for the primary generator. -/
theorem exceptionalPrimary_isCoprimeToPAndAlphaInt
    {t x : ℕ} (p : ExceptionalPrime ell t x)
    {q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t)
    (hcopCorrection : q.Coprime (Ideal.absNorm
      (cyclotomicRayCorrection ell K
        (exceptionalGeneratorData ell K t x p).correctionIndex))) :
    IsCoprimeToPAndAlphaInt (p := ell) (K := K) (q : ℤ)
      (exceptionalGeneratorData ell K t x p).primaryGenerator := by
  let data := exceptionalGeneratorData ell K t x p
  have hnot := exceptionalGenerators_not_mem_auxiliary
    ell K p hq hcopCorrection
  have hcopAlpha : IsCoprime (rationalModulusIdeal K q)
      (Ideal.span ({data.primaryGenerator} : Set (𝓞 K))) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    have hPqprime : (rationalModulusIdeal K q).IsPrime := by
      simpa [rationalModulusIdeal] using
        inertAuxiliaryPrimes_span_isPrime ell (K := K) hq
    have hPqne := rationalModulusIdeal_ne_bot
      (K := K) (inertAuxiliaryPrimes_prime ell hq).ne_zero
    have hPqmax := hPqprime.isMaximal hPqne
    by_contra hsup
    have heq := hPqmax.eq_of_le hsup le_sup_left
    have hle : Ideal.span ({data.primaryGenerator} : Set (𝓞 K)) ≤
        rationalModulusIdeal K q := by
      rw [heq]
      exact le_sup_right
    exact hnot.1 (hle (Ideal.subset_span (Set.mem_singleton _)))
  have hcopEll : IsCoprime (rationalModulusIdeal K q)
      (Ideal.span ({(ell : 𝓞 K)} : Set (𝓞 K))) := by
    rw [rationalModulusIdeal, Ideal.isCoprime_span_singleton_iff]
    exact (inertAuxiliaryPrimes_coprime_ell ell hq).cast (R := 𝓞 K)
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast (inertAuxiliaryPrimes_prime ell hq).ne_zero
  · simpa only [rationalIntIdeal, map_natCast, rationalModulusIdeal] using hcopAlpha
  · simpa only [rationalIntIdeal, map_natCast, rationalModulusIdeal] using hcopEll

/-- Reciprocity fixes the primary generator's local symbol solely from its
finite correction index. -/
theorem exceptionalPrimary_integerSymbol_eq_correction
    (hodd : Odd ell) {t x : ℕ} (p : ExceptionalPrime ell t x)
    {q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t)
    (hcopCorrection : q.Coprime (Ideal.absNorm
      (cyclotomicRayCorrection ell K
        (exceptionalGeneratorData ell K t x p).correctionIndex))) :
    pthSymbolAtInt_canonical (p := ell) (K := K)
        (exceptionalGeneratorData ell K t x p).primaryGenerator (q : ℤ) =
      pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K)
        (cyclotomicRayCorrection ell K
          (exceptionalGeneratorData ell K t x p).correctionIndex) := by
  let data := exceptionalGeneratorData ell K t x p
  let P : Ideal (𝓞 K) := data.primeIdeal
  have hPne : P ≠ ⊥ := nonZeroDivisors.coe_ne_zero data.primeIdeal
  have hPprime : P.IsPrime := data.primeIdeal_isPrime
  have hPmax : P.IsMaximal := hPprime.isMaximal hPne
  let : P.IsPrime := hPprime
  let : P.IsMaximal := hPmax
  apply (zmodPower_iff_integerSymbol_eq_correction
    (K := K) hodd hPne
    (cyclotomicRayCorrection_ne_bot ell K data.correctionIndex)
    (residueEquivOfPrimeAbsNorm K
      (exceptionalPrime_eligible ell t x p).1 P hPprime
      data.primeIdeal_absNorm)
    data.primaryGenerator_isPrimary data.primaryGenerator_isPrimeTo
    data.primaryGenerator_span
    (exceptionalPrimary_isCoprimeToPAndAlphaInt
      ell K p hq hcopCorrection)
    (auxiliary_not_mem_exceptionalPrimeIdeal ell K p hq)
    (by simpa [P, data.primeIdeal_absNorm] using
      dvd_prime_sub_one_of_eligible (exceptionalPrime_eligible ell t x p))
    (exponent_not_mem_exceptionalPrimeIdeal ell K p)).mp
  exact exists_auxiliaryPow_of_mem_exceptional ell p hq

/-! ## Fixed-tag local power-class pattern -/

/-- The local unit represented by a balanced exceptional generator. -/
noncomputable def exceptionalBalancedLocalUnit
    {t x : ℕ} (p : ExceptionalPrime ell t x)
    {q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t)
    (hcopCorrection : q.Coprime (Ideal.absNorm
      (cyclotomicRayCorrection ell K
        (exceptionalGeneratorData ell K t x p).correctionIndex))) :
    (𝓞 K ⧸ rationalModulusIdeal K q)ˣ := by
  let Pq := rationalModulusIdeal K q
  have hprime : Pq.IsPrime := by
    simpa [Pq, rationalModulusIdeal] using
      inertAuxiliaryPrimes_span_isPrime ell (K := K) hq
  letI : Pq.IsMaximal := hprime.isMaximal (by
    simpa [Pq] using rationalModulusIdeal_ne_bot
      (K := K) (inertAuxiliaryPrimes_prime ell hq).ne_zero)
  exact quotientUnitOfNotMem Pq
    (exceptionalGeneratorData ell K t x p).balancedGenerator
    (exceptionalGenerators_not_mem_auxiliary
      ell K p hq hcopCorrection).2

/-- Two exceptional conductors in the same correction/unit fibre determine
the same balanced-generator power class at every admissible auxiliary
prime. -/
theorem exceptionalBalanced_powerClass_eq_of_same_tag
    (hodd : Odd ell) {t x : ℕ}
    {p₁ p₂ : ExceptionalPrime ell t x}
    (htag : exceptionalGeneratorTag ell K t x p₁ =
      exceptionalGeneratorTag ell K t x p₂)
    {q : ℕ} (hq : q ∈ inertAuxiliaryPrimes ell t)
    (hcop₁ : q.Coprime (Ideal.absNorm
      (cyclotomicRayCorrection ell K
        (exceptionalGeneratorData ell K t x p₁).correctionIndex)))
    (hcop₂ : q.Coprime (Ideal.absNorm
      (cyclotomicRayCorrection ell K
        (exceptionalGeneratorData ell K t x p₂).correctionIndex))) :
    powerClass ell (exceptionalBalancedLocalUnit ell K p₁ hq hcop₁) =
      powerClass ell (exceptionalBalancedLocalUnit ell K p₂ hq hcop₂) := by
  let d₁ := exceptionalGeneratorData ell K t x p₁
  let d₂ := exceptionalGeneratorData ell K t x p₂
  have hi : d₁.correctionIndex = d₂.correctionIndex :=
    congrArg Prod.fst htag
  have hr : d₁.unitResidueIndex = d₂.unitResidueIndex :=
    congrArg Prod.snd htag
  have hsymbol :
      pthSymbolAtInt_canonical (p := ell) (K := K)
          d₁.primaryGenerator (q : ℤ) =
        pthSymbolAtInt_canonical (p := ell) (K := K)
          d₂.primaryGenerator (q : ℤ) := by
    calc
      _ = pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K)
          (cyclotomicRayCorrection ell K d₁.correctionIndex) :=
        exceptionalPrimary_integerSymbol_eq_correction
          ell K hodd p₁ hq hcop₁
      _ = pthSymbolAtIdeal_canonical (p := ell) (K := K) (q : 𝓞 K)
          (cyclotomicRayCorrection ell K d₂.correctionIndex) := by rw [hi]
      _ = _ := (exceptionalPrimary_integerSymbol_eq_correction
          ell K hodd p₂ hq hcop₂).symm
  have hnot₁ := exceptionalGenerators_not_mem_auxiliary ell K p₁ hq hcop₁
  have hnot₂ := exceptionalGenerators_not_mem_auxiliary ell K p₂ hq hcop₂
  have hellNot : (ell : 𝓞 K) ∉ rationalModulusIdeal K q := by
    have hprime : (rationalModulusIdeal K q).IsPrime := by
      simpa [rationalModulusIdeal] using
        inertAuxiliaryPrimes_span_isPrime ell (K := K) hq
    apply not_mem_of_coprime_span hprime.ne_top
    rw [rationalModulusIdeal, Ideal.isCoprime_span_singleton_iff]
    exact (inertAuxiliaryPrimes_coprime_ell ell hq).cast (R := 𝓞 K)
  have hprimary :=
    (integerSymbol_eq_iff_powerClass_eq ell K hq
      hnot₁.1 hnot₂.1 hellNot).mp hsymbol
  let v₁ := unitResidueRepresentative ell K d₁.unitResidueIndex
  let v₂ := unitResidueRepresentative ell K d₂.unitResidueIndex
  have hv : v₁ = v₂ := by simp [v₁, v₂, hr]
  have hb₁ : d₁.balancedGenerator = (v₁ : 𝓞 K) * d₁.primaryGenerator := by
    simp [d₁.primaryGenerator_eq, v₁, mul_assoc]
  have hb₂ : d₂.balancedGenerator = (v₂ : 𝓞 K) * d₂.primaryGenerator := by
    simp [d₂.primaryGenerator_eq, v₂, mul_assoc]
  let Pq := rationalModulusIdeal K q
  have hPqprime : Pq.IsPrime := by
    simpa [Pq, rationalModulusIdeal] using
      inertAuxiliaryPrimes_span_isPrime ell (K := K) hq
  let : Pq.IsMaximal := hPqprime.isMaximal (by
    simpa [Pq] using rationalModulusIdeal_ne_bot
      (K := K) (inertAuxiliaryPrimes_prime ell hq).ne_zero)
  have hv₁not : (v₁ : 𝓞 K) ∉ Pq := by
    intro hmem
    have hle := (Ideal.span_singleton_le_iff_mem Pq).mpr hmem
    have htop := Ideal.span_singleton_eq_top.mpr (Units.isUnit v₁)
    exact hPqprime.ne_top (top_unique (htop ▸ hle))
  have hv₂not : (v₂ : 𝓞 K) ∉ Pq := by simpa [hv] using hv₁not
  have hbunit₁ :
      quotientUnitOfNotMem Pq d₁.balancedGenerator hnot₁.2 =
        quotientUnitOfNotMem Pq (v₁ : 𝓞 K) hv₁not *
          quotientUnitOfNotMem Pq d₁.primaryGenerator hnot₁.1 := by
    have hprod₁ : (v₁ : 𝓞 K) * d₁.primaryGenerator ∉ Pq := by
      simpa only [← hb₁] using hnot₁.2
    simpa only [hb₁] using
      quotientUnitOfNotMem_mul Pq hv₁not hnot₁.1 hprod₁
  have hbunit₂ :
      quotientUnitOfNotMem Pq d₂.balancedGenerator hnot₂.2 =
        quotientUnitOfNotMem Pq (v₂ : 𝓞 K) hv₂not *
          quotientUnitOfNotMem Pq d₂.primaryGenerator hnot₂.1 := by
    have hprod₂ : (v₂ : 𝓞 K) * d₂.primaryGenerator ∉ Pq := by
      simpa only [← hb₂] using hnot₂.2
    simpa only [hb₂] using
      quotientUnitOfNotMem_mul Pq hv₂not hnot₂.1 hprod₂
  change powerClass ell
      (quotientUnitOfNotMem Pq d₁.balancedGenerator hnot₁.2) =
    powerClass ell
      (quotientUnitOfNotMem Pq d₂.balancedGenerator hnot₂.2)
  rw [hbunit₁, hbunit₂]
  rw [show powerClass ell
      (quotientUnitOfNotMem Pq (v₁ : 𝓞 K) hv₁not *
        quotientUnitOfNotMem Pq d₁.primaryGenerator hnot₁.1) =
      powerClass ell (quotientUnitOfNotMem Pq (v₁ : 𝓞 K) hv₁not) *
        powerClass ell
          (quotientUnitOfNotMem Pq d₁.primaryGenerator hnot₁.1) by
      exact map_mul (QuotientGroup.mk'
        (powMonoidHom ell : (𝓞 K ⧸ Pq)ˣ →* (𝓞 K ⧸ Pq)ˣ).range) _ _,
    show powerClass ell
      (quotientUnitOfNotMem Pq (v₂ : 𝓞 K) hv₂not *
        quotientUnitOfNotMem Pq d₂.primaryGenerator hnot₂.1) =
      powerClass ell (quotientUnitOfNotMem Pq (v₂ : 𝓞 K) hv₂not) *
        powerClass ell
          (quotientUnitOfNotMem Pq d₂.primaryGenerator hnot₂.1) by
      exact map_mul (QuotientGroup.mk'
        (powMonoidHom ell : (𝓞 K ⧸ Pq)ˣ →* (𝓞 K ⧸ Pq)ˣ).range) _ _]
  have hvunit :
      quotientUnitOfNotMem Pq (v₁ : 𝓞 K) hv₁not =
        quotientUnitOfNotMem Pq (v₂ : 𝓞 K) hv₂not := by
    apply Units.ext
    simp only [quotientUnitOfNotMem, hv]
  rw [hvunit, hprimary]

/-! ## The literal tensor cell of one finite tag fibre -/

/-- The fixed correction ideal selected by a correction/unit tag. -/
noncomputable def tagCorrectionIdeal
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :
    (Ideal (𝓞 K))⁰ :=
  ⟨cyclotomicRayCorrection ell K tag.1,
    mem_nonZeroDivisors_iff_ne_zero.mpr
      (cyclotomicRayCorrection_ne_bot ell K tag.1)⟩

/-- A balanced generator in a tag fibre belongs to that tag's fixed
correction ideal. -/
theorem exceptionalBalancedGenerator_mem_tagCorrectionIdeal
    {t x : ℕ}
    {tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K}
    {p : ExceptionalPrime ell t x}
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    exceptionalBalancedGenerator ell K t x p ∈
      (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) := by
  classical
  let data := exceptionalGeneratorData ell K t x p
  have htag : exceptionalGeneratorTag ell K t x p = tag := by
    rw [exceptionalGeneratorFiber, Finset.mem_filter] at hp
    exact hp.2
  have hi : data.correctionIndex = tag.1 :=
    congrArg Prod.fst htag
  change data.balancedGenerator ∈
    cyclotomicRayCorrection ell K tag.1
  rw [← hi]
  apply (show (data.primeIdeal : Ideal (𝓞 K)) *
      cyclotomicRayCorrection ell K data.correctionIndex ≤
        cyclotomicRayCorrection ell K data.correctionIndex from
      Ideal.mul_le_right)
  rw [← data.balancedGenerator_span]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The tuple of local auxiliary-field units represented by one balanced
exceptional generator. -/
noncomputable def exceptionalBalancedUnitTensor
    {t x : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    ∀ q : Q, InertLocalUnits K Q q := fun q ↦ by
  classical
  have htag : exceptionalGeneratorTag ell K t x p = tag := by
    rw [exceptionalGeneratorFiber, Finset.mem_filter] at hp
    exact hp.2
  have hi : (exceptionalGeneratorData ell K t x p).correctionIndex = tag.1 :=
    congrArg Prod.fst htag
  exact exceptionalBalancedLocalUnit ell K p (hQ q.2) (by
    simpa [tagCorrectionIdeal, hi] using hcop q.1 q.2)

/-- The tensor pattern represented by one member of a nonempty tag fibre. -/
noncomputable def exceptionalBalancedPowerClassPattern
    {t x : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    PowerClassTensor Q (InertLocalUnits K Q) ell :=
  powerClassTensorOf ell
    (exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp)

/-- All members of a fixed correction/unit fibre determine exactly the same
local power-class tensor. -/
theorem exceptionalBalancedPowerClassPattern_eq
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    {p₁ p₂ : ExceptionalPrime ell t x}
    (hp₁ : p₁ ∈ exceptionalGeneratorFiber ell K t x tag)
    (hp₂ : p₂ ∈ exceptionalGeneratorFiber ell K t x tag) :
    exceptionalBalancedPowerClassPattern ell K Q hQ tag hcop p₁ hp₁ =
      exceptionalBalancedPowerClassPattern ell K Q hQ tag hcop p₂ hp₂ := by
  classical
  funext q
  have htag₁ : exceptionalGeneratorTag ell K t x p₁ = tag := by
    exact (mem_exceptionalGeneratorFiber (ell := ell) (K := K)).mp hp₁
  have htag₂ : exceptionalGeneratorTag ell K t x p₂ = tag := by
    exact (mem_exceptionalGeneratorFiber (ell := ell) (K := K)).mp hp₂
  have hi₁ : (exceptionalGeneratorData ell K t x p₁).correctionIndex =
      tag.1 := by
    simpa only [exceptionalGeneratorTag] using congrArg Prod.fst htag₁
  have hi₂ : (exceptionalGeneratorData ell K t x p₂).correctionIndex =
      tag.1 := by
    simpa only [exceptionalGeneratorTag] using congrArg Prod.fst htag₂
  have hcop₁ : q.1.Coprime (Ideal.absNorm
      (cyclotomicRayCorrection ell K
        (exceptionalGeneratorData ell K t x p₁).correctionIndex)) := by
    rw [hi₁]
    simpa only [tagCorrectionIdeal] using hcop q.1 q.2
  have hcop₂ : q.1.Coprime (Ideal.absNorm
      (cyclotomicRayCorrection ell K
        (exceptionalGeneratorData ell K t x p₂).correctionIndex)) := by
    rw [hi₂]
    simpa only [tagCorrectionIdeal] using hcop q.1 q.2
  change powerClass ell
      (exceptionalBalancedLocalUnit ell K p₁ (hQ q.2) hcop₁) =
    powerClass ell
      (exceptionalBalancedLocalUnit ell K p₂ (hQ q.2) hcop₂)
  exact exceptionalBalanced_powerClass_eq_of_same_tag ell K hodd
    (htag₁.trans htag₂.symm) (hQ q.2) hcop₁ hcop₂

/-- The fixed-ideal coordinate vector of every balanced generator in the
fibre lies in the one exact mapped tensor cell determined by any reference
member of that fibre. -/
theorem exceptionalBalancedUnitTensor_mem_inertPowerClassCoordinateCell
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    {p₀ p : ExceptionalPrime ell t x}
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    inertLocalUnitsCoordinateEmbedding K Q
        (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
        (tagCorrectionIdeal ell K tag) hcop
        (exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp) ∈
      inertPowerClassCoordinateCell ell K Q
        (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
        (tagCorrectionIdeal ell K tag) hcop
        (exceptionalBalancedPowerClassPattern
          ell K Q hQ tag hcop p₀ hp₀) := by
  classical
  let hprime : ∀ q ∈ Q, q.Prime :=
    fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq)
  let (q : Q) : NeZero (rationalModulusIdeal K q.1) :=
    ⟨rationalModulusIdeal_ne_bot (hprime q.1 q.2).ne_zero⟩
  let (q : Q) : Finite (InertLocalRing K Q q) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (rationalModulusIdeal_ne_bot (hprime q.1 q.2).ne_zero)
  let : ∀ q : Q, Fintype (InertLocalUnits K Q q) :=
    fun _ ↦ Fintype.ofFinite _
  let (q : Q) : DecidableEq (InertLocalUnits K Q q) := Classical.decEq _
  change inertLocalUnitsCoordinateEmbedding K Q hprime
      (tagCorrectionIdeal ell K tag) hcop
      (exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp) ∈
    mappedPowerClassTensorResidueCell
      (inertLocalUnitsCoordinateEmbedding K Q hprime
        (tagCorrectionIdeal ell K tag) hcop) ell
      (exceptionalBalancedPowerClassPattern
        ell K Q hQ tag hcop p₀ hp₀)
  apply Finset.mem_map.mpr
  refine ⟨exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp, ?_, rfl⟩
  apply mem_tensorPatternFiber.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact exceptionalBalancedPowerClassPattern_eq ell K hodd Q hQ tag hcop hp hp₀

/-! ## Compatibility with the literal fixed-ideal lattice cell -/

/-- Reducing the integral coordinates of an element of `J`, then applying
the coordinate quotient equivalence, recovers its ordinary residue class.
This is the semantic compatibility needed to identify the tensor CRT
coordinates with the geometric congruence-cell label. -/
theorem fixedIdealCoordinateQuotientEquiv_coordinateResidue
    (J : (Ideal (𝓞 K))⁰) {q : ℕ} (hq : q.Prime)
    (hcop : q.Coprime (Ideal.absNorm (J : Ideal (𝓞 K))))
    (b : (J : Ideal (𝓞 K))) :
    fixedIdealCoordinateQuotientEquiv K J q hq hcop
        (coordinateResidue K J q b) =
      Ideal.Quotient.mk (rationalModulusIdeal K q) b.1 := by
  classical
  let : NeZero q := ⟨hq.ne_zero⟩
  rw [fixedIdealCoordinateQuotientEquiv_apply]
  apply Ideal.Quotient.eq.mpr
  have hsame : coordinateResidue K J q
      (coordinateRepresentative K J (coordinateResidue K J q b)) =
        coordinateResidue K J q b := by
    rw [coordinateResidue_coordinateRepresentative]
  obtain ⟨c, hc⟩ :=
    (coordinateResidue_eq_iff_exists_sub_eq_nsmul K J).mp hsame
  rw [rationalModulusIdeal]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨c.1, ?_⟩
  calc
    coordinateRepresentative K J (coordinateResidue K J q b) - b.1 =
        (coordinateRepresentative K J (coordinateResidue K J q b) - b).1 := rfl
    _ = (q • c).1 := congrArg Subtype.val hc
    _ = q • c.1 := rfl
    _ = (q : 𝓞 K) * c.1 := nsmul_eq_mul q c.1

/-- The CRT coordinate vector constructed from the local units of an
exceptional balanced generator is literally its integral-coordinate
residue modulo the product of the auxiliary primes. -/
theorem inertLocalUnitsCoordinateEmbedding_exceptional_eq_coordinateResidue
    {t x : ℕ} (Q : Finset ℕ)
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    inertLocalUnitsCoordinateEmbedding K Q
        (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
        (tagCorrectionIdeal ell K tag) hcop
        (exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp) =
      coordinateResidue K (tagCorrectionIdeal ell K tag)
        (inertTensorModulus Q)
        ⟨exceptionalBalancedGenerator ell K t x p,
          exceptionalBalancedGenerator_mem_tagCorrectionIdeal
            ell K hp⟩ := by
  classical
  let J := tagCorrectionIdeal ell K tag
  let bJ : (J : Ideal (𝓞 K)) :=
    ⟨exceptionalBalancedGenerator ell K t x p,
      exceptionalBalancedGenerator_mem_tagCorrectionIdeal ell K hp⟩
  let hprime : ∀ q ∈ Q, q.Prime :=
    fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq)
  have hmod0 : inertTensorModulus Q ≠ 0 := by
    unfold inertTensorModulus
    exact Finset.prod_ne_zero_iff.mpr fun q _ ↦
      (hprime q.1 q.2).ne_zero
  let : NeZero (inertTensorModulus Q) := ⟨hmod0⟩
  let hpair : Pairwise (Nat.Coprime on fun q : Q ↦ q.1) := by
    intro q r hqr
    exact (Nat.coprime_primes (hprime q.1 q.2)
      (hprime r.1 r.2)).mpr (Subtype.coe_ne_coe.mpr hqr)
  let eCRT := ZMod.prodEquivPi (fun q : Q ↦ q.1) hpair
  funext i
  apply eCRT.injective
  funext q
  change eCRT (eCRT.symm (fun q ↦
      ((fixedIdealCoordinateQuotientEquiv K J q.1
        (hprime q.1 q.2) (hcop q.1 q.2)).symm
        ((exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp q :
          InertLocalRing K Q q))) i)) q =
    eCRT (coordinateResidue K J (inertTensorModulus Q) bJ i) q
  rw [eCRT.apply_symm_apply]
  have huval :
      (exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp q :
          InertLocalRing K Q q) =
        Ideal.Quotient.mk (rationalModulusIdeal K q.1) bJ.1 := by
    simp only [exceptionalBalancedUnitTensor, exceptionalBalancedLocalUnit,
      exceptionalBalancedGenerator, quotientUnitOfNotMem, bJ, J]
    rfl
  have hcoords :
      (fixedIdealCoordinateQuotientEquiv K J q.1
          (hprime q.1 q.2) (hcop q.1 q.2)).symm
          ((exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp q :
            InertLocalRing K Q q)) =
        coordinateResidue K J q.1 bJ := by
    apply (fixedIdealCoordinateQuotientEquiv K J q.1
      (hprime q.1 q.2) (hcop q.1 q.2)).injective
    rw [Equiv.apply_symm_apply, huval]
    exact (fixedIdealCoordinateQuotientEquiv_coordinateResidue
      K J (hprime q.1 q.2) (hcop q.1 q.2) bJ).symm
  rw [hcoords]
  have hcrt := ZMod.prodEquivPi_apply
    (fun q : Q ↦ q.1) hpair
    (coordinateResidue K J (inertTensorModulus Q) bJ i) q
  rw [hcrt]
  exact (map_intCast
    (ZMod.castHom (Finset.dvd_prod_of_mem (fun q : Q ↦ q.1)
      (Finset.mem_univ q)) (ZMod q.1))
    (integralCoordinates K J bJ i)).symm

/-- The Minkowski embedding of an ideal element lies in the geometric cell
labelled by its own integral-coordinate residue. -/
theorem embedding_mem_generatorCongruenceCell_coordinateResidue
    (J : (Ideal (𝓞 K))⁰) (m : ℕ) [NeZero m]
    (b : (J : Ideal (𝓞 K))) :
    (NumberField.mixedEmbedding.stdBasis K).equivFunL
        (NumberField.mixedEmbedding K (b.1 : K)) ∈
      generatorCongruenceCell J m (coordinateResidue K J m b) := by
  classical
  let k := coordinateResidue K J m b
  have hdvd : ∀ i, (m : ℤ) ∣
      integralCoordinates K J b i - ((k i).val : ℤ) := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_sub, Int.cast_natCast, k, coordinateResidue]
    rw [ZMod.natCast_zmod_val, sub_self]
  choose z hz using hdvd
  let zr : NumberField.mixedEmbedding.index K → ℝ :=
    fun i ↦ (z i : ℝ)
  have hzr : zr ∈
      (Submodule.span ℤ (Set.range
        (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K))) :
          Set (NumberField.mixedEmbedding.index K → ℝ)) := by
    let := Fintype.ofFinite (NumberField.mixedEmbedding.index K)
    change zr ∈ Submodule.span ℤ
      (Set.range (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K)))
    simp only [
      (Pi.basisFun ℝ (NumberField.mixedEmbedding.index K)).mem_span_iff_repr_mem
        ℤ zr,
      Pi.basisFun_repr, Set.mem_range, eq_intCast, eq_comm]
    intro i
    exact ⟨z i, rfl⟩
  rw [generatorCongruenceCell]
  refine ⟨scaledIdealLatticeChart J m zr, ⟨zr, hzr, rfl⟩, ?_⟩
  simp only [vadd_eq_add, scaledIdealLatticeChart,
    LinearEquiv.trans_apply, LinearEquiv.smulOfNeZero_apply,
    generatorCongruenceTranslate]
  rw [← map_add, ← idealLatticeChart_integralCoordinates K J b]
  congr 1
  funext i
  change ((k i).val : ℝ) + (m : ℝ) * (z i : ℝ) =
    (integralCoordinates K J b i : ℝ)
  have hint : ((k i).val : ℤ) + (m : ℤ) * z i =
      integralCoordinates K J b i := by
    have := hz i
    omega
  exact_mod_cast hint

/-- Hence every exceptional balanced generator in the fixed tag fibre lies
in the literal generator congruence cell indexed by its tensor-unit
coordinate vector. -/
theorem exceptionalBalancedGenerator_mem_tensorGeneratorCongruenceCell
    {t x : ℕ} (Q : Finset ℕ)
    [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    (NumberField.mixedEmbedding.stdBasis K).equivFunL
        (NumberField.mixedEmbedding K
          (exceptionalBalancedGenerator ell K t x p : K)) ∈
      generatorCongruenceCell (tagCorrectionIdeal ell K tag)
        (inertTensorModulus Q)
        (inertLocalUnitsCoordinateEmbedding K Q
          (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
          (tagCorrectionIdeal ell K tag) hcop
          (exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp)) := by
  classical
  rw [inertLocalUnitsCoordinateEmbedding_exceptional_eq_coordinateResidue
    ell K Q hQ tag hcop p hp]
  exact embedding_mem_generatorCongruenceCell_coordinateResidue K
    (tagCorrectionIdeal ell K tag) (inertTensorModulus Q)
    ⟨exceptionalBalancedGenerator ell K t x p,
      exceptionalBalancedGenerator_mem_tagCorrectionIdeal ell K hp⟩

end Erdos980.ElliottTail.OddInertGeneratorMembership
