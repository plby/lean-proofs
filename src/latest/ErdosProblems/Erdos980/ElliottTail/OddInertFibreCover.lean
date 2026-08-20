import ErdosProblems.Erdos980.ElliottTail.OddInertCandidateInjection

/-!
# Finite correction/unit cover for odd exceptional primes

This file contains the finite bookkeeping that is independent of the
analytic Rosser parameters.  Exceptional rational primes are partitioned by
their correction ideal and balancing-unit tag.  In every tag we separate the
conductors that belong to the chosen rational sieve-prime set from the
surviving conductors.  The latter are exactly the fibres controlled by
`survivingExceptionalGeneratorFiber_card_le_normSiftedMass`.
-/

open scoped BigOperators NumberField nonZeroDivisors

noncomputable section

namespace Erdos980.ElliottTail.OddInertFibreCover

open BernoulliRegular
open OddInertGeneratorMembership
open OddInertCandidateInjection
open OddInertAuxiliaryPrimes
open OddInertTensorCells
open RayPrincipalization
open RayPrincipalizationHeight

variable (ell : ℕ) [Fact ell.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

local notation "lambdaIdeal" =>
  Ideal.span ({FLT37.zetaSubOne ell K} : Set (𝓞 K))

private theorem primaryRayModulus_ne_bot :
    lambdaIdeal ^ (2 * ell) ≠ ⊥ := by
  apply pow_ne_zero
  intro h
  exact FLT37.zetaSubOne_ne_zero ell K (Ideal.span_singleton_eq_bot.mp h)

noncomputable local instance : Finite (𝓞 K ⧸ lambdaIdeal ^ (2 * ell)) :=
  Ring.HasFiniteQuotients.finiteQuotient (primaryRayModulus_ne_bot ell K)

noncomputable local instance : Fintype (𝓞 K ⧸ lambdaIdeal ^ (2 * ell)) :=
  Fintype.ofFinite _

noncomputable local instance :
    Fintype (CyclotomicRayCorrectionIndex ell K) :=
  Fintype.ofFinite _

noncomputable local instance : Fintype (UnitResidueImage ell K) :=
  Fintype.ofFinite _

/-- The fixed finite set of correction-ideal and balancing-unit tags. -/
def exceptionalTagIndices :
    Finset (CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) :=
  Finset.univ

/-- Full local-unit tuples embed into all coordinate residue tuples, so
their density inside the scalar residue space is at most one.  This is the
normalization that preserves the factor `ell⁻ʲ` in the Rosser main term. -/
theorem inertUnitResidueCount_le_fullCoordinateResidues
    {t : ℕ} (Q : Finset ℕ) (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (J : (Ideal (𝓞 K))⁰)
    (hcop : ∀ q ∈ Q, q.Coprime (Ideal.absNorm (J : Ideal (𝓞 K)))) :
    inertUnitResidueCount K Q ≤
      inertTensorModulus Q ^ Nat.card (NumberField.mixedEmbedding.index K) := by
  let hprime : ∀ q ∈ Q, q.Prime :=
    fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq)
  letI : NeZero (inertTensorModulus Q) := ⟨by
    unfold inertTensorModulus
    exact Finset.prod_ne_zero_iff.mpr fun q _ ↦ (hprime q.1 q.2).ne_zero⟩
  have hcard := Nat.card_le_card_of_injective
    (inertLocalUnitsCoordinateEmbedding K Q hprime J hcop)
    (inertLocalUnitsCoordinateEmbedding K Q hprime J hcop).injective
  simpa only [inertUnitResidueCount, Nat.card_fun, Nat.card_zmod] using hcard

/-- Rational conductors in one correction/unit tag. -/
def rationalExceptionalGeneratorFiber
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (t x : ℕ) : Finset ℕ := by
  classical
  exact (exceptionalGeneratorFiber ell K t x tag).image Subtype.val

/-- Conductors in one tag that survive the rational norm sieve. -/
def rationalSurvivingExceptionalGeneratorFiber
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (sievePrimes : Finset ℕ) (t x : ℕ) : Finset ℕ := by
  classical
  exact (survivingExceptionalGeneratorFiber ell K (t := t) (x := x)
    tag sievePrimes).image Subtype.val

/-- Conductors in one tag that are themselves among the rational sieve
primes.  These form the finite sieve loss. -/
def rationalExceptionalSieveLoss
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (sievePrimes : Finset ℕ) (t x : ℕ) : Finset ℕ := by
  classical
  exact ((exceptionalGeneratorFiber ell K t x tag).filter
    fun p ↦ p.1 ∈ sievePrimes).image Subtype.val

/-- The total finite sieve loss after summing over all correction/unit tags. -/
def rationalExceptionalSieveLossTotal
    (sievePrimes :
      (CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) →
        Finset ℕ)
    (t x : ℕ) : Finset ℕ := by
  classical
  exact (exceptionalTagIndices ell K).biUnion fun tag ↦
    rationalExceptionalSieveLoss ell K tag (sievePrimes tag) t x

theorem rationalSurvivingExceptionalGeneratorFiber_card
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (sievePrimes : Finset ℕ) (t x : ℕ) :
    (rationalSurvivingExceptionalGeneratorFiber ell K tag sievePrimes t x).card =
      (survivingExceptionalGeneratorFiber ell K (t := t) (x := x)
        tag sievePrimes).card := by
  classical
  exact Finset.card_image_of_injective _ Subtype.val_injective

theorem rationalExceptionalSieveLoss_subset
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (sievePrimes : Finset ℕ) (t x : ℕ) :
    rationalExceptionalSieveLoss ell K tag sievePrimes t x ⊆ sievePrimes := by
  classical
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  exact (Finset.mem_filter.mp hq).2

theorem rationalExceptionalSieveLossTotal_card_le_sum
    (sievePrimes :
      (CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) →
        Finset ℕ)
    (t x : ℕ) :
    (rationalExceptionalSieveLossTotal ell K sievePrimes t x).card ≤
      ∑ tag ∈ exceptionalTagIndices ell K, (sievePrimes tag).card := by
  classical
  calc
    (rationalExceptionalSieveLossTotal ell K sievePrimes t x).card ≤
        ∑ tag ∈ exceptionalTagIndices ell K,
          (rationalExceptionalSieveLoss ell K tag (sievePrimes tag) t x).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ tag ∈ exceptionalTagIndices ell K, (sievePrimes tag).card := by
      exact Finset.sum_le_sum fun tag _ ↦ Finset.card_le_card
        (rationalExceptionalSieveLoss_subset ell K tag (sievePrimes tag) t x)

/-- Every exceptional rational prime is either a sieve-prime loss in its
own tag or belongs to the surviving part of that tag. -/
theorem exceptionalPrimes_subset_loss_union_survivingFibres
    (sievePrimes :
      (CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K) →
        Finset ℕ)
    (t x : ℕ) :
    exceptionalPrimes ell t x ⊆
      rationalExceptionalSieveLossTotal ell K sievePrimes t x ∪
        (exceptionalTagIndices ell K).biUnion (fun tag ↦
          rationalSurvivingExceptionalGeneratorFiber ell K tag
            (sievePrimes tag) t x) := by
  classical
  intro p hp
  let q : ExceptionalPrime ell t x := ⟨p, hp⟩
  let tag := exceptionalGeneratorTag ell K t x q
  have htag : tag ∈ exceptionalTagIndices ell K := by
    unfold exceptionalTagIndices
    exact Finset.mem_univ tag
  have hqtag : q ∈ exceptionalGeneratorFiber ell K t x tag := by
    exact (mem_exceptionalGeneratorFiber (ell := ell) (K := K)).mpr rfl
  by_cases hsieve : p ∈ sievePrimes tag
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨tag, htag, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨q, Finset.mem_filter.mpr ⟨hqtag, hsieve⟩, rfl⟩
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨tag, htag, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨q, ?_, rfl⟩
    exact (mem_survivingExceptionalGeneratorFiber
      (ell := ell) (K := K)).mpr ⟨hqtag, hsieve⟩

end Erdos980.ElliottTail.OddInertFibreCover
