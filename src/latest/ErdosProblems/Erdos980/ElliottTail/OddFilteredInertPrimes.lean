import ErdosProblems.Erdos980.ElliottTail.OddInertAuxiliaryPrimes

/-!
# Inert auxiliary primes avoiding a fixed correction ideal

For a fixed nonzero ideal `J` of the prime-conductor cyclotomic field, this
file removes from the inert auxiliary primes every rational prime dividing
`Ideal.absNorm J`, then takes the canonical least
`OddMediumParameters.oddTensorDepth t` survivors.

Only finitely many primes are removed.  A deliberately coarse bound by
`Ideal.absNorm J + 1`, together with
`eventually_add_oddTensorDepth_le_inertAuxiliaryPrimes_card`, proves that the
selected family eventually has the requested exact cardinality.
-/

open scoped BigOperators NumberField

namespace Erdos980.ElliottTail.OddFilteredInertPrimes

open Filter Finset NumberField Ideal IsCyclotomicExtension
open OddInertAuxiliaryPrimes

noncomputable section

variable (ell : ℕ) [Fact ell.Prime]
variable {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-- Inert auxiliary primes whose rational prime is coprime to the norm of
the fixed correction ideal. -/
def coprimeInertAuxiliaryPrimes (J : Ideal (𝓞 K)) (t : ℕ) : Finset ℕ :=
  (inertAuxiliaryPrimes ell t).filter fun q => q.Coprime (Ideal.absNorm J)

@[simp] theorem mem_coprimeInertAuxiliaryPrimes
    {J : Ideal (𝓞 K)} {t q : ℕ} :
    q ∈ coprimeInertAuxiliaryPrimes ell J t ↔
      q ∈ inertAuxiliaryPrimes ell t ∧ q.Coprime (Ideal.absNorm J) := by
  simp [coprimeInertAuxiliaryPrimes]

/-- The canonical tensor family after excluding the rational prime support
of `J`. -/
def selectedCoprimeInertAuxiliaryPrimes
    (J : Ideal (𝓞 K)) (t : ℕ) : Finset ℕ :=
  (((coprimeInertAuxiliaryPrimes ell J t).sort (· ≤ ·)).take
    (OddMediumParameters.oddTensorDepth t)).toFinset

theorem selectedCoprimeInertAuxiliaryPrimes_subset_filtered
    (J : Ideal (𝓞 K)) (t : ℕ) :
    selectedCoprimeInertAuxiliaryPrimes ell J t ⊆
      coprimeInertAuxiliaryPrimes ell J t := by
  intro q hq
  have hqTake :
      q ∈ ((coprimeInertAuxiliaryPrimes ell J t).sort (· ≤ ·)).take
        (OddMediumParameters.oddTensorDepth t) := by
    simpa [selectedCoprimeInertAuxiliaryPrimes] using hq
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take hqTake)

theorem coprimeInertAuxiliaryPrimes_subset (J : Ideal (𝓞 K)) (t : ℕ) :
    coprimeInertAuxiliaryPrimes ell J t ⊆ inertAuxiliaryPrimes ell t := by
  intro q hq
  exact ((mem_coprimeInertAuxiliaryPrimes (ell := ell)).mp hq).1

theorem selectedCoprimeInertAuxiliaryPrimes_subset
    (J : Ideal (𝓞 K)) (t : ℕ) :
    selectedCoprimeInertAuxiliaryPrimes ell J t ⊆
      inertAuxiliaryPrimes ell t :=
  (selectedCoprimeInertAuxiliaryPrimes_subset_filtered ell J t).trans
    (coprimeInertAuxiliaryPrimes_subset ell J t)

theorem selectedCoprimeInertAuxiliaryPrimes_card_le
    (J : Ideal (𝓞 K)) (t : ℕ) :
    (selectedCoprimeInertAuxiliaryPrimes ell J t).card ≤
      OddMediumParameters.oddTensorDepth t := by
  rw [selectedCoprimeInertAuxiliaryPrimes,
    List.toFinset_card_of_nodup
      ((coprimeInertAuxiliaryPrimes ell J t).sort_nodup (· ≤ ·)).take,
    List.length_take, (coprimeInertAuxiliaryPrimes ell J t).length_sort]
  exact Nat.min_le_left _ _

theorem selectedCoprimeInertAuxiliaryPrimes_card
    {J : Ideal (𝓞 K)} {t : ℕ}
    (havailable : OddMediumParameters.oddTensorDepth t ≤
      (coprimeInertAuxiliaryPrimes ell J t).card) :
    (selectedCoprimeInertAuxiliaryPrimes ell J t).card =
      OddMediumParameters.oddTensorDepth t := by
  rw [selectedCoprimeInertAuxiliaryPrimes,
    List.toFinset_card_of_nodup
      ((coprimeInertAuxiliaryPrimes ell J t).sort_nodup (· ≤ ·)).take,
    List.length_take, (coprimeInertAuxiliaryPrimes ell J t).length_sort]
  exact Nat.min_eq_left havailable

/-! ## The finite loss and eventual exact cardinality -/

private theorem badInertAuxiliaryPrimes_card_le
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (t : ℕ) :
    ((inertAuxiliaryPrimes ell t).filter
      fun q => ¬q.Coprime (Ideal.absNorm J)).card ≤
        Ideal.absNorm J + 1 := by
  have hnormPos : 0 < Ideal.absNorm J :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hsubset :
      (inertAuxiliaryPrimes ell t).filter
          (fun q => ¬q.Coprime (Ideal.absNorm J)) ⊆
        Finset.range (Ideal.absNorm J + 1) := by
    intro q hq
    simp only [Finset.mem_filter] at hq
    rw [Finset.mem_range]
    have hqprime := inertAuxiliaryPrimes_prime ell hq.1
    have hqDvd : q ∣ Ideal.absNorm J := by
      by_contra hnotDvd
      exact hq.2 (hqprime.coprime_iff_not_dvd.mpr hnotDvd)
    have hqle : q ≤ Ideal.absNorm J := Nat.le_of_dvd hnormPos hqDvd
    omega
  simpa using Finset.card_le_card hsubset

theorem eventually_oddTensorDepth_le_coprimeInertAuxiliaryPrimes_card
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    ∀ᶠ t : ℕ in atTop,
      OddMediumParameters.oddTensorDepth t ≤
        (coprimeInertAuxiliaryPrimes ell J t).card := by
  filter_upwards
      [eventually_add_oddTensorDepth_le_inertAuxiliaryPrimes_card ell
        (Ideal.absNorm J + 1)] with t hsupply
  have hbad := badInertAuxiliaryPrimes_card_le ell J hJ t
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := inertAuxiliaryPrimes ell t)
    (p := fun q => q.Coprime (Ideal.absNorm J))
  change
    (coprimeInertAuxiliaryPrimes ell J t).card +
        ((inertAuxiliaryPrimes ell t).filter
          fun q => ¬q.Coprime (Ideal.absNorm J)).card =
      (inertAuxiliaryPrimes ell t).card at hpartition
  omega

theorem eventually_selectedCoprimeInertAuxiliaryPrimes_card
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    ∀ᶠ t : ℕ in atTop,
      (selectedCoprimeInertAuxiliaryPrimes ell J t).card =
        OddMediumParameters.oddTensorDepth t := by
  filter_upwards
      [eventually_oddTensorDepth_le_coprimeInertAuxiliaryPrimes_card ell J hJ]
      with t ht
  exact selectedCoprimeInertAuxiliaryPrimes_card ell ht

/-! ## Inherited arithmetic properties -/

theorem selectedCoprimeInertAuxiliaryPrimes_prime
    {J : Ideal (𝓞 K)} {t q : ℕ}
    (hq : q ∈ selectedCoprimeInertAuxiliaryPrimes ell J t) : q.Prime :=
  inertAuxiliaryPrimes_prime ell
    (selectedCoprimeInertAuxiliaryPrimes_subset ell J t hq)

theorem selectedCoprimeInertAuxiliaryPrimes_lt
    {J : Ideal (𝓞 K)} {t q : ℕ}
    (hq : q ∈ selectedCoprimeInertAuxiliaryPrimes ell J t) : q < t :=
  inertAuxiliaryPrimes_lt ell
    (selectedCoprimeInertAuxiliaryPrimes_subset ell J t hq)

theorem selectedCoprimeInertAuxiliaryPrimes_modEq
    {J : Ideal (𝓞 K)} {t q : ℕ}
    (hq : q ∈ selectedCoprimeInertAuxiliaryPrimes ell J t) :
    q % ell = inertResidue ell :=
  inertAuxiliaryPrimes_modEq ell
    (selectedCoprimeInertAuxiliaryPrimes_subset ell J t hq)

theorem selectedCoprimeInertAuxiliaryPrimes_coprime_absNorm
    {J : Ideal (𝓞 K)} {t q : ℕ}
    (hq : q ∈ selectedCoprimeInertAuxiliaryPrimes ell J t) :
    q.Coprime (Ideal.absNorm J) :=
  ((mem_coprimeInertAuxiliaryPrimes (ell := ell)).mp
    (selectedCoprimeInertAuxiliaryPrimes_subset_filtered ell J t hq)).2

theorem selectedCoprimeInertAuxiliaryPrimes_coprime_primaryRaySupport
    {J : Ideal (𝓞 K)} {t q : ℕ}
    (hq : q ∈ selectedCoprimeInertAuxiliaryPrimes ell J t) :
    q.Coprime (ell ^ (2 * ell)) :=
  inertAuxiliaryPrimes_coprime_primaryRaySupport ell
    (selectedCoprimeInertAuxiliaryPrimes_subset ell J t hq)

theorem selectedCoprimeInertAuxiliaryPrimes_pairwise_coprime
    (J : Ideal (𝓞 K)) (t : ℕ) :
    (selectedCoprimeInertAuxiliaryPrimes ell J t : Set ℕ).Pairwise
      Nat.Coprime :=
  (inertAuxiliaryPrimes_pairwise_coprime ell t).mono
    (selectedCoprimeInertAuxiliaryPrimes_subset ell J t)

theorem selectedCoprimeInertAuxiliaryPrimes_prod_le_four_pow
    (J : Ideal (𝓞 K)) (t : ℕ) :
    (selectedCoprimeInertAuxiliaryPrimes ell J t).prod id ≤ 4 ^ t := by
  calc
    (selectedCoprimeInertAuxiliaryPrimes ell J t).prod id ≤
        (inertAuxiliaryPrimes ell t).prod id := by
      apply Finset.prod_le_prod_of_subset_of_one_le
        (selectedCoprimeInertAuxiliaryPrimes_subset ell J t)
      · intro q hq
        exact Nat.zero_le q
      · intro q hq _
        exact (inertAuxiliaryPrimes_prime ell hq).one_le
    _ ≤ 4 ^ t := inertAuxiliaryPrimes_prod_le_four_pow ell t

theorem selectedCoprimeInertAuxiliaryPrimes_prod_le_modulusBound
    (J : Ideal (𝓞 K)) (t : ℕ) :
    (selectedCoprimeInertAuxiliaryPrimes ell J t).prod id ≤
      OddMediumParameters.oddAuxiliaryModulusBound t := by
  apply OddMediumParameters.prod_auxiliaryPrimes_le_modulusBound
    (selectedCoprimeInertAuxiliaryPrimes ell J t)
    (selectedCoprimeInertAuxiliaryPrimes_card_le ell J t)
  intro q hq
  exact (selectedCoprimeInertAuxiliaryPrimes_lt ell hq).le

theorem selectedCoprimeInertAuxiliaryPrimes_span_isPrime
    {J : Ideal (𝓞 K)} {t q : ℕ}
    (hq : q ∈ selectedCoprimeInertAuxiliaryPrimes ell J t) :
    (Ideal.span {(q : 𝓞 K)}).IsPrime :=
  inertAuxiliaryPrimes_span_isPrime ell (K := K)
    (selectedCoprimeInertAuxiliaryPrimes_subset ell J t hq)

theorem selectedCoprimeInertAuxiliaryPrimes_quotient_units_isCyclic
    {J : Ideal (𝓞 K)} {t q : ℕ}
    (hq : q ∈ selectedCoprimeInertAuxiliaryPrimes ell J t) :
    IsCyclic ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) :=
  inertAuxiliaryPrimes_quotient_units_isCyclic ell (K := K)
    (selectedCoprimeInertAuxiliaryPrimes_subset ell J t hq)

theorem selectedCoprimeInertAuxiliaryPrimes_natCard_powerClass
    {J : Ideal (𝓞 K)} {t q : ℕ}
    (hq : q ∈ selectedCoprimeInertAuxiliaryPrimes ell J t) :
    Nat.card (NumberFieldLargerSieve.PowerClass
      ((𝓞 K ⧸ Ideal.span {(q : 𝓞 K)})ˣ) ell) = ell :=
  inertAuxiliaryPrimes_natCard_powerClass ell (K := K)
    (selectedCoprimeInertAuxiliaryPrimes_subset ell J t hq)

end

end Erdos980.ElliottTail.OddFilteredInertPrimes
