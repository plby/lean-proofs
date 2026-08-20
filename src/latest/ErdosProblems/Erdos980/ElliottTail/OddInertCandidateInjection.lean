import ErdosProblems.Erdos980.ElliottTail.FixedRayCellCandidateData
import ErdosProblems.Erdos980.ElliottTail.OddCellGeometry
import ErdosProblems.Erdos980.ElliottTail.OddInertGeneratorMembership
import ErdosProblems.Erdos980.ElliottTail.NormSiftedInjection

/-!
# Exceptional odd-prime generators as conductor-norm sieve candidates

This file turns the exact tensor-cell membership proved in
`OddInertGeneratorMembership` into an injection into the literal finite
candidate family of `FixedRayCellCandidateData`.  It also proves the two
norm identities needed by the sieve:

* every point in the common height region has conductor norm at most `x`;
* the point attached to an exceptional rational prime `p` has conductor
  norm exactly `p`.

Consequently the part of a correction/unit fibre whose conductors do not
belong to the selected rational sieve-prime interval injects into the
unit-weight norm-sifted mass.
-/

open Filter
open scoped BigOperators NumberField nonZeroDivisors Pointwise

noncomputable section

namespace Erdos980.ElliottTail.OddInertCandidateInjection

open NumberField
open NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open IdealGeneratorCongruenceCount
open RayPrincipalizationHeight
open RayNormPrimeSieve
open FixedRayCellCandidateData
open OddCellGeometry
open OddInertAuxiliaryPrimes
open OddInertTensorCells
open OddInertGeneratorMembership
open NormSiftedInjection
open RationalPrimeGeneratorBridge
open RayPrincipalization

variable (ell : ℕ) [Fact ell.Prime]
variable (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

/-- The single height used for every conductor below `x` in one fixed
correction/unit fibre. -/
def exceptionalTagHeight
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (x : ℕ) : ℝ :=
  (((x * Ideal.absNorm
      (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) : ℕ) : ℝ) ^
    ((Module.finrank ℚ K : ℝ)⁻¹))

theorem exceptionalTagHeight_pos
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    {x : ℕ} (hx : 0 < x) :
    0 < exceptionalTagHeight ell K tag x := by
  unfold exceptionalTagHeight
  apply Real.rpow_pos_of_pos
  exact_mod_cast Nat.mul_pos hx (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr
      (nonZeroDivisors.coe_ne_zero (tagCorrectionIdeal ell K tag))))

theorem exceptionalTagHeight_pow_finrank
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    {x : ℕ} (hx : 0 < x) :
    exceptionalTagHeight ell K tag x ^ Module.finrank ℚ K =
      ((x * Ideal.absNorm
        (tagCorrectionIdeal ell K tag : Ideal (𝓞 K)) : ℕ) : ℝ) := by
  unfold exceptionalTagHeight
  apply Real.rpow_inv_natCast_pow
  · positivity
  · exact Module.finrank_pos.ne'

/-- Every realized point in a height region whose `d`-th power is
`x * N(J)` has conductor norm at most `x`. -/
theorem conductorNorm_le_of_mem_heightRegion
    (J : (Ideal (𝓞 K))⁰) (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f))
    (height : ℝ) (R : GeneratorRealization J f rayAllowed height)
    (x : ℕ) (hheight : 0 < height)
    (hheightPow : height ^ Module.finrank ℚ K =
      ((x * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ))
    (a : Candidate K J f rayAllowed height) :
    conductorNorm R a ≤ x := by
  rcases a.2.2.2 with ⟨y, hy, hya⟩
  rcases hy with ⟨z, hz, rfl⟩
  have hemb : mixedEmbedding K (R.generator a : K) = height • z := by
    apply (mixedEmbedding.stdBasis K).equivFunL.injective
    rw [map_smul, R.embedding_eq_point a]
    exact hya.symm
  have hnormLe : mixedEmbedding.norm (mixedEmbedding K (R.generator a : K)) ≤
      height ^ Module.finrank ℚ K := by
    rw [hemb, mixedEmbedding.norm_smul, abs_of_pos hheight]
    have hzNorm := (mem_normLeOne.mp hz).2
    nlinarith [mixedEmbedding.norm_nonneg z,
      pow_nonneg hheight.le (Module.finrank ℚ K)]
  have hprincipalReal :
      (Ideal.absNorm (Ideal.span ({R.generator a} : Set (𝓞 K))) : ℝ) ≤
        ((x * Ideal.absNorm (J : Ideal (𝓞 K)) : ℕ) : ℝ) := by
    rw [← mixedEmbedding_norm_ringOfIntegers K]
    exact hnormLe.trans_eq hheightPow
  have hprincipal :
      Ideal.absNorm (Ideal.span ({R.generator a} : Set (𝓞 K))) ≤
        x * Ideal.absNorm (J : Ideal (𝓞 K)) := by
    exact_mod_cast hprincipalReal
  rw [principalNorm_eq_conductorNorm_mul R a] at hprincipal
  exact Nat.le_of_mul_le_mul_right hprincipal
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (nonZeroDivisors.coe_ne_zero J)))

/-- The canonical full-cell candidate family at the common tag height has
conductor norm bounded by `x`. -/
theorem canonicalConductorNorm_le_x
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (f : ℕ) [NeZero f]
    (rayAllowed : Finset (index K → ZMod f))
    {x : ℕ} (hx : 0 < x)
    (a : Candidate K (tagCorrectionIdeal ell K tag) f rayAllowed
      (exceptionalTagHeight ell K tag x)) :
    conductorNorm
      (canonicalGeneratorRealization (K := K)
        (tagCorrectionIdeal ell K tag) f rayAllowed
        (exceptionalTagHeight ell K tag x)) a ≤ x := by
  apply conductorNorm_le_of_mem_heightRegion K
  · exact exceptionalTagHeight_pos ell K tag hx
  · exact exceptionalTagHeight_pow_finrank ell K tag hx

/-- The balanced generator in a fixed tag fibre lies in the common height
region for the ambient cutoff `x`. -/
theorem exceptionalBalancedGenerator_mem_tagHeight
    {t x : ℕ}
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K
          (exceptionalBalancedGenerator ell K t x p : K)) ∈
      exceptionalTagHeight ell K tag x • generatorNormRegion K := by
  have htag := (mem_exceptionalGeneratorFiber
    (ell := ell) (K := K)).mp hp
  have hi : (exceptionalGeneratorData ell K t x p).correctionIndex = tag.1 := by
    simpa only [exceptionalGeneratorTag] using congrArg Prod.fst htag
  have hpx : p.1 ≤ x := (mem_exceptionalPrimes.mp p.2).1.le
  have hmem := boundedGenerator_mem_commonNormRegion ell K
    (exceptionalGeneratorData ell K t x p) hpx
  simpa only [exceptionalBalancedGenerator, exceptionalTagHeight,
    tagCorrectionIdeal, hi] using hmem

/-- A member of a fixed tag fibre, encoded as a literal point of the exact
inert tensor ray cell and the common height region. -/
def exceptionalBalancedCandidate
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    Candidate K (tagCorrectionIdeal ell K tag) (inertTensorModulus Q)
      (inertPowerClassCoordinateCell ell K Q
        (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
        (tagCorrectionIdeal ell K tag) hcop
        (exceptionalBalancedPowerClassPattern
          ell K Q hQ tag hcop p₀ hp₀))
      (exceptionalTagHeight ell K tag x) := by
  classical
  let hprime : ∀ q ∈ Q, q.Prime :=
    fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq)
  let k := inertLocalUnitsCoordinateEmbedding K Q hprime
    (tagCorrectionIdeal ell K tag) hcop
    (exceptionalBalancedUnitTensor ell K Q hQ tag hcop p hp)
  refine ⟨⟨k, ?_⟩, ⟨
    (mixedEmbedding.stdBasis K).equivFunL
      (mixedEmbedding K (exceptionalBalancedGenerator ell K t x p : K)),
    ?_, ?_⟩⟩
  · exact exceptionalBalancedUnitTensor_mem_inertPowerClassCoordinateCell
      ell K hodd Q hQ tag hcop hp₀ hp
  · exact exceptionalBalancedGenerator_mem_tensorGeneratorCongruenceCell
      ell K Q hQ tag hcop p hp
  · exact exceptionalBalancedGenerator_mem_tagHeight ell K tag p hp

/-- The canonical realization of the exceptional point is the exceptional
balanced generator itself. -/
theorem exceptionalBalancedCandidate_generator
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    let rayAllowed := inertPowerClassCoordinateCell ell K Q
      (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
      (tagCorrectionIdeal ell K tag) hcop
      (exceptionalBalancedPowerClassPattern ell K Q hQ tag hcop p₀ hp₀)
    let R := canonicalGeneratorRealization (K := K)
      (tagCorrectionIdeal ell K tag) (inertTensorModulus Q) rayAllowed
      (exceptionalTagHeight ell K tag x)
    R.generator
        (exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ p hp) =
      exceptionalBalancedGenerator ell K t x p := by
  dsimp only
  apply RingOfIntegers.coe_injective (K := K)
  apply mixedEmbedding_injective K
  apply (mixedEmbedding.stdBasis K).equivFunL.injective
  let rayAllowed := inertPowerClassCoordinateCell ell K Q
    (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
    (tagCorrectionIdeal ell K tag) hcop
    (exceptionalBalancedPowerClassPattern ell K Q hQ tag hcop p₀ hp₀)
  let R := canonicalGeneratorRealization (K := K)
    (tagCorrectionIdeal ell K tag) (inertTensorModulus Q) rayAllowed
    (exceptionalTagHeight ell K tag x)
  let a := exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ p hp
  calc
    (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K (R.generator a : K)) = a.2.1 :=
      R.embedding_eq_point a
    _ = (mixedEmbedding.stdBasis K).equivFunL
        (mixedEmbedding K (exceptionalBalancedGenerator ell K t x p : K)) := rfl

/-- The conductor norm of the exceptional candidate is its original
rational prime. -/
theorem exceptionalBalancedCandidate_conductorNorm
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    let rayAllowed := inertPowerClassCoordinateCell ell K Q
      (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
      (tagCorrectionIdeal ell K tag) hcop
      (exceptionalBalancedPowerClassPattern ell K Q hQ tag hcop p₀ hp₀)
    let R := canonicalGeneratorRealization (K := K)
      (tagCorrectionIdeal ell K tag) (inertTensorModulus Q) rayAllowed
      (exceptionalTagHeight ell K tag x)
    conductorNorm R
        (exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ p hp) =
      p.1 := by
  dsimp only
  rw [conductorNorm,
    exceptionalBalancedCandidate_generator ell K hodd Q hQ tag hcop p₀ hp₀ p hp]
  let data := exceptionalGeneratorData ell K t x p
  have htag := (mem_exceptionalGeneratorFiber
    (ell := ell) (K := K)).mp hp
  have hi : data.correctionIndex = tag.1 := by
    simpa only [exceptionalGeneratorTag, data] using congrArg Prod.fst htag
  change Ideal.absNorm
      (Ideal.span ({data.balancedGenerator} : Set (𝓞 K))) /
        Ideal.absNorm (cyclotomicRayCorrection ell K tag.1) = p.1
  rw [data.balancedGenerator_span, map_mul, data.primeIdeal_absNorm, hi]
  simpa only [Nat.mul_comm] using Nat.mul_div_right p.1 (Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr
      (cyclotomicRayCorrection_ne_bot ell K tag.1)))

/-- The part of one tag fibre whose rational conductors do not themselves
belong to the selected sieve-prime set. -/
def survivingExceptionalGeneratorFiber
    {t x : ℕ}
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (sievePrimes : Finset ℕ) : Finset (ExceptionalPrime ell t x) := by
  classical
  exact (exceptionalGeneratorFiber ell K t x tag).filter
    fun p ↦ p.1 ∉ sievePrimes

@[simp] theorem mem_survivingExceptionalGeneratorFiber
    {t x : ℕ}
    {tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K}
    {sievePrimes : Finset ℕ} {p : ExceptionalPrime ell t x} :
    p ∈ survivingExceptionalGeneratorFiber ell K tag sievePrimes ↔
      p ∈ exceptionalGeneratorFiber ell K t x tag ∧
        p.1 ∉ sievePrimes := by
  classical
  simp [survivingExceptionalGeneratorFiber]

/-- Use the reference point as a harmless default away from the fixed tag
fibre, so the exceptional-candidate encoding is a total function. -/
def exceptionalBalancedCandidateTotal
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (p : ExceptionalPrime ell t x) :
    Candidate K (tagCorrectionIdeal ell K tag) (inertTensorModulus Q)
      (inertPowerClassCoordinateCell ell K Q
        (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
        (tagCorrectionIdeal ell K tag) hcop
        (exceptionalBalancedPowerClassPattern
          ell K Q hQ tag hcop p₀ hp₀))
      (exceptionalTagHeight ell K tag x) := by
  classical
  by_cases hp : p ∈ exceptionalGeneratorFiber ell K t x tag
  · exact exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ p hp
  · exact exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ p₀ hp₀

theorem exceptionalBalancedCandidateTotal_of_mem
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (p : ExceptionalPrime ell t x)
    (hp : p ∈ exceptionalGeneratorFiber ell K t x tag) :
    exceptionalBalancedCandidateTotal ell K hodd Q hQ tag hcop p₀ hp₀ p =
      exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ p hp := by
  classical
  simp only [exceptionalBalancedCandidateTotal, dif_pos hp]

theorem exceptionalBalancedCandidateTotal_injective_on_survivors
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (sievePrimes : Finset ℕ) :
    Set.InjOn
      (exceptionalBalancedCandidateTotal ell K hodd Q hQ tag hcop p₀ hp₀)
      (survivingExceptionalGeneratorFiber ell K (t := t) (x := x)
        tag sievePrimes :
        Set (ExceptionalPrime ell t x)) := by
  intro p hp q hq hpq
  have hp' := (mem_survivingExceptionalGeneratorFiber
    (ell := ell) (K := K)).mp hp
  have hq' := (mem_survivingExceptionalGeneratorFiber
    (ell := ell) (K := K)).mp hq
  have hpq' :
      exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ p hp'.1 =
        exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ q hq'.1 := by
    calc
      exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ p hp'.1 =
          exceptionalBalancedCandidateTotal ell K hodd Q hQ tag hcop p₀ hp₀ p :=
        (exceptionalBalancedCandidateTotal_of_mem ell K hodd Q hQ tag hcop
          p₀ hp₀ p hp'.1).symm
      _ = exceptionalBalancedCandidateTotal ell K hodd Q hQ tag hcop p₀ hp₀ q := hpq
      _ = exceptionalBalancedCandidate ell K hodd Q hQ tag hcop p₀ hp₀ q hq'.1 :=
        exceptionalBalancedCandidateTotal_of_mem ell K hodd Q hQ tag hcop
          p₀ hp₀ q hq'.1
  have hgen : exceptionalBalancedGenerator ell K t x p =
      exceptionalBalancedGenerator ell K t x q := by
    rw [← exceptionalBalancedCandidate_generator ell K hodd Q hQ tag hcop
      p₀ hp₀ p hp'.1,
      ← exceptionalBalancedCandidate_generator ell K hodd Q hQ tag hcop
        p₀ hp₀ q hq'.1]
    exact congrArg
      (canonicalGeneratorRealization (K := K)
        (tagCorrectionIdeal ell K tag) (inertTensorModulus Q)
        (inertPowerClassCoordinateCell ell K Q
          (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
          (tagCorrectionIdeal ell K tag) hcop
          (exceptionalBalancedPowerClassPattern
            ell K Q hQ tag hcop p₀ hp₀))
        (exceptionalTagHeight ell K tag x)).generator hpq'
  exact exceptionalBalancedGenerator_injective_on_fiber ell K tag hp'.1 hq'.1 hgen

/-- The surviving part of one nonempty correction/unit fibre injects into
the literal unit-weight norm-sifted mass of the canonical fixed-ray data. -/
theorem survivingExceptionalGeneratorFiber_card_le_normSiftedMass
    (hodd : Odd ell) {t x : ℕ} (Q : Finset ℕ)
    [NeZero (inertTensorModulus Q)]
    (hQ : Q ⊆ inertAuxiliaryPrimes ell t)
    (tag : CyclotomicRayCorrectionIndex ell K × UnitResidueImage ell K)
    (hcop : ∀ q ∈ Q, q.Coprime
      (Ideal.absNorm (tagCorrectionIdeal ell K tag : Ideal (𝓞 K))))
    (p₀ : ExceptionalPrime ell t x)
    (hp₀ : p₀ ∈ exceptionalGeneratorFiber ell K t x tag)
    (sievePrimes : Finset ℕ)
    (hsievePrime : ∀ q ∈ sievePrimes, q.Prime)
    (j unitResidueCount : ℕ)
    (hrootPos : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      0 < (coordinateAlgebraNormResidueSystem K
        (tagCorrectionIdeal ell K tag)).rootCount K p)
    (hrootLt : ∀ p, p.Prime → p ∣ sievePrimes.prod id →
      (coordinateAlgebraNormResidueSystem K
        (tagCorrectionIdeal ell K tag)).rootCount K p <
          p ^ Nat.card (index K))
    (hx : 0 < x) :
    let rayAllowed := inertPowerClassCoordinateCell ell K Q
      (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
      (tagCorrectionIdeal ell K tag) hcop
      (exceptionalBalancedPowerClassPattern ell K Q hQ tag hcop p₀ hp₀)
    let D := canonicalData (K := K) (tagCorrectionIdeal ell K tag)
      (inertTensorModulus Q) rayAllowed (exceptionalTagHeight ell K tag x)
      x (canonicalConductorNorm_le_x ell K tag (inertTensorModulus Q)
        rayAllowed hx) sievePrimes hsievePrime ell j unitResidueCount
      hrootPos hrootLt
    ((survivingExceptionalGeneratorFiber ell K (t := t) (x := x)
      tag sievePrimes).card : ℝ) ≤ normSiftedMass D := by
  dsimp only
  let rayAllowed := inertPowerClassCoordinateCell ell K Q
    (fun q hq ↦ inertAuxiliaryPrimes_prime ell (hQ hq))
    (tagCorrectionIdeal ell K tag) hcop
    (exceptionalBalancedPowerClassPattern ell K Q hQ tag hcop p₀ hp₀)
  let R := canonicalGeneratorRealization (K := K)
    (tagCorrectionIdeal ell K tag) (inertTensorModulus Q) rayAllowed
    (exceptionalTagHeight ell K tag x)
  let D := canonicalData (K := K) (tagCorrectionIdeal ell K tag)
    (inertTensorModulus Q) rayAllowed (exceptionalTagHeight ell K tag x)
    x (canonicalConductorNorm_le_x ell K tag (inertTensorModulus Q)
      rayAllowed hx) sievePrimes hsievePrime ell j unitResidueCount
    hrootPos hrootLt
  apply card_le_normSiftedMass_of_injection D
    (survivingExceptionalGeneratorFiber ell K (t := t) (x := x)
      tag sievePrimes)
    (exceptionalBalancedCandidateTotal ell K hodd Q hQ tag hcop p₀ hp₀)
  · exact exceptionalBalancedCandidateTotal_injective_on_survivors
      ell K hodd Q hQ tag hcop p₀ hp₀ sievePrimes
  · intro p hp
    change exceptionalBalancedCandidateTotal ell K hodd Q hQ tag hcop p₀ hp₀ p ∈
      candidateFinset (K := K) (tagCorrectionIdeal ell K tag)
        (inertTensorModulus Q) rayAllowed (exceptionalTagHeight ell K tag x)
        (fun k _ ↦ generatorCongruenceCell_inter_generatorNormRegion_finite
          (tagCorrectionIdeal ell K tag) (inertTensorModulus Q) k
          (exceptionalTagHeight ell K tag x))
    exact mem_candidateFinset _ _ _ _ _ _
  · intro p hp
    rfl
  · intro p hp q hq hqdiv
    have hp' := (mem_survivingExceptionalGeneratorFiber
      (ell := ell) (K := K)).mp hp
    have hcond : D.conductorNorm
        (exceptionalBalancedCandidateTotal ell K hodd Q hQ tag hcop p₀ hp₀ p) =
        p.1 := by
      change conductorNorm R
          (exceptionalBalancedCandidateTotal ell K hodd Q hQ tag hcop p₀ hp₀ p) =
        p.1
      rw [exceptionalBalancedCandidateTotal_of_mem ell K hodd Q hQ tag hcop
        p₀ hp₀ p hp'.1]
      exact exceptionalBalancedCandidate_conductorNorm ell K hodd Q hQ tag hcop
        p₀ hp₀ p hp'.1
    rw [hcond] at hqdiv
    have hpeq : q = p.1 := (Nat.prime_dvd_prime_iff_eq
      (hsievePrime q hq) (exceptionalPrime_eligible ell t x p).1).mp hqdiv
    exact hp'.2 (hpeq ▸ hq)

end Erdos980.ElliottTail.OddInertCandidateInjection
