import ErdosProblems.Erdos980.ElliottTail.NumberFieldLargerSieve
import ErdosProblems.Erdos980.ElliottTail.OddPowerReciprocity
import ErdosProblems.Erdos980.ElliottTail.RayPrincipalization

/-!
# Finite correction-indexed tensors for odd prime exponents

This file joins the three algebraic inputs for the odd-prime medium range:

* finite ray principalization chooses `(alpha) = P * C_i`, with `alpha`
  primary and prime to `ell`;
* Eisenstein reciprocity identifies an ordinary local `ell`-power condition
  with `(alpha / q)_ell = (q / C_i)_ell`;
* subtracting the correction symbol produces a tensor-valued code whose zero
  fibre contains exactly the simultaneous local power-residue candidates.

The correction index is finite.  It is therefore legitimate to split the
candidate prime conductors into these finitely many fibres before applying
the tensor larger sieve.
-/

open scoped NumberField nonZeroDivisors

namespace Erdos980.ElliottTail.OddPrimeTensorBridge

noncomputable section

open BernoulliRegular
open BernoulliRegular.Furtwaengler
open NumberField
open OddPowerReciprocity
open RayPrincipalization
open NumberFieldLargerSieve

variable (ell : ℕ) [Fact ell.Prime]
  (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {ell} ℚ K]

local notation "lambdaIdeal" =>
  Ideal.span ({FLT37.zetaSubOne ell K} : Set (𝓞 K))

private lemma lambdaIdeal_ne_bot : lambdaIdeal ≠ ⊥ := by
  intro h
  exact FLT37.zetaSubOne_ne_zero ell K
    (Ideal.span_singleton_eq_bot.mp h)

private lemma primaryModulus_ne_bot : lambdaIdeal ^ (2 * ell) ≠ ⊥ :=
  pow_ne_zero _ (lambdaIdeal_ne_bot ell K)

noncomputable local instance : Finite (𝓞 K ⧸ lambdaIdeal ^ (2 * ell)) :=
  Ring.HasFiniteQuotients.finiteQuotient (primaryModulus_ne_bot ell K)

noncomputable local instance : Fintype (𝓞 K ⧸ lambdaIdeal ^ (2 * ell)) :=
  Fintype.ofFinite _

noncomputable local instance :
    Fintype (CyclotomicRayCorrectionIndex ell K) :=
  Fintype.ofFinite _

/-! ## Canonical finite principalization choices -/

/-- The finite correction index selected for a nonzero ideal away from the
cyclotomic prime. -/
noncomputable def correctionIndexOf
    (P : (Ideal (𝓞 K))⁰)
    (hPL : lambdaIdeal ⊔ (P : Ideal (𝓞 K)) = ⊤) :
    CyclotomicRayCorrectionIndex ell K :=
  Classical.choose
    (exists_primary_generator_mul_cyclotomicRayCorrection ell K P hPL)

/-- A primary generator of `P` times its selected finite correction. -/
noncomputable def primaryGeneratorOf
    (P : (Ideal (𝓞 K))⁰)
    (hPL : lambdaIdeal ⊔ (P : Ideal (𝓞 K)) = ⊤) : 𝓞 K :=
  Classical.choose
    (Classical.choose_spec
      (exists_primary_generator_mul_cyclotomicRayCorrection ell K P hPL))

theorem primaryGeneratorOf_spec
    (P : (Ideal (𝓞 K))⁰)
    (hPL : lambdaIdeal ⊔ (P : Ideal (𝓞 K)) = ⊤) :
    FLT37.IsPrimary ell (K := K) (primaryGeneratorOf ell K P hPL) ∧
      IsPrimeToP (p := ell) (K := K) (primaryGeneratorOf ell K P hPL) ∧
      Ideal.span ({primaryGeneratorOf ell K P hPL} : Set (𝓞 K)) =
        (P : Ideal (𝓞 K)) *
          cyclotomicRayCorrection ell K (correctionIndexOf ell K P hPL) := by
  exact Classical.choose_spec
    (Classical.choose_spec
      (exists_primary_generator_mul_cyclotomicRayCorrection ell K P hPL))

/-! ## The correction-normalized symbol tensor -/

/-- One residue-symbol coordinate for every auxiliary test integer. -/
abbrev OddPrimeSymbolTensor (Q : Type*) := Q → ZMod ell

/-- The residue-symbol tensor of the selected primary generator, normalized
by the fixed ideal-class correction indexed by `i`.

For the selected correction `i = correctionIndexOf P`, reciprocity says this
coordinate is zero precisely when `q(t)` is an `ell`-th power at `P`. -/
noncomputable def normalizedSymbolCode
    {A Q : Type*} (q : Q → ℕ)
    (P : A → (Ideal (𝓞 K))⁰)
    (hPL : ∀ a, lambdaIdeal ⊔ (P a : Ideal (𝓞 K)) = ⊤)
    (i : CyclotomicRayCorrectionIndex ell K)
    (a : A) : OddPrimeSymbolTensor ell Q :=
  fun t =>
    pthSymbolAtInt_canonical (p := ell) (K := K)
        (primaryGeneratorOf ell K (P a) (hPL a)) (q t : ℤ) -
      pthSymbolAtIdeal_canonical (p := ell) (K := K) (q t : 𝓞 K)
        (cyclotomicRayCorrection ell K i)

/-- Candidate prime conductors for which every auxiliary integer is an
`ell`-th power modulo the corresponding rational prime. -/
noncomputable def simultaneousLocalPowerCandidates
    {A Q : Type*} [DecidableEq A] [Fintype Q]
    (S : Finset A) (r : A → ℕ) (q : Q → ℕ) : Finset A := by
  classical
  exact S.filter fun a =>
    ∀ t, ∃ b : ZMod (r a), b ^ ell = (q t : ZMod (r a))

@[simp] theorem mem_simultaneousLocalPowerCandidates
    {A Q : Type*} [DecidableEq A] [Fintype Q]
    {S : Finset A} {r : A → ℕ} {q : Q → ℕ} {a : A} :
    a ∈ simultaneousLocalPowerCandidates ell S r q ↔
      a ∈ S ∧ ∀ t, ∃ b : ZMod (r a),
        b ^ ell = (q t : ZMod (r a)) := by
  classical
  simp [simultaneousLocalPowerCandidates]

/-! ## Exact tensor-fibre bridge -/

section Candidates

variable {A Q : Type*} [DecidableEq A] [Fintype Q]
variable (P : A → (Ideal (𝓞 K))⁰)
variable (hPprime : ∀ a, (P a : Ideal (𝓞 K)).IsPrime)
variable (hPmax : ∀ a, (P a : Ideal (𝓞 K)).IsMaximal)
variable (hPL : ∀ a,
  Ideal.span ({FLT37.zetaSubOne ell K} : Set (𝓞 K)) ⊔
    (P a : Ideal (𝓞 K)) = ⊤)
variable (r : A → ℕ) (q : Q → ℕ)
variable (residueEquiv : ∀ a, ZMod (r a) ≃+* (𝓞 K ⧸ (P a : Ideal (𝓞 K))))

include hPprime hPmax residueEquiv

private abbrev alpha (a : A) : 𝓞 K :=
  primaryGeneratorOf ell K (P a) (hPL a)

private abbrev corrIndex (a : A) : CyclotomicRayCorrectionIndex ell K :=
  correctionIndexOf ell K (P a) (hPL a)

/-- For a fixed candidate, membership in its selected correction-normalized
zero tensor is exactly simultaneous ordinary power residuacity. -/
theorem normalizedSymbolCode_eq_zero_iff
    (hellOdd : Odd ell)
    (hqCoprime : ∀ a t, IsCoprimeToPAndAlphaInt
      (p := ell) (K := K) (q t : ℤ) (alpha ell K P hPL a))
    (hqNotMem : ∀ a t, (q t : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (hellDvd : ∀ a, ell ∣ Ideal.absNorm (P a : Ideal (𝓞 K)) - 1)
    (hellNotMem : ∀ a, (ell : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (a : A) :
    normalizedSymbolCode ell K q P hPL (corrIndex ell K P hPL a) a = 0 ↔
      ∀ t, ∃ b : ZMod (r a), b ^ ell = (q t : ZMod (r a)) := by
  letI : (P a : Ideal (𝓞 K)).IsPrime := hPprime a
  letI : (P a : Ideal (𝓞 K)).IsMaximal := hPmax a
  constructor
  · intro hzero t
    have hcoord := congrFun hzero t
    have heq :
        pthSymbolAtInt_canonical (p := ell) (K := K)
            (alpha ell K P hPL a) (q t : ℤ) =
          pthSymbolAtIdeal_canonical (p := ell) (K := K) (q t : 𝓞 K)
            (cyclotomicRayCorrection ell K (corrIndex ell K P hPL a)) := by
      exact sub_eq_zero.mp hcoord
    exact (zmodPower_iff_integerSymbol_eq_correction
      (K := K) hellOdd
      (P := (P a : Ideal (𝓞 K)))
      (C := cyclotomicRayCorrection ell K (corrIndex ell K P hPL a))
      (nonZeroDivisors.coe_ne_zero (P a))
      (cyclotomicRayCorrection_ne_bot ell K (corrIndex ell K P hPL a))
      (residueEquiv a)
      (primaryGeneratorOf_spec ell K (P a) (hPL a)).1
      (primaryGeneratorOf_spec ell K (P a) (hPL a)).2.1
      (primaryGeneratorOf_spec ell K (P a) (hPL a)).2.2
      (hqCoprime a t) (hqNotMem a t) (hellDvd a) (hellNotMem a)).mpr heq
  · intro hpowers
    funext t
    apply sub_eq_zero.mpr
    exact (zmodPower_iff_integerSymbol_eq_correction
      (K := K) hellOdd
      (P := (P a : Ideal (𝓞 K)))
      (C := cyclotomicRayCorrection ell K (corrIndex ell K P hPL a))
      (nonZeroDivisors.coe_ne_zero (P a))
      (cyclotomicRayCorrection_ne_bot ell K (corrIndex ell K P hPL a))
      (residueEquiv a)
      (primaryGeneratorOf_spec ell K (P a) (hPL a)).1
      (primaryGeneratorOf_spec ell K (P a) (hPL a)).2.1
      (primaryGeneratorOf_spec ell K (P a) (hPL a)).2.2
      (hqCoprime a t) (hqNotMem a t) (hellDvd a) (hellNotMem a)).mp
        (hpowers t)

/-- Exact membership equivalence with the finite correction-indexed tensor
zero fibre. -/
theorem mem_correctedZeroFiber_iff
    (hellOdd : Odd ell)
    (hqCoprime : ∀ a t, IsCoprimeToPAndAlphaInt
      (p := ell) (K := K) (q t : ℤ) (alpha ell K P hPL a))
    (hqNotMem : ∀ a t, (q t : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (hellDvd : ∀ a, ell ∣ Ideal.absNorm (P a : Ideal (𝓞 K)) - 1)
    (hellNotMem : ∀ a, (ell : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (S : Finset A) (a : A) :
    a ∈ correctedTensorPatternFiber S
        (corrIndex ell K P hPL)
        (normalizedSymbolCode ell K q P hPL)
        (0 : OddPrimeSymbolTensor ell Q) ↔
      a ∈ simultaneousLocalPowerCandidates ell S r q := by
  rw [mem_correctedTensorPatternFiber,
    mem_simultaneousLocalPowerCandidates]
  exact and_congr_right fun _ =>
    normalizedSymbolCode_eq_zero_iff ell K P hPprime hPmax hPL r q residueEquiv
      hellOdd hqCoprime hqNotMem hellDvd hellNotMem a

/-- Exact inclusion requested by the tensor sieve: every simultaneous local
power-residue candidate lies in the correction-indexed zero fibre. -/
theorem simultaneousLocalPowerCandidates_subset_correctedZeroFiber
    (hellOdd : Odd ell)
    (hqCoprime : ∀ a t, IsCoprimeToPAndAlphaInt
      (p := ell) (K := K) (q t : ℤ) (alpha ell K P hPL a))
    (hqNotMem : ∀ a t, (q t : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (hellDvd : ∀ a, ell ∣ Ideal.absNorm (P a : Ideal (𝓞 K)) - 1)
    (hellNotMem : ∀ a, (ell : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (S : Finset A) :
    simultaneousLocalPowerCandidates ell S r q ⊆
      correctedTensorPatternFiber S
        (corrIndex ell K P hPL)
        (normalizedSymbolCode ell K q P hPL)
        (0 : OddPrimeSymbolTensor ell Q) := by
  intro a ha
  exact (mem_correctedZeroFiber_iff ell K P hPprime hPmax hPL r q residueEquiv
    hellOdd hqCoprime hqNotMem hellDvd hellNotMem S a).mpr ha

/-- The inclusion above is in fact an equality.  This is the exact finite-set
interface used when the analytic argument counts the candidate conductors. -/
theorem simultaneousLocalPowerCandidates_eq_correctedZeroFiber
    (hellOdd : Odd ell)
    (hqCoprime : ∀ a t, IsCoprimeToPAndAlphaInt
      (p := ell) (K := K) (q t : ℤ) (alpha ell K P hPL a))
    (hqNotMem : ∀ a t, (q t : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (hellDvd : ∀ a, ell ∣ Ideal.absNorm (P a : Ideal (𝓞 K)) - 1)
    (hellNotMem : ∀ a, (ell : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (S : Finset A) :
    simultaneousLocalPowerCandidates ell S r q =
      correctedTensorPatternFiber S
        (corrIndex ell K P hPL)
        (normalizedSymbolCode ell K q P hPL)
        (0 : OddPrimeSymbolTensor ell Q) := by
  ext a
  exact (mem_correctedZeroFiber_iff ell K P hPprime hPmax hPL r q residueEquiv
    hellOdd hqCoprime hqNotMem hellDvd hellNotMem S a).symm

/-- Exact disjoint correction-fibre decomposition of the simultaneous local
power-residue count.  The summation type is finite by ray principalization. -/
theorem simultaneousLocalPowerCandidates_card_eq_sum_correctionFibers
    (hellOdd : Odd ell)
    (hqCoprime : ∀ a t, IsCoprimeToPAndAlphaInt
      (p := ell) (K := K) (q t : ℤ) (alpha ell K P hPL a))
    (hqNotMem : ∀ a t, (q t : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (hellDvd : ∀ a, ell ∣ Ideal.absNorm (P a : Ideal (𝓞 K)) - 1)
    (hellNotMem : ∀ a, (ell : 𝓞 K) ∉ (P a : Ideal (𝓞 K)))
    (S : Finset A) :
    (simultaneousLocalPowerCandidates ell S r q).card =
      ∑ i : CyclotomicRayCorrectionIndex ell K,
        (tensorPatternFiber
          (finiteCorrectionFiber S (corrIndex ell K P hPL) i)
          (normalizedSymbolCode ell K q P hPL i)
          (0 : OddPrimeSymbolTensor ell Q)).card := by
  rw [simultaneousLocalPowerCandidates_eq_correctedZeroFiber ell K P hPprime
    hPmax hPL r q residueEquiv hellOdd hqCoprime hqNotMem hellDvd hellNotMem S]
  exact correctedTensorPatternFiber_card_eq_sum S
    (corrIndex ell K P hPL) (normalizedSymbolCode ell K q P hPL)
    (0 : OddPrimeSymbolTensor ell Q)

end Candidates

end

end Erdos980.ElliottTail.OddPrimeTensorBridge
