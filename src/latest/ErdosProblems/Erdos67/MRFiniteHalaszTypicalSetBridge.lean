import ErdosProblems.Erdos67.MRFiniteHalaszTypicalDyadic

/-!
# Bridge between the finite Halasz and MRT typical sets

The finite Halasz factorization describes two selected prime bands as the
complementary predicates `not P₁ and P₂` and `not P₁ and not P₂`.  The MRT
reduction instead uses `typicalFactorizationSet` for a finite set of closed
prime intervals.  This file identifies the two descriptions exactly.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

open MRHalaszBands

/-- The first Halasz predicate is the complement of the union of two prime
blocks. -/
def mrTwoBlockOutside (I₁ I₂ : ℕ × ℕ) (p : ℕ) : Prop :=
  p ∉ primesInBlock I₁ ∧ p ∉ primesInBlock I₂

/-- The second Halasz predicate distinguishes the first block inside that
union. -/
def mrTwoBlockFirst (I₁ : ℕ × ℕ) (p : ℕ) : Prop :=
  p ∈ primesInBlock I₁

instance (I₁ I₂ : ℕ × ℕ) : DecidablePred (mrTwoBlockOutside I₁ I₂) :=
  fun p ↦ Classical.propDecidable (mrTwoBlockOutside I₁ I₂ p)

instance (I₁ : ℕ × ℕ) : DecidablePred (mrTwoBlockFirst I₁) :=
  fun p ↦ Classical.propDecidable (mrTwoBlockFirst I₁ p)

/-- Prime-factor membership through `Nat.primeFactors` is the same as the
divisibility formulation used by MRT, for positive integers. -/
theorem hasPrimeFactor_mem_primesInBlock_iff
    (I : ℕ × ℕ) {n : ℕ} (hn : 0 < n) :
    HasPrimeFactor (fun p ↦ p ∈ primesInBlock I) n ↔
      HasPrimeFactorInBlock I n := by
  rw [hasPrimeFactor_iff]
  constructor
  · rintro ⟨p, hpFactors, hpI⟩
    exact ⟨p, hpI, Nat.dvd_of_mem_primeFactors hpFactors⟩
  · rintro ⟨p, hpI, hpn⟩
    exact ⟨p, Nat.mem_primeFactors.mpr
      ⟨(mem_primesInBlock.mp hpI).1, hpn, hn.ne'⟩, hpI⟩

/-- Extensional predicates give the same finite prime-factor condition. -/
theorem hasPrimeFactor_congr
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    {n : ℕ} (hPQ : ∀ p, P p ↔ Q p) :
    HasPrimeFactor P n ↔ HasPrimeFactor Q n := by
  unfold HasPrimeFactor
  have hfilter : n.primeFactors.filter P = n.primeFactors.filter Q := by
    ext p
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ ↦ hPQ p
  rw [hfilter]

/-- The positive complementary band is exactly the first prime block. -/
theorem hasPrimeFactor_not_outside_and_first_iff
    (I₁ I₂ : ℕ × ℕ) {n : ℕ} (hn : 0 < n) :
    HasPrimeFactor
        (fun p ↦ ¬mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) n ↔
      HasPrimeFactorInBlock I₁ n := by
  rw [← hasPrimeFactor_mem_primesInBlock_iff I₁ hn]
  apply hasPrimeFactor_congr
  intro p
  constructor
  · exact fun hp ↦ hp.2
  · intro hp
    refine ⟨?_, hp⟩
    unfold mrTwoBlockOutside
    intro houtside
    exact houtside.1 hp

/-- For disjoint blocks, the negative complementary band is exactly the
second prime block. -/
theorem hasPrimeFactor_not_outside_and_not_first_iff
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {n : ℕ} (hn : 0 < n) :
    HasPrimeFactor
        (fun p ↦ ¬mrTwoBlockOutside I₁ I₂ p ∧ ¬mrTwoBlockFirst I₁ p) n ↔
      HasPrimeFactorInBlock I₂ n := by
  rw [← hasPrimeFactor_mem_primesInBlock_iff I₂ hn]
  apply hasPrimeFactor_congr
  intro p
  have hnotBoth : ¬(p ∈ primesInBlock I₁ ∧ p ∈ primesInBlock I₂) := by
    intro hp
    exact Finset.disjoint_left.mp hdisj hp.1 hp.2
  simp only [mrTwoBlockOutside, mrTwoBlockFirst, not_and_or]
  tauto

/-- On the dyadic packet `(Y,2Y]`, the actual MRT two-block typical set is
exactly the finite Halasz complementary-band set.  The larger cutoff `Z`
does not alter the packet once `2Y ≤ Z`. -/
theorem dyadicRestrictedSupport_twoBlockTypical_eq_finiteHalasz
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {Y Z : ℕ} (hY : 0 < Y) (hYZ : 2 * Y ≤ Z) :
    dyadicRestrictedSupport
        (typicalFactorizationSet {I₁, I₂} Z) Y =
      finiteHalaszTypicalDyadicSet Y
        (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁) := by
  ext n
  simp only [dyadicRestrictedSupport, Finset.mem_inter,
    Finset.mem_Ioc, mem_typicalFactorizationSet,
    finiteHalaszTypicalDyadicSet, Finset.mem_filter]
  constructor
  · rintro ⟨hpacket, hnOne, hnZ, htyp⟩
    have hn : 0 < n := hY.trans hpacket.1
    have htyp₁ : HasPrimeFactorInBlock I₁ n := by
      exact htyp I₁ (by simp)
    have htyp₂ : HasPrimeFactorInBlock I₂ n := by
      exact htyp I₂ (by simp)
    exact ⟨hpacket,
      (hasPrimeFactor_not_outside_and_first_iff I₁ I₂ hn).2 htyp₁,
      (hasPrimeFactor_not_outside_and_not_first_iff hdisj hn).2 htyp₂⟩
  · rintro ⟨hpacket, htyp₁, htyp₂⟩
    have hn : 0 < n := hY.trans hpacket.1
    have hnOne : 1 ≤ n := hn
    have hnZ : n ≤ Z := hpacket.2.trans hYZ
    refine ⟨hpacket, hnOne, hnZ, ?_⟩
    intro I hI
    simp only [Finset.mem_insert, Finset.mem_singleton] at hI
    rcases hI with hI | hI
    · simpa only [hI] using
        (hasPrimeFactor_not_outside_and_first_iff I₁ I₂ hn).1 htyp₁
    · simpa only [hI] using
        (hasPrimeFactor_not_outside_and_not_first_iff hdisj hn).1 htyp₂

/-- Polynomial-level form of the exact two-block support bridge. -/
theorem dyadicVerticalDirichletPolynomial_twoBlockTypical_eq_finiteHalasz
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    (f : ℕ → ℂ) {Y Z : ℕ} (hY : 0 < Y) (hYZ : 2 * Y ≤ Z)
    (t : ℝ) :
    dyadicVerticalDirichletPolynomial
        (typicalFactorizationSet {I₁, I₂} Z) f Y t =
      dyadicVerticalDirichletPolynomial
        (finiteHalaszTypicalDyadicSet Y
          (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) f Y t := by
  unfold dyadicVerticalDirichletPolynomial
  rw [dyadicRestrictedSupport_twoBlockTypical_eq_finiteHalasz
    hdisj hY hYZ]
  unfold dyadicRestrictedSupport finiteHalaszTypicalDyadicSet
  rw [Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]

end

end Erdos67
