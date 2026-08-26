import ErdosProblems.Erdos796.PrimeAugmentation
import ErdosProblems.Erdos796.SmoothStructural

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Smooth fibres together with the prime-tail budget

This module is the finite bridge between the two normal forms in the
structural reduction.  It filters the large-prime cofactor fibres to their
`Z`-smooth members, collision-cleans them, compresses quotient buckets, and
then adjoins the prime tail `(Z,j]`.  The resulting family is compatible, so
the smooth contribution plus the entire prime-tail budget is bounded by
`G(n)`, apart from the exact collision-cleaning loss `R^4`.
-/

namespace Erdos796

open scoped BigOperators

namespace SmoothAugmentation

open PruningArithmetic SmoothFiberCross BucketCompression CollisionCleaning

/-- The `Z`-smooth part of the cofactor fibre attached to `q`. -/
noncomputable def smoothCofactorFiber
    (A : Finset ℕ) (R Z q : ℕ) : Finset ℕ := by
  classical
  exact (cofactorFiber A R q).filter (ZSmooth Z)

@[simp]
theorem mem_smoothCofactorFiber
    {A : Finset ℕ} {R Z q u : ℕ} :
    u ∈ smoothCofactorFiber A R Z q ↔
      u ∈ positiveIcc R ∧ q * u ∈ A ∧ ZSmooth Z u := by
  classical
  simp [smoothCofactorFiber, and_assoc]

theorem smoothCofactorFiber_subset_cofactorFiber
    (A : Finset ℕ) (R Z q : ℕ) :
    smoothCofactorFiber A R Z q ⊆ cofactorFiber A R q := by
  classical
  exact Finset.filter_subset _ _

theorem smoothCofactorFiber_subset_range
    (A : Finset ℕ) (R Z q : ℕ) :
    smoothCofactorFiber A R Z q ⊆ positiveIcc R :=
  (smoothCofactorFiber_subset_cofactorFiber A R Z q).trans
    (cofactorFiber_subset A R q)

theorem smoothCofactorFiber_isSmooth
    {A : Finset ℕ} {R Z q u : ℕ}
    (hu : u ∈ smoothCofactorFiber A R Z q) : ZSmooth Z u :=
  (mem_smoothCofactorFiber.mp hu).2.2

/-- Distinct smooth cofactor fibres retain the cross-compatibility of the
full cofactor fibres. -/
theorem smoothCofactorFibers_crossCompatibleOn
    {n R Z : ℕ} {A Qs : Finset ℕ}
    (hA : Admissible n A)
    (hprime : ∀ q ∈ Qs, q.Prime)
    (hlarge : ∀ q ∈ Qs, R < q) :
    CrossCompatibleOn Qs (smoothCofactorFiber A R Z) := by
  intro q hq Q hQ hneq m
  exact (productRepCount_mono
      (smoothCofactorFiber_subset_cofactorFiber A R Z q)
      (smoothCofactorFiber_subset_cofactorFiber A R Z Q)).trans
    (cofactorFibers_crossCompatibleOn hA hprime hlarge q hq Q hQ hneq m)

/-- Collision-clean the smooth fibres, with the same exact `R^4` loss. -/
theorem exists_cleaned_smoothCofactorFibers
    {n R Z : ℕ} {A Qs : Finset ℕ}
    (hA : Admissible n A)
    (hprime : ∀ q ∈ Qs, q.Prime)
    (hlarge : ∀ q ∈ Qs, R < q) :
    ∃ S : ℕ → Finset ℕ,
      (∀ q ∈ Qs, S q ⊆ smoothCofactorFiber A R Z q) ∧
      (∀ i ∈ Qs, ∀ j ∈ Qs, ∀ m : ℕ,
        productRepCount (S i) (S j) m ≤ 2) ∧
      (∑ q ∈ Qs,
        ((smoothCofactorFiber A R Z q).card - (S q).card) ≤ R ^ 4) := by
  apply exists_compatible_cleaning
  · intro q _
    exact smoothCofactorFiber_subset_range A R Z q
  · exact smoothCofactorFibers_crossCompatibleOn hA hprime hlarge

/-- Bucket compression preserves `Z`-smoothness. -/
theorem compressedFamily_isSmooth
    {Z : ℕ} {Q : Finset ℕ} {bucket : ℕ → ℕ}
    {S : ℕ → Finset ℕ}
    (hSmooth : ∀ q ∈ Q, ∀ x ∈ S q, ZSmooth Z x) :
    ∀ j, ∀ x ∈ compressedFamily Q bucket S j, ZSmooth Z x := by
  intro j x hx
  by_cases hj : j ∈ bucketIndices Q bucket
  · rw [compressedFamily_eq_of_mem hj] at hx
    exact hSmooth _ (representative_mem hj) x hx
  · rw [compressedFamily_eq_empty_of_not_mem hj] at hx
    simp at hx

/-- The weighted number of primes in `(Z,j]` available across all quotient
buckets. -/
def primeTailScore (n Z : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 n.sqrt,
    bucketCount n j * (newPrimes Z j).card

/-- Augmentation splits its model score exactly into the old score and the
prime-tail budget. -/
theorem modelScore_primeAugmentation
    {n Z : ℕ} {S : ℕ → Finset ℕ}
    (hSrange : ∀ j, S j ⊆ positiveIcc j)
    (hSmooth : ∀ j, ∀ x ∈ S j, ZSmooth Z x) :
    modelScore n (primeAugmentation Z S) =
      modelScore n S + primeTailScore n Z := by
  unfold modelScore primeTailScore
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [card_primeAugmentation hSrange hSmooth]
  exact Nat.mul_add _ _ _

/-- For the actual large-prime quotient buckets, each bucket multiplicity is
exactly `bucketCount`. -/
theorem largePrime_bucketMultiplicity_eq_bucketCount (n j : ℕ) :
    bucketMultiplicity (largePrimes n) (fun q => n / q) j =
      bucketCount n j := by
  simp [bucketMultiplicity, bucketFiber, bucketCount, largePrimes,
    Finset.filter_filter]

/-- The compressed score dominates the total size of the cleaned fibres for
the actual large-prime quotient buckets. -/
theorem sum_cleaned_le_modelScore
    {n : ℕ} {S : ℕ → Finset ℕ}
    (_hrange : ∀ q ∈ largePrimes n, S q ⊆ positiveIcc (n / q)) :
    ∑ q ∈ largePrimes n, (S q).card ≤
      modelScore n
        (compressedFamily (largePrimes n) (fun q => n / q) S) := by
  let V := compressedFamily (largePrimes n) (fun q => n / q) S
  calc
    ∑ q ∈ largePrimes n, (S q).card ≤
        ∑ q ∈ largePrimes n, (V (n / q)).card := by
      apply Finset.sum_le_sum
      intro q hq
      have hj : n / q ∈
          bucketIndices (largePrimes n) (fun r => n / r) :=
        mem_bucketIndices.mpr ⟨q, hq, rfl⟩
      rw [show V (n / q) =
          S (representative (largePrimes n) (fun r => n / r) S (n / q)) by
        exact compressedFamily_eq_of_mem hj]
      exact card_le_representative hj hq rfl
    _ = modelScore n V := sum_primes_eq_modelScore n V

/-- Main finite estimate: the smooth normal form together with the complete
prime-tail budget is absorbed by a single compatible model family, with only
the exact collision-cleaning loss. -/
theorem smooth_plus_primeTail_le_G_add_cleaning
    {n R Z : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hR : R ≤ n.sqrt) :
    (∑ q ∈ largePrimes n,
        (smoothCofactorFiber A R Z q).card) + primeTailScore n Z ≤
      G n + R ^ 4 := by
  obtain ⟨S, hSsub, hScompat, hcost⟩ :=
    exists_cleaned_smoothCofactorFibers hA
      (fun q hq => SmoothStructural.largePrimes_are_prime hq)
      (fun q hq => SmoothStructural.largePrime_gt_cofactorRange hR hq)
  let V := compressedFamily (largePrimes n) (fun q => n / q) S
  let U := primeAugmentation Z V
  have hSrange : ∀ q ∈ largePrimes n,
      S q ⊆ positiveIcc (n / q) := by
    intro q hq
    exact (hSsub q hq).trans
      ((smoothCofactorFiber_subset_cofactorFiber A R Z q).trans
        (SmoothStructural.cofactorFiber_subset_quotient hA hq))
  have hV : Compatible V := compatible_compressedFamily hSrange hScompat
  have hVsmooth : ∀ j, ∀ x ∈ V j, ZSmooth Z x := by
    apply compressedFamily_isSmooth
    intro q hq x hx
    exact smoothCofactorFiber_isSmooth (hSsub q hq hx)
  have hU : Compatible U := compatible_primeAugmentation hV hVsmooth
  have hscore : modelScore n U = modelScore n V + primeTailScore n Z :=
    modelScore_primeAugmentation hV.1 hVsmooth
  have hcleaned :
      ∑ q ∈ largePrimes n, (S q).card ≤ modelScore n V :=
    sum_cleaned_le_modelScore hSrange
  have hsplit :
      ∑ q ∈ largePrimes n,
          (smoothCofactorFiber A R Z q).card =
        (∑ q ∈ largePrimes n,
          ((smoothCofactorFiber A R Z q).card - (S q).card)) +
        ∑ q ∈ largePrimes n, (S q).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hcard := Finset.card_le_card (hSsub q hq)
    omega
  have hmodel : modelScore n U ≤ G n := modelScore_le_G hU n
  rw [hsplit]
  omega

end SmoothAugmentation

end Erdos796
