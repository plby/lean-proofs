import ErdosProblems.Erdos796.PruningPartition
import ErdosProblems.Erdos796.PruningCounts
import ErdosProblems.Erdos796.SmoothAugmentation

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Counting the smooth pruning normal form

This file splits the smooth normal form according to whether its canonical
largest prime is at most or above `sqrt n`.  The small-prime part has the
elementary bound `pi(sqrt n) * Y^4`; the large-prime part embeds into the
`Z`-smooth cofactor fibres used by `SmoothAugmentation`.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

namespace NormalFormCounting

open PruningNormalForms PruningClassification PruningPartition
  SmoothFiberCross SmoothAugmentation

/-- Smooth-normal elements whose canonical largest prime is at most
`sqrt n`. -/
noncomputable def smoothNormalSmallPrime
    (n Y Z : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (smoothNormalPiece Y Z A).filter fun a =>
    largestPrimeFactor a ≤ n.sqrt

/-- Smooth-normal elements whose canonical largest prime exceeds `sqrt n`. -/
noncomputable def smoothNormalLargePrime
    (n Y Z : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (smoothNormalPiece Y Z A).filter fun a =>
    n.sqrt < largestPrimeFactor a

@[simp]
theorem mem_smoothNormalSmallPrime
    {n Y Z a : ℕ} {A : Finset ℕ} :
    a ∈ smoothNormalSmallPrime n Y Z A ↔
      a ∈ A ∧ IsSmoothNormalForm Y Z a ∧
        largestPrimeFactor a ≤ n.sqrt := by
  classical
  simp [smoothNormalSmallPrime, and_assoc]

@[simp]
theorem mem_smoothNormalLargePrime
    {n Y Z a : ℕ} {A : Finset ℕ} :
    a ∈ smoothNormalLargePrime n Y Z A ↔
      a ∈ A ∧ IsSmoothNormalForm Y Z a ∧
        n.sqrt < largestPrimeFactor a := by
  classical
  simp [smoothNormalLargePrime, and_assoc]

theorem disjoint_smoothNormal_small_large
    (n Y Z : ℕ) (A : Finset ℕ) :
    Disjoint (smoothNormalSmallPrime n Y Z A)
      (smoothNormalLargePrime n Y Z A) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  have hle := (mem_smoothNormalSmallPrime.mp ha).2.2
  have hlt := (mem_smoothNormalLargePrime.mp hb).2.2
  omega

/-- Exact partition of the smooth normal form at the square-root cutoff. -/
theorem smoothNormal_small_union_large
    (n Y Z : ℕ) (A : Finset ℕ) :
    smoothNormalSmallPrime n Y Z A ∪
        smoothNormalLargePrime n Y Z A = smoothNormalPiece Y Z A := by
  classical
  ext a
  simp only [Finset.mem_union, mem_smoothNormalSmallPrime,
    mem_smoothNormalLargePrime, mem_smoothNormalPiece]
  by_cases h : largestPrimeFactor a ≤ n.sqrt
  · simp [h, Nat.not_lt_of_ge h]
  · have h' : n.sqrt < largestPrimeFactor a := Nat.lt_of_not_ge h
    simp [h, h']

theorem card_smoothNormal_eq_small_add_large
    (n Y Z : ℕ) (A : Finset ℕ) :
    (smoothNormalPiece Y Z A).card =
      (smoothNormalSmallPrime n Y Z A).card +
        (smoothNormalLargePrime n Y Z A).card := by
  rw [← smoothNormal_small_union_large]
  exact Finset.card_union_of_disjoint
    (disjoint_smoothNormal_small_large n Y Z A)

/-- The canonical cofactor in a smooth normal form is positive when the
represented integer is positive. -/
theorem smoothNormal_cofactor_pos
    {n Y Z a : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (ha : a ∈ A)
    (hform : IsSmoothNormalForm Y Z a) :
    0 < a / largestPrimeFactor a := by
  dsimp [IsSmoothNormalForm] at hform
  have hapos := (mem_positiveIcc.mp (hA.1 ha)).1
  have hqpos := hform.1.pos
  by_contra ht
  have ht0 : a / largestPrimeFactor a = 0 := Nat.eq_zero_of_not_pos ht
  rw [ht0, Nat.mul_zero] at hform
  omega

/-- The part whose largest prime is at most `sqrt n` has the elementary
prime-times-cofactor bound. -/
theorem card_smoothNormalSmallPrime_le
    {n Y Z : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    (smoothNormalSmallPrime n Y Z A).card ≤
      Nat.primeCounting n.sqrt * Y ^ 4 := by
  apply PruningCounts.card_le_primeCounting_mul_of_factorization
  intro a ha
  have ha' := mem_smoothNormalSmallPrime.mp ha
  let q := largestPrimeFactor a
  let t := a / q
  have hform := ha'.2.1
  dsimp [IsSmoothNormalForm] at hform
  have htpos : 0 < t := by
    dsimp [t, q]
    exact smoothNormal_cofactor_pos hA ha'.1 ha'.2.1
  have htle : t ≤ Y ^ 4 := hform.2.2.2.2.2.le
  refine ⟨q, Nat.mem_primesLE.mpr ⟨ha'.2.2, hform.1⟩,
    t, mem_positiveIcc.mpr ⟨htpos, htle⟩, ?_⟩
  exact hform.2.2.2.1

/-- The finite parameter space of all smooth cofactors attached to large
primes. -/
noncomputable def smoothLargeParameters
    (n : ℕ) (A : Finset ℕ) (R Z : ℕ) : Finset (Σ _q : ℕ, ℕ) := by
  classical
  exact (largePrimes n).sigma fun q => smoothCofactorFiber A R Z q

/-- Products represented by the smooth large-prime parameter space. -/
noncomputable def smoothLargeProducts
    (n : ℕ) (A : Finset ℕ) (R Z : ℕ) : Finset ℕ := by
  classical
  exact (smoothLargeParameters n A R Z).image fun qu => qu.1 * qu.2

@[simp]
theorem mk_mem_smoothLargeParameters
    {n R Z q u : ℕ} {A : Finset ℕ} :
    (⟨q, u⟩ : Σ _q : ℕ, ℕ) ∈ smoothLargeParameters n A R Z ↔
      q ∈ largePrimes n ∧ u ∈ smoothCofactorFiber A R Z q := by
  classical
  simp [smoothLargeParameters]

theorem mem_smoothLargeProducts
    {n R Z a : ℕ} {A : Finset ℕ} :
    a ∈ smoothLargeProducts n A R Z ↔
      ∃ q u : ℕ, q ∈ largePrimes n ∧
        u ∈ smoothCofactorFiber A R Z q ∧ q * u = a := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨⟨q, u⟩, hqu, rfl⟩
    exact ⟨q, u, (mk_mem_smoothLargeParameters.mp hqu).1,
      (mk_mem_smoothLargeParameters.mp hqu).2, rfl⟩
  · rintro ⟨q, u, hq, hu, rfl⟩
    exact Finset.mem_image.mpr
      ⟨⟨q, u⟩, mk_mem_smoothLargeParameters.mpr ⟨hq, hu⟩, rfl⟩

/-- The smooth large-prime normal form is contained in the corresponding
cofactor-product image. -/
theorem smoothNormalLargePrime_subset_products
    {n Y Z : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    smoothNormalLargePrime n Y Z A ⊆
      smoothLargeProducts n A (Y ^ 4) Z := by
  intro a ha
  have ha' := mem_smoothNormalLargePrime.mp ha
  let q := largestPrimeFactor a
  let t := a / q
  have hform := ha'.2.1
  dsimp [IsSmoothNormalForm] at hform
  have hapos := (mem_positiveIcc.mp (hA.1 ha'.1)).1
  have hqleA : q ≤ a := Nat.le_of_dvd hapos hform.2.1
  have hqleN : q ≤ n := hqleA.trans (mem_positiveIcc.mp (hA.1 ha'.1)).2
  have hqLarge : q ∈ largePrimes n :=
    mem_largePrimes.mpr ⟨ha'.2.2, hqleN, hform.1⟩
  have htpos : 0 < t := by
    dsimp [t, q]
    exact smoothNormal_cofactor_pos hA ha'.1 ha'.2.1
  have htmem : t ∈ smoothCofactorFiber A (Y ^ 4) Z q := by
    apply mem_smoothCofactorFiber.mpr
    exact ⟨mem_positiveIcc.mpr ⟨htpos, hform.2.2.2.2.2.le⟩,
      hform.2.2.2.1.symm ▸ ha'.1, hform.2.2.2.2.1⟩
  exact mem_smoothLargeProducts.mpr
    ⟨q, t, hqLarge, htmem, hform.2.2.2.1.symm⟩

/-- The number of displayed smooth products is at most the sum of the fibre
sizes. -/
theorem card_smoothLargeProducts_le_sum
    (n : ℕ) (A : Finset ℕ) (R Z : ℕ) :
    (smoothLargeProducts n A R Z).card ≤
      ∑ q ∈ largePrimes n, (smoothCofactorFiber A R Z q).card := by
  classical
  calc
    (smoothLargeProducts n A R Z).card ≤
        (smoothLargeParameters n A R Z).card := Finset.card_image_le
    _ = ∑ q ∈ largePrimes n,
        (smoothCofactorFiber A R Z q).card := by
      simp [smoothLargeParameters]

/-- Final large-prime smooth-normal bound. -/
theorem card_smoothNormalLargePrime_le
    {n Y Z : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    (smoothNormalLargePrime n Y Z A).card ≤
      ∑ q ∈ largePrimes n,
        (smoothCofactorFiber A (Y ^ 4) Z q).card :=
  (Finset.card_le_card (smoothNormalLargePrime_subset_products hA)).trans
    (card_smoothLargeProducts_le_sum n A (Y ^ 4) Z)

/-- Combined finite estimate for the entire smooth normal form. -/
theorem card_smoothNormalPiece_le
    {n Y Z : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    (smoothNormalPiece Y Z A).card ≤
      Nat.primeCounting n.sqrt * Y ^ 4 +
        ∑ q ∈ largePrimes n,
          (smoothCofactorFiber A (Y ^ 4) Z q).card := by
  rw [card_smoothNormal_eq_small_add_large]
  exact Nat.add_le_add (card_smoothNormalSmallPrime_le hA)
    (card_smoothNormalLargePrime_le hA)

end NormalFormCounting

end Erdos796
