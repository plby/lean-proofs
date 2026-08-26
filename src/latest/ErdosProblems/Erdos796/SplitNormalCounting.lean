import ErdosProblems.Erdos796.PruningPartition
import ErdosProblems.Erdos796.PruningCounts
import ErdosProblems.Erdos796.SemiprimeTailBudget

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Counting the split pruning normal form

The canonical split form writes an element as `s*q*r`, with `q` its largest
prime factor and `r` the largest prime factor of the first cofactor.  This
file embeds the part with `q > sqrt n` and `s < W` into the exact semiprime
tail multiplier fibres.  It also isolates and bounds the repeated-prime case
`q = r`.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

namespace SplitNormalCounting

open PruningNormalForms PruningClassification PruningPartition
  PairwiseOverlap SemiprimeTailBudget

/-- Canonical first prime in the split form. -/
def splitQ (a : ℕ) : ℕ := largestPrimeFactor a

/-- Cofactor after removing the canonical first prime. -/
def splitT (a : ℕ) : ℕ := a / splitQ a

/-- Canonical second prime in the split form. -/
def splitR (a : ℕ) : ℕ := largestPrimeFactor (splitT a)

/-- Residual multiplier in the split form. -/
def splitS (a : ℕ) : ℕ := splitT a / splitR a

/-- The part paid for by the large-prime semiprime tail. -/
noncomputable def splitTailPiece
    (n Y Z W : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (splitNormalPiece Y Z A).filter fun a =>
    n.sqrt < splitQ a ∧ splitQ a ≠ splitR a ∧ splitS a < W

/-- The repeated-prime exceptional part. -/
noncomputable def splitRepeatedPrimePiece
    (Y Z : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (splitNormalPiece Y Z A).filter fun a => splitQ a = splitR a

/-- Distinct-prime split forms whose canonical largest prime is still at
most `sqrt n`. -/
noncomputable def splitSmallPrimePiece
    (n Y Z : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (splitNormalPiece Y Z A).filter fun a =>
    splitQ a ≠ splitR a ∧ splitQ a ≤ n.sqrt

/-- Distinct-prime, large-first-prime split forms whose residual multiplier
is at least `W`.  This is the part removed by the second complete-box
argument. -/
noncomputable def splitLargeMultiplierPiece
    (n Y Z W : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (splitNormalPiece Y Z A).filter fun a =>
    splitQ a ≠ splitR a ∧ n.sqrt < splitQ a ∧ W ≤ splitS a

@[simp]
theorem mem_splitTailPiece
    {n Y Z W a : ℕ} {A : Finset ℕ} :
    a ∈ splitTailPiece n Y Z W A ↔
      a ∈ A ∧ IsSplitNormalForm Y Z a ∧
        n.sqrt < splitQ a ∧ splitQ a ≠ splitR a ∧ splitS a < W := by
  classical
  simp [splitTailPiece, and_assoc]

@[simp]
theorem mem_splitRepeatedPrimePiece
    {Y Z a : ℕ} {A : Finset ℕ} :
    a ∈ splitRepeatedPrimePiece Y Z A ↔
      a ∈ A ∧ IsSplitNormalForm Y Z a ∧
        splitQ a = splitR a := by
  classical
  simp [splitRepeatedPrimePiece, and_assoc]

@[simp]
theorem mem_splitSmallPrimePiece
    {n Y Z a : ℕ} {A : Finset ℕ} :
    a ∈ splitSmallPrimePiece n Y Z A ↔
      a ∈ A ∧ IsSplitNormalForm Y Z a ∧
        splitQ a ≠ splitR a ∧ splitQ a ≤ n.sqrt := by
  classical
  simp [splitSmallPrimePiece, and_assoc]

@[simp]
theorem mem_splitLargeMultiplierPiece
    {n Y Z W a : ℕ} {A : Finset ℕ} :
    a ∈ splitLargeMultiplierPiece n Y Z W A ↔
      a ∈ A ∧ IsSplitNormalForm Y Z a ∧
        splitQ a ≠ splitR a ∧ n.sqrt < splitQ a ∧ W ≤ splitS a := by
  classical
  simp [splitLargeMultiplierPiece, and_assoc]

/-- The four pieces cover the whole split normal form. -/
theorem splitNormalPiece_subset_four_pieces
    (n Y Z W : ℕ) (A : Finset ℕ) :
    splitNormalPiece Y Z A ⊆
      splitRepeatedPrimePiece Y Z A ∪
        splitSmallPrimePiece n Y Z A ∪
          splitLargeMultiplierPiece n Y Z W A ∪
            splitTailPiece n Y Z W A := by
  intro a ha
  have ha' := mem_splitNormalPiece.mp ha
  simp only [Finset.mem_union]
  by_cases hqr : splitQ a = splitR a
  · exact Or.inl <| Or.inl <| Or.inl <|
      mem_splitRepeatedPrimePiece.mpr ⟨ha'.1, ha'.2, hqr⟩
  · by_cases hq : splitQ a ≤ n.sqrt
    · exact Or.inl <| Or.inl <| Or.inr <|
        mem_splitSmallPrimePiece.mpr ⟨ha'.1, ha'.2, hqr, hq⟩
    · have hq' : n.sqrt < splitQ a := Nat.lt_of_not_ge hq
      by_cases hs : splitS a < W
      · exact Or.inr <|
          mem_splitTailPiece.mpr ⟨ha'.1, ha'.2, hq', hqr, hs⟩
      · have hs' : W ≤ splitS a := Nat.le_of_not_gt hs
        exact Or.inl <| Or.inr <|
          mem_splitLargeMultiplierPiece.mpr
            ⟨ha'.1, ha'.2, hqr, hq', hs'⟩

/-- Cardinal form of the four-piece cover.  Disjointness is not needed for
the upper bound used in the structural reduction. -/
theorem card_splitNormalPiece_le_four_pieces
    (n Y Z W : ℕ) (A : Finset ℕ) :
    (splitNormalPiece Y Z A).card ≤
      (splitRepeatedPrimePiece Y Z A).card +
        (splitSmallPrimePiece n Y Z A).card +
          (splitLargeMultiplierPiece n Y Z W A).card +
            (splitTailPiece n Y Z W A).card := by
  have hsub := Finset.card_le_card
    (splitNormalPiece_subset_four_pieces n Y Z W A)
  calc
    (splitNormalPiece Y Z A).card ≤
        (splitRepeatedPrimePiece Y Z A ∪
          splitSmallPrimePiece n Y Z A ∪
            splitLargeMultiplierPiece n Y Z W A ∪
              splitTailPiece n Y Z W A).card := hsub
    _ ≤ (splitRepeatedPrimePiece Y Z A).card +
        (splitSmallPrimePiece n Y Z A).card +
          (splitLargeMultiplierPiece n Y Z W A).card +
            (splitTailPiece n Y Z W A).card := by
      calc
        (splitRepeatedPrimePiece Y Z A ∪
            splitSmallPrimePiece n Y Z A ∪
              splitLargeMultiplierPiece n Y Z W A ∪
                splitTailPiece n Y Z W A).card ≤
            (splitRepeatedPrimePiece Y Z A ∪
              splitSmallPrimePiece n Y Z A ∪
                splitLargeMultiplierPiece n Y Z W A).card +
              (splitTailPiece n Y Z W A).card :=
          Finset.card_union_le _ _
        _ ≤ ((splitRepeatedPrimePiece Y Z A ∪
              splitSmallPrimePiece n Y Z A).card +
                (splitLargeMultiplierPiece n Y Z W A).card) +
              (splitTailPiece n Y Z W A).card :=
          Nat.add_le_add_right
            (Finset.card_union_le
              (splitRepeatedPrimePiece Y Z A ∪
                splitSmallPrimePiece n Y Z A)
              (splitLargeMultiplierPiece n Y Z W A)) _
        _ ≤ (((splitRepeatedPrimePiece Y Z A).card +
              (splitSmallPrimePiece n Y Z A).card) +
                (splitLargeMultiplierPiece n Y Z W A).card) +
              (splitTailPiece n Y Z W A).card :=
          Nat.add_le_add_right
            (Nat.add_le_add_right
              (Finset.card_union_le
                (splitRepeatedPrimePiece Y Z A)
                (splitSmallPrimePiece n Y Z A)) _) _

/-- Positivity of the residual multiplier in every split normal form coming
from a positive ambient set. -/
theorem splitS_pos
    {n Y Z a : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (ha : a ∈ A)
    (hform : IsSplitNormalForm Y Z a) : 0 < splitS a := by
  have hapos := (mem_positiveIcc.mp (hA.1 ha)).1
  dsimp [IsSplitNormalForm] at hform
  change 0 < a / largestPrimeFactor a /
    largestPrimeFactor (a / largestPrimeFactor a)
  by_contra hs
  have hs0 : a / largestPrimeFactor a /
      largestPrimeFactor (a / largestPrimeFactor a) = 0 :=
    Nat.eq_zero_of_not_pos hs
  have ht0 : a / largestPrimeFactor a = 0 := by
    calc
      a / largestPrimeFactor a =
          largestPrimeFactor (a / largestPrimeFactor a) *
            (a / largestPrimeFactor a /
              largestPrimeFactor (a / largestPrimeFactor a)) :=
        hform.2.2.2.2.2.2.2.2.1
      _ = 0 := by rw [hs0, Nat.mul_zero]
  rw [ht0, Nat.mul_zero] at hform
  omega

/-- Expanded canonical product identity `a = s*q*r`. -/
theorem split_value_eq
    {Y Z a : ℕ} (hform : IsSplitNormalForm Y Z a) :
    a = splitS a * splitQ a * splitR a := by
  let q := largestPrimeFactor a
  let t := a / q
  let r := largestPrimeFactor t
  let s := t / r
  have haqt : a = q * t := by
    simpa [q, t, IsSplitNormalForm] using! hform.2.2.2.1
  have htrs : t = r * s := by
    simpa [q, t, r, s, IsSplitNormalForm] using!
      hform.2.2.2.2.2.2.2.2.1
  change a = s * q * r
  calc
    a = q * t := haqt
    _ = q * (r * s) := congrArg (fun x => q * x) htrs
    _ = s * q * r := by ring

/-- The first canonical prime of a split form is prime and divides `a`. -/
theorem splitQ_prime_dvd
    {Y Z a : ℕ} (hform : IsSplitNormalForm Y Z a) :
    (splitQ a).Prime ∧ splitQ a ∣ a := by
  simpa [splitQ, IsSplitNormalForm] using! ⟨hform.1, hform.2.1⟩

/-- The second canonical prime is prime and lies above `Z`. -/
theorem splitR_prime_gt
    {Y Z a : ℕ} (hform : IsSplitNormalForm Y Z a) :
    (splitR a).Prime ∧ Z < splitR a := by
  dsimp [IsSplitNormalForm, splitR, splitT, splitQ] at hform ⊢
  exact ⟨hform.2.2.2.2.2.1, hform.2.2.2.2.2.2.2.1⟩

/-- Residual multiplier bound supplied by the split normal form. -/
theorem splitS_lt_pow_four
    {Y Z a : ℕ} (hform : IsSplitNormalForm Y Z a) :
    splitS a < Y ^ 4 := by
  simpa [splitS, splitR, splitT, splitQ, IsSplitNormalForm] using!
    hform.2.2.2.2.2.2.2.2.2

/-- The finite product image of a family of tail multiplier fibres. -/
noncomputable def splitTailProducts
    (n Z : ℕ) (A M : Finset ℕ) : Finset ℕ := by
  classical
  exact (M.sigma fun s => multiplierFiberEdges n Z A s).image fun p =>
    multipliedPrimePair p.1 p.2.1 p.2.2

theorem mem_splitTailProducts
    {n Z a : ℕ} {A M : Finset ℕ} :
    a ∈ splitTailProducts n Z A M ↔
      ∃ s ∈ M, ∃ Q r : ℕ,
        (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ multiplierFiberEdges n Z A s ∧
          multipliedPrimePair s Q r = a := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨⟨s, ⟨Q, r⟩⟩, hp, rfl⟩
    have hp' := Finset.mem_sigma.mp hp
    exact ⟨s, hp'.1, Q, r, hp'.2, rfl⟩
  · rintro ⟨s, hs, Q, r, hQr, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨⟨s, ⟨Q, r⟩⟩, Finset.mem_sigma.mpr ⟨hs, hQr⟩, rfl⟩

/-- A captured split-normal element belongs to the product image of the
corresponding positive multipliers below `W`. -/
theorem splitTailPiece_subset_products
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    splitTailPiece n Y Z W A ⊆
      splitTailProducts n Z A (positiveIcc (W - 1)) := by
  intro a ha
  have ha' := mem_splitTailPiece.mp ha
  have hform := ha'.2.1
  let q := splitQ a
  let r := splitR a
  let s := splitS a
  have hspos : 0 < s := by
    dsimp [s]
    exact splitS_pos hA ha'.1 hform
  have hsW : s ∈ positiveIcc (W - 1) := by
    apply mem_positiveIcc.mpr
    omega
  have hqpd := splitQ_prime_dvd hform
  have hrp := splitR_prime_gt hform
  have hapos := (mem_positiveIcc.mp (hA.1 ha'.1)).1
  have hqleA : q ≤ a := Nat.le_of_dvd hapos hqpd.2
  have hqleN : q ≤ n := hqleA.trans (mem_positiveIcc.mp (hA.1 ha'.1)).2
  have hqLarge : q ∈ largePrimes n :=
    mem_largePrimes.mpr ⟨ha'.2.2.1, hqleN, hqpd.1⟩
  have hqrle : q * r ≤ n := by
    have hsone : 1 ≤ s := hspos
    have hqrs : q * r ≤ s * q * r := by
      have hmul := Nat.mul_le_mul_left (q * r) hsone
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using! hmul
    have hvalue : s * q * r = a := by
      simpa [s, q, r] using! (split_value_eq hform).symm
    rw [hvalue] at hqrs
    exact hqrs.trans (mem_positiveIcc.mp (hA.1 ha'.1)).2
  have hrquot : r ≤ n / q := by
    apply (Nat.le_div_iff_mul_le hqpd.1.pos).mpr
    simpa [q, Nat.mul_comm] using! hqrle
  have hrNew : r ∈ newPrimes Z (n / q) :=
    mem_newPrimes.mpr ⟨hrp.2, hrquot, hrp.1⟩
  have hedge : (⟨q, r⟩ : Σ _q : ℕ, ℕ) ∈
      multiplierFiberEdges n Z A s := by
    apply mem_multiplierFiberEdges.mpr
    have hvalue : multipliedPrimePair s q r = a := by
      simpa [multipliedPrimePair, s, q, r] using!
        (split_value_eq hform).symm
    exact ⟨hspos, hqLarge, hrNew, hvalue ▸ ha'.1⟩
  have hvalue : multipliedPrimePair s q r = a := by
    simpa [multipliedPrimePair, s, q, r] using!
      (split_value_eq hform).symm
  exact mem_splitTailProducts.mpr
    ⟨s, hsW, q, r, hedge, hvalue⟩

/-- Product images have cardinality at most the total size of their
multiplier fibres. -/
theorem card_splitTailProducts_le_sum
    (n Z : ℕ) (A M : Finset ℕ) :
    (splitTailProducts n Z A M).card ≤
      ∑ s ∈ M, (multiplierFiberEdges n Z A s).card := by
  classical
  calc
    (splitTailProducts n Z A M).card ≤
        (M.sigma fun s => multiplierFiberEdges n Z A s).card :=
      Finset.card_image_le
    _ = ∑ s ∈ M, (multiplierFiberEdges n Z A s).card := by simp

/-- Captured split-normal elements are dominated by the multiplier-fibre
sum to which Bonferroni applies. -/
theorem card_splitTailPiece_le_sum
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    (splitTailPiece n Y Z W A).card ≤
      ∑ s ∈ positiveIcc (W - 1),
        (multiplierFiberEdges n Z A s).card :=
  (Finset.card_le_card (splitTailPiece_subset_products hA)).trans
    (card_splitTailProducts_le_sum n Z A (positiveIcc (W - 1)))

/-- Every repeated-prime split form lies in the elementary set of products
`s*q^2`, with `q ≤ sqrt n` and `s ≤ Y^4`. -/
theorem splitRepeatedPrimePiece_subset_products
    {n Y Z : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    splitRepeatedPrimePiece Y Z A ⊆
      PruningCounts.boundedPrimeSquareProducts n.sqrt (Y ^ 4) := by
  intro a ha
  have ha' := mem_splitRepeatedPrimePiece.mp ha
  have hform := ha'.2.1
  let q := splitQ a
  let s := splitS a
  have hspos : 0 < s := by
    dsimp [s]
    exact splitS_pos hA ha'.1 hform
  have hsle : s ≤ Y ^ 4 := (splitS_lt_pow_four hform).le
  have hvalue := split_value_eq hform
  have hqr : splitR a = q := ha'.2.2.symm
  have hqpd := splitQ_prime_dvd hform
  have hqqleA : q * q ≤ a := by
    rw [hvalue, hqr]
    nlinarith
  have hqqleN : q * q ≤ n :=
    hqqleA.trans (mem_positiveIcc.mp (hA.1 ha'.1)).2
  have hqsqrt : q ≤ n.sqrt := Nat.le_sqrt.mpr hqqleN
  rw [PruningCounts.boundedPrimeSquareProducts]
  apply Finset.mem_image.mpr
  refine ⟨(q, s), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Nat.mem_primesLE.mpr ⟨hqsqrt, hqpd.1⟩
  · exact mem_positiveIcc.mpr ⟨hspos, hsle⟩
  · rw [hvalue, hqr]

/-- Repeated-prime split forms have the explicit elementary cardinal bound. -/
theorem card_splitRepeatedPrimePiece_le
    {n Y Z : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    (splitRepeatedPrimePiece Y Z A).card ≤
      Nat.primeCounting n.sqrt * Y ^ 4 :=
  (Finset.card_le_card (splitRepeatedPrimePiece_subset_products hA)).trans
    (PruningCounts.card_boundedPrimeSquareProducts_le n.sqrt (Y ^ 4))

end SplitNormalCounting

end Erdos796
