import ErdosProblems.Erdos796.SplitNormalCounting
import ErdosProblems.Erdos796.TriplePruning

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Pruning the large residual-multiplier split forms

For a split normal form `a`, the canonical coordinates
`(splitS a, splitQ a, splitR a)` multiply back to `a`.  On the
large-multiplier piece these triples are injectively parametrized by the
underlying elements of `A`.  If `W ≤ Z ≤ Y`, all three coordinates are at
least `W`, so the complete-box estimate and the finite dyadic decomposition
give a uniform fourth-root saving in `W`.
-/

namespace Erdos796

namespace LargeMultiplierPruning

open scoped BigOperators
open PruningClassification SplitNormalCounting
open AdmissibleTriples DyadicBoxes

/-- The canonical triple attached to a split normal form. -/
def canonicalSplitTriple (a : ℕ) : ℕ × ℕ × ℕ :=
  (splitS a, splitQ a, splitR a)

/-- Canonical triples coming from the large residual-multiplier piece. -/
noncomputable def largeMultiplierTriples
    (n Y Z W : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (splitLargeMultiplierPiece n Y Z W A).image canonicalSplitTriple

@[simp] theorem mem_largeMultiplierTriples
    {n Y Z W : ℕ} {A : Finset ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ largeMultiplierTriples n Y Z W A ↔
      ∃ a ∈ splitLargeMultiplierPiece n Y Z W A,
        canonicalSplitTriple a = p := by
  classical
  simp [largeMultiplierTriples]

/-- Multiplication recovers the element from its canonical split triple. -/
theorem tripleProduct_canonicalSplitTriple
    {Y Z a : ℕ} (hform : IsSplitNormalForm Y Z a) :
    tripleProduct (canonicalSplitTriple a) = a := by
  simpa [canonicalSplitTriple, tripleProduct] using!
    (split_value_eq hform).symm

/-- The canonical triple map is injective on the large-multiplier piece. -/
theorem canonicalSplitTriple_injective_on
    {n Y Z W : ℕ} {A : Finset ℕ} :
    Set.InjOn canonicalSplitTriple
      (splitLargeMultiplierPiece n Y Z W A : Set ℕ) := by
  intro a ha b hb hab
  have haForm := (mem_splitLargeMultiplierPiece.mp ha).2.1
  have hbForm := (mem_splitLargeMultiplierPiece.mp hb).2.1
  calc
    a = tripleProduct (canonicalSplitTriple a) :=
      (tripleProduct_canonicalSplitTriple haForm).symm
    _ = tripleProduct (canonicalSplitTriple b) := congrArg tripleProduct hab
    _ = b := tripleProduct_canonicalSplitTriple hbForm

@[simp] theorem card_largeMultiplierTriples
    (n Y Z W : ℕ) (A : Finset ℕ) :
    (largeMultiplierTriples n Y Z W A).card =
      (splitLargeMultiplierPiece n Y Z W A).card := by
  classical
  rw [largeMultiplierTriples, Finset.card_image_iff]
  exact canonicalSplitTriple_injective_on

/-- Multiplication is injective on the canonical triple family. -/
theorem largeMultiplierTriples_productInjective
    (n Y Z W : ℕ) (A : Finset ℕ) :
    TripleProductInjective (largeMultiplierTriples n Y Z W A) := by
  intro p hp q hq hpq
  rcases mem_largeMultiplierTriples.mp hp with ⟨a, ha, rfl⟩
  rcases mem_largeMultiplierTriples.mp hq with ⟨b, hb, rfl⟩
  have haForm := (mem_splitLargeMultiplierPiece.mp ha).2.1
  have hbForm := (mem_splitLargeMultiplierPiece.mp hb).2.1
  have hab : a = b := by
    calc
      a = tripleProduct (canonicalSplitTriple a) :=
        (tripleProduct_canonicalSplitTriple haForm).symm
      _ = tripleProduct (canonicalSplitTriple b) := hpq
      _ = b := tripleProduct_canonicalSplitTriple hbForm
  subst b
  rfl

/-- Every canonical triple product belongs to the original admissible set. -/
theorem largeMultiplierTriples_productsIn
    (n Y Z W : ℕ) (A : Finset ℕ) :
    TripleProductsIn (largeMultiplierTriples n Y Z W A) A := by
  intro p hp
  rcases mem_largeMultiplierTriples.mp hp with ⟨a, ha, rfl⟩
  rw [tripleProduct_canonicalSplitTriple
    (mem_splitLargeMultiplierPiece.mp ha).2.1]
  exact (mem_splitLargeMultiplierPiece.mp ha).1

/-- Coordinate lower bounds supplied by the split normal form and the
definition of the large-multiplier piece. -/
theorem largeMultiplierTriples_coordinateBounds
    {n Y Z W : ℕ} {A : Finset ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ largeMultiplierTriples n Y Z W A) :
    W ≤ p.1 ∧ Y < p.2.1 ∧ Z < p.2.2 := by
  rcases mem_largeMultiplierTriples.mp hp with ⟨a, ha, rfl⟩
  have ha' := mem_splitLargeMultiplierPiece.mp ha
  have hform := ha'.2.1
  have hq : Y < splitQ a := by
    simpa [splitQ, IsSplitNormalForm] using! hform.2.2.1
  have hr : Z < splitR a := (splitR_prime_gt hform).2
  exact ⟨ha'.2.2.2.2, hq, hr⟩

/-- Every canonical triple lies in the positive cube `[1,n]³`. -/
theorem largeMultiplierTriples_subset_ambient
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    largeMultiplierTriples n Y Z W A ⊆ tripleAmbient n := by
  intro p hp
  have hproducts := largeMultiplierTriples_productsIn n Y Z W A
  have hpos := coordinates_pos_of_mem hA hproducts hp
  have hle := TriplePruning.coordinate_le_tripleProduct hpos
  have hprodN :=
    (mem_positiveIcc.mp (hA.1 (hproducts p hp))).2
  exact mem_tripleAmbient.mpr
    ⟨mem_positiveIcc.mpr ⟨hpos.1, hle.1.trans hprodN⟩,
      mem_positiveIcc.mpr ⟨hpos.2.1, hle.2.1.trans hprodN⟩,
      mem_positiveIcc.mpr ⟨hpos.2.2, hle.2.2.trans hprodN⟩⟩

/-- The complete-box estimate for one dyadic fibre of canonical triples. -/
theorem largeMultiplierBox_completeBox_bound
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {ijk : ℕ × ℕ × ℕ} :
    ((tripleBoxPart n (largeMultiplierTriples n Y Z W A) ijk).card : ℝ) ≤
      (4 * (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ)) /
        Tripartite.realFourthRoot
          (Nat.min (2 ^ ijk.1)
            (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) := by
  let H := tripleBoxPart n (largeMultiplierTriples n Y Z W A) ijk
  have hsub : H ⊆
      TriplePruning.fullScaleInterval ijk.1 ×ˢ
        (TriplePruning.fullScaleInterval ijk.2.1 ×ˢ
          TriplePruning.fullScaleInterval ijk.2.2) :=
    TriplePruning.tripleBoxPart_subset_fullTripleBox
      (largeMultiplierTriples_subset_ambient hA) ijk
  have hinj : TripleProductInjective H := by
    intro p hp q hq heq
    exact largeMultiplierTriples_productInjective n Y Z W A
      (tripleBoxPart_subset n (largeMultiplierTriples n Y Z W A) ijk hp)
      (tripleBoxPart_subset n (largeMultiplierTriples n Y Z W A) ijk hq)
      heq
  have hproducts : TripleProductsIn H A := by
    intro p hp
    exact largeMultiplierTriples_productsIn n Y Z W A p
      (tripleBoxPart_subset n (largeMultiplierTriples n Y Z W A) ijk hp)
  simpa only [H, TriplePruning.card_fullScaleInterval, Nat.cast_pow,
    Nat.cast_ofNat] using!
    card_le_completeBox hA hinj hproducts
      (TriplePruning.fullScaleInterval ijk.1)
      (TriplePruning.fullScaleInterval ijk.2.1)
      (TriplePruning.fullScaleInterval ijk.2.2)
      hsub (by simp) (by simp) (by simp)

/-- A nonempty dyadic fibre has minimum side length at least `W/2`, while
the product of its side lengths is at most `n`. -/
theorem activeLargeMultiplierBox_scaleBounds
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hWZ : W ≤ Z) (hZY : Z ≤ Y) {ijk : ℕ × ℕ × ℕ}
    (hijk : ijk ∈
      activeTripleBoxIndices n (largeMultiplierTriples n Y Z W A)) :
    (W : ℝ) / 2 ≤
        (Nat.min (2 ^ ijk.1)
          (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) ∧
      (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ) ≤ (n : ℝ) := by
  rcases (mem_activeTripleBoxIndices.mp hijk).2 with ⟨p, hp⟩
  have hpLarge : p ∈ largeMultiplierTriples n Y Z W A :=
    tripleBoxPart_subset n (largeMultiplierTriples n Y Z W A) ijk hp
  have hcoords := largeMultiplierTriples_coordinateBounds hpLarge
  have hpFull := TriplePruning.tripleBoxPart_subset_fullTripleBox
    (largeMultiplierTriples_subset_ambient hA) ijk hp
  have hb := TriplePruning.mem_fullTripleBox.mp hpFull
  have hb1 := TriplePruning.mem_fullScaleInterval.mp hb.1
  have hb2 := TriplePruning.mem_fullScaleInterval.mp hb.2.1
  have hb3 := TriplePruning.mem_fullScaleInterval.mp hb.2.2
  have hWp1 : W ≤ p.1 := hcoords.1
  have hWp2 : W ≤ p.2.1 :=
    hWZ.trans (hZY.trans hcoords.2.1.le)
  have hWp3 : W ≤ p.2.2 := hWZ.trans hcoords.2.2.le
  have hside1 : (W : ℝ) / 2 ≤ (2 ^ ijk.1 : ℝ) := by
    have hNat : W < 2 ^ (ijk.1 + 1) := hWp1.trans_lt hb1.2
    have hReal : (W : ℝ) < ((2 ^ (ijk.1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  have hside2 : (W : ℝ) / 2 ≤ (2 ^ ijk.2.1 : ℝ) := by
    have hNat : W < 2 ^ (ijk.2.1 + 1) := hWp2.trans_lt hb2.2
    have hReal : (W : ℝ) < ((2 ^ (ijk.2.1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  have hside3 : (W : ℝ) / 2 ≤ (2 ^ ijk.2.2 : ℝ) := by
    have hNat : W < 2 ^ (ijk.2.2 + 1) := hWp3.trans_lt hb3.2
    have hReal : (W : ℝ) < ((2 ^ (ijk.2.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  constructor
  · rw [Nat.cast_min, Nat.cast_min, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_pow]
    exact le_min hside1 (le_min hside2 hside3)
  · have hvolumeProduct :
        2 ^ ijk.1 * (2 ^ ijk.2.1 * 2 ^ ijk.2.2) ≤
          p.1 * (p.2.1 * p.2.2) :=
      Nat.mul_le_mul hb1.1 (Nat.mul_le_mul hb2.1 hb3.1)
    have hvolumeTriple :
        2 ^ ijk.1 * (2 ^ ijk.2.1 * 2 ^ ijk.2.2) ≤
          tripleProduct p := by
      simpa [tripleProduct, Nat.mul_assoc] using! hvolumeProduct
    have hproductN : tripleProduct p ≤ n := by
      have hproductA :=
        largeMultiplierTriples_productsIn n Y Z W A p hpLarge
      exact (mem_positiveIcc.mp (hA.1 hproductA)).2
    have hvolumeN :
        (2 ^ ijk.1 * 2 ^ ijk.2.1) * 2 ^ ijk.2.2 ≤ n := by
      simpa [Nat.mul_assoc] using! hvolumeTriple.trans hproductN
    exact_mod_cast hvolumeN

/-- Every active dyadic fibre satisfies one common fourth-root bound. -/
theorem activeLargeMultiplierBox_uniformBound
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hW : 2 ≤ W) (hWZ : W ≤ Z) (hZY : Z ≤ Y)
    {ijk : ℕ × ℕ × ℕ}
    (hijk : ijk ∈
      activeTripleBoxIndices n (largeMultiplierTriples n Y Z W A)) :
    ((tripleBoxPart n
        (largeMultiplierTriples n Y Z W A) ijk).card : ℝ) ≤
      (4 * (n : ℝ)) /
        Tripartite.realFourthRoot ((W : ℝ) / 2) := by
  have hbox := largeMultiplierBox_completeBox_bound hA
    (Y := Y) (Z := Z) (W := W) (ijk := ijk)
  have hscale := activeLargeMultiplierBox_scaleBounds hA hWZ hZY hijk
  have hhalf : (1 : ℝ) ≤ (W : ℝ) / 2 := by
    have hWReal : (2 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    linarith
  have hrootPos :
      0 < Tripartite.realFourthRoot ((W : ℝ) / 2) :=
    Tripartite.realFourthRoot_pos_of_one_le hhalf
  have hrootMono :
      Tripartite.realFourthRoot ((W : ℝ) / 2) ≤
        Tripartite.realFourthRoot
          (Nat.min (2 ^ ijk.1)
            (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) :=
    Tripartite.realFourthRoot_mono hscale.1
  have hnumerator :
      4 * (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ) ≤ 4 * (n : ℝ) := by
    linarith
  exact hbox.trans
    (div_le_div₀ (by positivity) hnumerator hrootPos hrootMono)

/-- The summed large-multiplier pruning estimate. -/
theorem card_splitLargeMultiplierPiece_le_dyadicPruning
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hW : 2 ≤ W) (hWZ : W ≤ Z) (hZY : Z ≤ Y) :
    ((splitLargeMultiplierPiece n Y Z W A).card : ℝ) ≤
      (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((W : ℝ) / 2)) := by
  let H := largeMultiplierTriples n Y Z W A
  let I := activeTripleBoxIndices n H
  let P := tripleBoxPart n H
  let C : ℝ :=
    (4 * (n : ℝ)) / Tripartite.realFourthRoot ((W : ℝ) / 2)
  have huniform : ∀ ijk ∈ I, ((P ijk).card : ℝ) ≤ C := by
    intro ijk hijk
    exact activeLargeMultiplierBox_uniformBound hA hW hWZ hZY hijk
  have hunion := BoxPruning.card_biUnion_le_card_mul_of_uniform
    I P C huniform
  have hcover : I.biUnion P = H := by
    simpa [I, P, H] using!
      (biUnion_activeTripleBoxParts
        (largeMultiplierTriples_subset_ambient hA))
  rw [hcover] at hunion
  have hcardNat : I.card ≤ (Nat.log 2 n + 1) ^ 3 := by
    simpa [I, H] using!
      card_activeTripleBoxIndices_le n
        (largeMultiplierTriples n Y Z W A)
  have hcard : (I.card : ℝ) ≤
      (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (by positivity)
      (Tripartite.realFourthRoot_nonneg _)
  rw [← card_largeMultiplierTriples n Y Z W A]
  calc
    ((largeMultiplierTriples n Y Z W A).card : ℝ) ≤
        (I.card : ℝ) * C := by simpa [H] using! hunion
    _ ≤ (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) * C :=
      mul_le_mul_of_nonneg_right hcard hC
    _ = (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((W : ℝ) / 2)) := rfl

/-! ## The unrestricted large-multiplier piece

The following version removes the condition `n.sqrt < splitQ a`.  None of
the complete-box argument uses that condition: it needs only the canonical
product identity and the three coordinate lower bounds.
-/

set_option linter.unusedVariables false in
/-- Split normal forms with distinct canonical primes and residual
multiplier at least `W`, with no restriction on the size of `splitQ`. -/
noncomputable def splitAnyLargeMultiplierPiece
    (n Y Z W : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (PruningPartition.splitNormalPiece Y Z A).filter fun a =>
    splitQ a ≠ splitR a ∧ W ≤ splitS a

@[simp] theorem mem_splitAnyLargeMultiplierPiece
    {n Y Z W a : ℕ} {A : Finset ℕ} :
    a ∈ splitAnyLargeMultiplierPiece n Y Z W A ↔
      a ∈ A ∧ IsSplitNormalForm Y Z a ∧
        splitQ a ≠ splitR a ∧ W ≤ splitS a := by
  classical
  simp [splitAnyLargeMultiplierPiece, and_assoc]

/-- Canonical triples for the unrestricted large-multiplier piece. -/
noncomputable def anyLargeMultiplierTriples
    (n Y Z W : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (splitAnyLargeMultiplierPiece n Y Z W A).image
    canonicalSplitTriple

@[simp] theorem mem_anyLargeMultiplierTriples
    {n Y Z W : ℕ} {A : Finset ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ anyLargeMultiplierTriples n Y Z W A ↔
      ∃ a ∈ splitAnyLargeMultiplierPiece n Y Z W A,
        canonicalSplitTriple a = p := by
  classical
  simp [anyLargeMultiplierTriples]

/-- The canonical triple map remains injective after dropping the
large-first-prime condition. -/
theorem canonicalSplitTriple_injective_on_anyLargeMultiplierPiece
    {n Y Z W : ℕ} {A : Finset ℕ} :
    Set.InjOn canonicalSplitTriple
      (splitAnyLargeMultiplierPiece n Y Z W A : Set ℕ) := by
  intro a ha b hb hab
  have haForm := (mem_splitAnyLargeMultiplierPiece.mp ha).2.1
  have hbForm := (mem_splitAnyLargeMultiplierPiece.mp hb).2.1
  calc
    a = tripleProduct (canonicalSplitTriple a) :=
      (tripleProduct_canonicalSplitTriple haForm).symm
    _ = tripleProduct (canonicalSplitTriple b) := congrArg tripleProduct hab
    _ = b := tripleProduct_canonicalSplitTriple hbForm

@[simp] theorem card_anyLargeMultiplierTriples
    (n Y Z W : ℕ) (A : Finset ℕ) :
    (anyLargeMultiplierTriples n Y Z W A).card =
      (splitAnyLargeMultiplierPiece n Y Z W A).card := by
  classical
  rw [anyLargeMultiplierTriples, Finset.card_image_iff]
  exact canonicalSplitTriple_injective_on_anyLargeMultiplierPiece

/-- Triple multiplication is injective on the unrestricted canonical
family. -/
theorem anyLargeMultiplierTriples_productInjective
    (n Y Z W : ℕ) (A : Finset ℕ) :
    TripleProductInjective (anyLargeMultiplierTriples n Y Z W A) := by
  intro p hp q hq hpq
  rcases mem_anyLargeMultiplierTriples.mp hp with ⟨a, ha, rfl⟩
  rcases mem_anyLargeMultiplierTriples.mp hq with ⟨b, hb, rfl⟩
  have haForm := (mem_splitAnyLargeMultiplierPiece.mp ha).2.1
  have hbForm := (mem_splitAnyLargeMultiplierPiece.mp hb).2.1
  have hab : a = b := by
    calc
      a = tripleProduct (canonicalSplitTriple a) :=
        (tripleProduct_canonicalSplitTriple haForm).symm
      _ = tripleProduct (canonicalSplitTriple b) := hpq
      _ = b := tripleProduct_canonicalSplitTriple hbForm
  subst b
  rfl

/-- All unrestricted canonical products lie in `A`. -/
theorem anyLargeMultiplierTriples_productsIn
    (n Y Z W : ℕ) (A : Finset ℕ) :
    TripleProductsIn (anyLargeMultiplierTriples n Y Z W A) A := by
  intro p hp
  rcases mem_anyLargeMultiplierTriples.mp hp with ⟨a, ha, rfl⟩
  rw [tripleProduct_canonicalSplitTriple
    (mem_splitAnyLargeMultiplierPiece.mp ha).2.1]
  exact (mem_splitAnyLargeMultiplierPiece.mp ha).1

/-- The unrestricted family has the same three coordinate lower bounds. -/
theorem anyLargeMultiplierTriples_coordinateBounds
    {n Y Z W : ℕ} {A : Finset ℕ} {p : ℕ × ℕ × ℕ}
    (hp : p ∈ anyLargeMultiplierTriples n Y Z W A) :
    W ≤ p.1 ∧ Y < p.2.1 ∧ Z < p.2.2 := by
  rcases mem_anyLargeMultiplierTriples.mp hp with ⟨a, ha, rfl⟩
  have ha' := mem_splitAnyLargeMultiplierPiece.mp ha
  have hform := ha'.2.1
  have hq : Y < splitQ a := by
    simpa [splitQ, IsSplitNormalForm] using! hform.2.2.1
  have hr : Z < splitR a := (splitR_prime_gt hform).2
  exact ⟨ha'.2.2.2, hq, hr⟩

/-- Every unrestricted canonical triple lies in `[1,n]³`. -/
theorem anyLargeMultiplierTriples_subset_ambient
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    anyLargeMultiplierTriples n Y Z W A ⊆ tripleAmbient n := by
  intro p hp
  have hproducts := anyLargeMultiplierTriples_productsIn n Y Z W A
  have hpos := coordinates_pos_of_mem hA hproducts hp
  have hle := TriplePruning.coordinate_le_tripleProduct hpos
  have hprodN := (mem_positiveIcc.mp (hA.1 (hproducts p hp))).2
  exact mem_tripleAmbient.mpr
    ⟨mem_positiveIcc.mpr ⟨hpos.1, hle.1.trans hprodN⟩,
      mem_positiveIcc.mpr ⟨hpos.2.1, hle.2.1.trans hprodN⟩,
      mem_positiveIcc.mpr ⟨hpos.2.2, hle.2.2.trans hprodN⟩⟩

/-- The complete-box bound for one unrestricted dyadic fibre. -/
theorem anyLargeMultiplierBox_completeBox_bound
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    {ijk : ℕ × ℕ × ℕ} :
    ((tripleBoxPart n
        (anyLargeMultiplierTriples n Y Z W A) ijk).card : ℝ) ≤
      (4 * (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ)) /
        Tripartite.realFourthRoot
          (Nat.min (2 ^ ijk.1)
            (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) := by
  let H := tripleBoxPart n (anyLargeMultiplierTriples n Y Z W A) ijk
  have hsub : H ⊆
      TriplePruning.fullScaleInterval ijk.1 ×ˢ
        (TriplePruning.fullScaleInterval ijk.2.1 ×ˢ
          TriplePruning.fullScaleInterval ijk.2.2) :=
    TriplePruning.tripleBoxPart_subset_fullTripleBox
      (anyLargeMultiplierTriples_subset_ambient hA) ijk
  have hinj : TripleProductInjective H := by
    intro p hp q hq heq
    exact anyLargeMultiplierTriples_productInjective n Y Z W A
      (tripleBoxPart_subset n
        (anyLargeMultiplierTriples n Y Z W A) ijk hp)
      (tripleBoxPart_subset n
        (anyLargeMultiplierTriples n Y Z W A) ijk hq)
      heq
  have hproducts : TripleProductsIn H A := by
    intro p hp
    exact anyLargeMultiplierTriples_productsIn n Y Z W A p
      (tripleBoxPart_subset n
        (anyLargeMultiplierTriples n Y Z W A) ijk hp)
  simpa only [H, TriplePruning.card_fullScaleInterval, Nat.cast_pow,
    Nat.cast_ofNat] using!
    card_le_completeBox hA hinj hproducts
      (TriplePruning.fullScaleInterval ijk.1)
      (TriplePruning.fullScaleInterval ijk.2.1)
      (TriplePruning.fullScaleInterval ijk.2.2)
      hsub (by simp) (by simp) (by simp)

/-- A nonempty unrestricted fibre has minimum side length at least `W/2`
and dyadic volume at most `n`. -/
theorem activeAnyLargeMultiplierBox_scaleBounds
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hWZ : W ≤ Z) (hZY : Z ≤ Y) {ijk : ℕ × ℕ × ℕ}
    (hijk : ijk ∈
      activeTripleBoxIndices n (anyLargeMultiplierTriples n Y Z W A)) :
    (W : ℝ) / 2 ≤
        (Nat.min (2 ^ ijk.1)
          (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) ∧
      (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ) ≤ (n : ℝ) := by
  rcases (mem_activeTripleBoxIndices.mp hijk).2 with ⟨p, hp⟩
  have hpLarge : p ∈ anyLargeMultiplierTriples n Y Z W A :=
    tripleBoxPart_subset n (anyLargeMultiplierTriples n Y Z W A) ijk hp
  have hcoords := anyLargeMultiplierTriples_coordinateBounds hpLarge
  have hpFull := TriplePruning.tripleBoxPart_subset_fullTripleBox
    (anyLargeMultiplierTriples_subset_ambient hA) ijk hp
  have hb := TriplePruning.mem_fullTripleBox.mp hpFull
  have hb1 := TriplePruning.mem_fullScaleInterval.mp hb.1
  have hb2 := TriplePruning.mem_fullScaleInterval.mp hb.2.1
  have hb3 := TriplePruning.mem_fullScaleInterval.mp hb.2.2
  have hWp1 : W ≤ p.1 := hcoords.1
  have hWp2 : W ≤ p.2.1 := hWZ.trans (hZY.trans hcoords.2.1.le)
  have hWp3 : W ≤ p.2.2 := hWZ.trans hcoords.2.2.le
  have hside1 : (W : ℝ) / 2 ≤ (2 ^ ijk.1 : ℝ) := by
    have hNat : W < 2 ^ (ijk.1 + 1) := hWp1.trans_lt hb1.2
    have hReal : (W : ℝ) < ((2 ^ (ijk.1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  have hside2 : (W : ℝ) / 2 ≤ (2 ^ ijk.2.1 : ℝ) := by
    have hNat : W < 2 ^ (ijk.2.1 + 1) := hWp2.trans_lt hb2.2
    have hReal : (W : ℝ) < ((2 ^ (ijk.2.1 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  have hside3 : (W : ℝ) / 2 ≤ (2 ^ ijk.2.2 : ℝ) := by
    have hNat : W < 2 ^ (ijk.2.2 + 1) := hWp3.trans_lt hb3.2
    have hReal : (W : ℝ) < ((2 ^ (ijk.2.2 + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNat
    norm_num [pow_succ] at hReal ⊢
    linarith
  constructor
  · rw [Nat.cast_min, Nat.cast_min, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_pow]
    exact le_min hside1 (le_min hside2 hside3)
  · have hvolumeProduct :
        2 ^ ijk.1 * (2 ^ ijk.2.1 * 2 ^ ijk.2.2) ≤
          p.1 * (p.2.1 * p.2.2) :=
      Nat.mul_le_mul hb1.1 (Nat.mul_le_mul hb2.1 hb3.1)
    have hvolumeTriple :
        2 ^ ijk.1 * (2 ^ ijk.2.1 * 2 ^ ijk.2.2) ≤
          tripleProduct p := by
      simpa [tripleProduct, Nat.mul_assoc] using! hvolumeProduct
    have hproductN : tripleProduct p ≤ n := by
      have hproductA := anyLargeMultiplierTriples_productsIn
        n Y Z W A p hpLarge
      exact (mem_positiveIcc.mp (hA.1 hproductA)).2
    have hvolumeN :
        (2 ^ ijk.1 * 2 ^ ijk.2.1) * 2 ^ ijk.2.2 ≤ n := by
      simpa [Nat.mul_assoc] using! hvolumeTriple.trans hproductN
    exact_mod_cast hvolumeN

/-- Uniform fourth-root estimate for every active unrestricted fibre. -/
theorem activeAnyLargeMultiplierBox_uniformBound
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hW : 2 ≤ W) (hWZ : W ≤ Z) (hZY : Z ≤ Y)
    {ijk : ℕ × ℕ × ℕ}
    (hijk : ijk ∈
      activeTripleBoxIndices n (anyLargeMultiplierTriples n Y Z W A)) :
    ((tripleBoxPart n
        (anyLargeMultiplierTriples n Y Z W A) ijk).card : ℝ) ≤
      (4 * (n : ℝ)) /
        Tripartite.realFourthRoot ((W : ℝ) / 2) := by
  have hbox := anyLargeMultiplierBox_completeBox_bound hA
    (Y := Y) (Z := Z) (W := W) (ijk := ijk)
  have hscale := activeAnyLargeMultiplierBox_scaleBounds hA hWZ hZY hijk
  have hhalf : (1 : ℝ) ≤ (W : ℝ) / 2 := by
    have hWReal : (2 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    linarith
  have hrootPos : 0 < Tripartite.realFourthRoot ((W : ℝ) / 2) :=
    Tripartite.realFourthRoot_pos_of_one_le hhalf
  have hrootMono :
      Tripartite.realFourthRoot ((W : ℝ) / 2) ≤
        Tripartite.realFourthRoot
          (Nat.min (2 ^ ijk.1)
            (Nat.min (2 ^ ijk.2.1) (2 ^ ijk.2.2)) : ℝ) :=
    Tripartite.realFourthRoot_mono hscale.1
  have hnumerator :
      4 * (2 ^ ijk.1 : ℝ) * (2 ^ ijk.2.1 : ℝ) *
          (2 ^ ijk.2.2 : ℝ) ≤ 4 * (n : ℝ) := by
    linarith
  exact hbox.trans
    (div_le_div₀ (by positivity) hnumerator hrootPos hrootMono)

/-- Summed dyadic pruning estimate for all split normal forms whose
canonical residual multiplier is at least `W`, with no first-prime cutoff. -/
theorem card_splitAnyLargeMultiplierPiece_le_dyadicPruning
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hW : 2 ≤ W) (hWZ : W ≤ Z) (hZY : Z ≤ Y) :
    ((splitAnyLargeMultiplierPiece n Y Z W A).card : ℝ) ≤
      (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((W : ℝ) / 2)) := by
  let H := anyLargeMultiplierTriples n Y Z W A
  let I := activeTripleBoxIndices n H
  let P := tripleBoxPart n H
  let C : ℝ :=
    (4 * (n : ℝ)) / Tripartite.realFourthRoot ((W : ℝ) / 2)
  have huniform : ∀ ijk ∈ I, ((P ijk).card : ℝ) ≤ C := by
    intro ijk hijk
    exact activeAnyLargeMultiplierBox_uniformBound hA hW hWZ hZY hijk
  have hunion := BoxPruning.card_biUnion_le_card_mul_of_uniform
    I P C huniform
  have hcover : I.biUnion P = H := by
    simpa [I, P, H] using!
      (biUnion_activeTripleBoxParts
        (anyLargeMultiplierTriples_subset_ambient hA))
  rw [hcover] at hunion
  have hcardNat : I.card ≤ (Nat.log 2 n + 1) ^ 3 := by
    simpa [I, H] using!
      card_activeTripleBoxIndices_le n
        (anyLargeMultiplierTriples n Y Z W A)
  have hcard : (I.card : ℝ) ≤
      (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (by positivity)
      (Tripartite.realFourthRoot_nonneg _)
  rw [← card_anyLargeMultiplierTriples n Y Z W A]
  calc
    ((anyLargeMultiplierTriples n Y Z W A).card : ℝ) ≤
        (I.card : ℝ) * C := by simpa [H] using! hunion
    _ ≤ (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) * C :=
      mul_le_mul_of_nonneg_right hcard hC
    _ = (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((W : ℝ) / 2)) := rfl

end LargeMultiplierPruning

end Erdos796
