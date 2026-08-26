import ErdosProblems.Erdos796.PruningClassification
import ErdosProblems.Erdos796.Core
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A finite partition into pruning normal forms

This file turns the pointwise arithmetic classification from
`PruningClassification` into a finite-set decomposition.  The three pieces
are the `Y`-smooth elements, the canonical smooth-cofactor normal form, and
the canonical split normal form.  Their defining predicates are genuinely
disjoint, so once the pointwise obstruction hypothesis is supplied the cover
is an exact disjoint partition and cardinalities add exactly.
-/

namespace Erdos796

namespace PruningPartition

open PruningArithmetic PruningClassification

/-- Elements of `A` which are `Y`-smooth. -/
noncomputable def ySmoothPiece (Y : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact A.filter (YSmooth Y)

/-- Elements of `A` in the canonical smooth-cofactor normal form. -/
noncomputable def smoothNormalPiece (Y Z : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact A.filter (IsSmoothNormalForm Y Z)

/-- Elements of `A` in the canonical split normal form. -/
noncomputable def splitNormalPiece (Y Z : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact A.filter (IsSplitNormalForm Y Z)

@[simp] theorem mem_ySmoothPiece {Y a : ℕ} {A : Finset ℕ} :
    a ∈ ySmoothPiece Y A ↔ a ∈ A ∧ YSmooth Y a := by
  classical
  simp [ySmoothPiece]

@[simp] theorem mem_smoothNormalPiece {Y Z a : ℕ} {A : Finset ℕ} :
    a ∈ smoothNormalPiece Y Z A ↔
      a ∈ A ∧ IsSmoothNormalForm Y Z a := by
  classical
  simp [smoothNormalPiece]

@[simp] theorem mem_splitNormalPiece {Y Z a : ℕ} {A : Finset ℕ} :
    a ∈ splitNormalPiece Y Z A ↔
      a ∈ A ∧ IsSplitNormalForm Y Z a := by
  classical
  simp [splitNormalPiece]

theorem ySmoothPiece_subset (Y : ℕ) (A : Finset ℕ) :
    ySmoothPiece Y A ⊆ A := by
  classical
  exact Finset.filter_subset _ _

theorem smoothNormalPiece_subset (Y Z : ℕ) (A : Finset ℕ) :
    smoothNormalPiece Y Z A ⊆ A := by
  classical
  exact Finset.filter_subset _ _

theorem splitNormalPiece_subset (Y Z : ℕ) (A : Finset ℕ) :
    splitNormalPiece Y Z A ⊆ A := by
  classical
  exact Finset.filter_subset _ _

/-- Pointwise three-way classification, with all scale and obstruction
hypotheses visible. -/
theorem ySmooth_or_smoothNormal_or_splitNormal
    {Y Z a : ℕ} (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (ha : 0 < a) (hnoTriple : ¬HasThreeLargeFactors Y a) :
    YSmooth Y a ∨
      IsSmoothNormalForm Y Z a ∨ IsSplitNormalForm Y Z a := by
  by_cases hsmooth : YSmooth Y a
  · exact Or.inl hsmooth
  · exact Or.inr
      (smooth_or_split_normal_form hZ hZY ha hsmooth hnoTriple)

/-- A `Y`-smooth integer cannot simultaneously be in the smooth normal
form, whose displayed prime divisor is larger than `Y`. -/
theorem not_ySmooth_of_smoothNormalForm {Y Z a : ℕ}
    (h : IsSmoothNormalForm Y Z a) : ¬YSmooth Y a := by
  dsimp [IsSmoothNormalForm] at h
  intro hsmooth
  have hqle := hsmooth _ h.1 h.2.1
  omega

/-- The same incompatibility for the split normal form. -/
theorem not_ySmooth_of_splitNormalForm {Y Z a : ℕ}
    (h : IsSplitNormalForm Y Z a) : ¬YSmooth Y a := by
  dsimp [IsSplitNormalForm] at h
  intro hsmooth
  have hqle := hsmooth _ h.1 h.2.1
  omega

/-- The two canonical non-smooth branches are disjoint because the first has
a `Z`-smooth cofactor and the second has the negation of that property. -/
theorem smoothNormalForm_not_splitNormalForm {Y Z a : ℕ}
    (hs : IsSmoothNormalForm Y Z a)
    (ht : IsSplitNormalForm Y Z a) : False := by
  dsimp [IsSmoothNormalForm] at hs
  dsimp [IsSplitNormalForm] at ht
  exact ht.2.2.2.2.1 hs.2.2.2.2.1

theorem disjoint_ySmooth_smoothNormal (Y Z : ℕ) (A : Finset ℕ) :
    Disjoint (ySmoothPiece Y A) (smoothNormalPiece Y Z A) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hs
  exact (not_ySmooth_of_smoothNormalForm
    (mem_smoothNormalPiece.mp hs).2) (mem_ySmoothPiece.mp ha).2

theorem disjoint_ySmooth_splitNormal (Y Z : ℕ) (A : Finset ℕ) :
    Disjoint (ySmoothPiece Y A) (splitNormalPiece Y Z A) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hs
  exact (not_ySmooth_of_splitNormalForm
    (mem_splitNormalPiece.mp hs).2) (mem_ySmoothPiece.mp ha).2

theorem disjoint_smoothNormal_splitNormal (Y Z : ℕ) (A : Finset ℕ) :
    Disjoint (smoothNormalPiece Y Z A) (splitNormalPiece Y Z A) := by
  classical
  rw [Finset.disjoint_left]
  intro a hs ht
  exact smoothNormalForm_not_splitNormalForm
    (mem_smoothNormalPiece.mp hs).2 (mem_splitNormalPiece.mp ht).2

/-- The union of the first two pieces remains disjoint from the split piece. -/
theorem disjoint_union_splitNormal (Y Z : ℕ) (A : Finset ℕ) :
    Disjoint (ySmoothPiece Y A ∪ smoothNormalPiece Y Z A)
      (splitNormalPiece Y Z A) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha ht
  rcases Finset.mem_union.mp ha with hy | hs
  · exact (Finset.disjoint_left.mp (disjoint_ySmooth_splitNormal Y Z A))
      hy ht
  · exact (Finset.disjoint_left.mp (disjoint_smoothNormal_splitNormal Y Z A))
      hs ht

/-- Set-level cover under the explicit pointwise hypotheses. -/
theorem subset_union_three_pieces
    {Y Z : ℕ} {A : Finset ℕ}
    (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (hpos : ∀ a ∈ A, 0 < a)
    (hnoTriple : ∀ a ∈ A, ¬HasThreeLargeFactors Y a) :
    A ⊆ ySmoothPiece Y A ∪
      smoothNormalPiece Y Z A ∪ splitNormalPiece Y Z A := by
  classical
  intro a ha
  rcases ySmooth_or_smoothNormal_or_splitNormal hZ hZY
      (hpos a ha) (hnoTriple a ha) with hy | hs | ht
  · exact Finset.mem_union_left _
      (Finset.mem_union_left _ (mem_ySmoothPiece.mpr ⟨ha, hy⟩))
  · exact Finset.mem_union_left _
      (Finset.mem_union_right _ (mem_smoothNormalPiece.mpr ⟨ha, hs⟩))
  · exact Finset.mem_union_right _
      (mem_splitNormalPiece.mpr ⟨ha, ht⟩)

/-- Exact finite-set partition. -/
theorem union_three_pieces_eq
    {Y Z : ℕ} {A : Finset ℕ}
    (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (hpos : ∀ a ∈ A, 0 < a)
    (hnoTriple : ∀ a ∈ A, ¬HasThreeLargeFactors Y a) :
    ySmoothPiece Y A ∪ smoothNormalPiece Y Z A ∪
        splitNormalPiece Y Z A = A := by
  apply Finset.Subset.antisymm
  · intro a ha
    rcases Finset.mem_union.mp ha with ha | ht
    · rcases Finset.mem_union.mp ha with hy | hs
      · exact (mem_ySmoothPiece.mp hy).1
      · exact (mem_smoothNormalPiece.mp hs).1
    · exact (mem_splitNormalPiece.mp ht).1
  · exact subset_union_three_pieces hZ hZY hpos hnoTriple

/-- Exact additive cardinality form of the partition. -/
theorem card_eq_sum_three_pieces
    {Y Z : ℕ} {A : Finset ℕ}
    (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (hpos : ∀ a ∈ A, 0 < a)
    (hnoTriple : ∀ a ∈ A, ¬HasThreeLargeFactors Y a) :
    A.card = (ySmoothPiece Y A).card +
      (smoothNormalPiece Y Z A).card + (splitNormalPiece Y Z A).card := by
  have hcard := congrArg Finset.card
    (union_three_pieces_eq hZ hZY hpos hnoTriple)
  rw [Finset.card_union_of_disjoint (disjoint_union_splitNormal Y Z A),
    Finset.card_union_of_disjoint (disjoint_ySmooth_smoothNormal Y Z A)] at hcard
  exact hcard.symm

/-- Cardinal inequality form, convenient when the three pieces are bounded
separately. -/
theorem card_le_sum_three_pieces
    {Y Z : ℕ} {A : Finset ℕ}
    (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (hpos : ∀ a ∈ A, 0 < a)
    (hnoTriple : ∀ a ∈ A, ¬HasThreeLargeFactors Y a) :
    A.card ≤ (ySmoothPiece Y A).card +
      (smoothNormalPiece Y Z A).card + (splitNormalPiece Y Z A).card := by
  exact (card_eq_sum_three_pieces hZ hZY hpos hnoTriple).le

/-- The smooth piece is supported on `[1,Y^6]` once the same obstruction is
excluded pointwise. -/
theorem ySmoothPiece_subset_powSix
    {Y : ℕ} {A : Finset ℕ} (hY : 2 ≤ Y)
    (hpos : ∀ a ∈ A, 0 < a)
    (hnoTriple : ∀ a ∈ A, ¬HasThreeLargeFactors Y a) :
    ySmoothPiece Y A ⊆ positiveIcc (Y ^ 6) := by
  intro a ha
  have ha' := mem_ySmoothPiece.mp ha
  exact mem_positiveIcc.mpr
    ⟨hpos a ha'.1,
      ySmooth_le_pow_six_of_no_three_large_factors
        hY ha'.2 (hnoTriple a ha'.1)⟩

/-- Version specialized to a set already supported on a positive interval. -/
theorem card_eq_sum_three_pieces_of_subset_positiveIcc
    {n Y Z : ℕ} {A : Finset ℕ} (hA : A ⊆ positiveIcc n)
    (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (hnoTriple : ∀ a ∈ A, ¬HasThreeLargeFactors Y a) :
    A.card = (ySmoothPiece Y A).card +
      (smoothNormalPiece Y Z A).card + (splitNormalPiece Y Z A).card := by
  apply card_eq_sum_three_pieces hZ hZY
  · intro a ha
    exact (mem_positiveIcc.mp (hA ha)).1
  · exact hnoTriple

end PruningPartition

end Erdos796
