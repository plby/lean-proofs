/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness
import ErdosProblems.Erdos186.PZ.Reduction.Coordinates

/-!
# Pham--Zakharov irreducibility in GAP coordinates

This file gives the literal finite-coordinate content of Definition 9 in
Pham--Zakharov.  A selector records an actual enhanced CFP witness for each
nonempty finite lattice set on which the reduction is run.  It is explicit
data, not an assumed proposition such as `HasCFPStructure`.

The large CFP core is identified with its coefficient vectors in the
canonical coefficient box of the selected proper GAP.  Irreducibility then
quantifies over dense subsets of that identified core and over translations
by every point of the coefficient box, exactly as in the paper.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

/-- One concrete enhanced CFP output, with all its finite parameters, for a
specified input set. -/
structure SelectedCFP {d : ℕ} (A : Finset (BoxPoint d)) where
  reserveBound : ℕ
  rankBound : ℕ
  dilation : ℕ
  loss : ℕ
  witness :
    CFP.EnhancedCFPWitness A reserveBound rankBound dilation loss

/-- A concrete witness-producing choice function on the nonempty sets
encountered in the reduction.  A genuine CFP theorem supplies this function
on the relevant class of sets; no existence is postulated here. -/
structure CFPSelector where
  select : ∀ {d : ℕ} (A : Finset (BoxPoint d)), A.Nonempty → SelectedCFP A

namespace SelectedCFP

variable {d : ℕ} {A : Finset (BoxPoint d)} (S : SelectedCFP A)

/-- The selected subset-sum dimension. -/
abbrev dimension : ℕ := S.witness.rank

/-- The selected progression. -/
abbrev progression : GAP d S.dimension := S.witness.progression

/-- The large CFP core in the input ambient lattice. -/
abbrev core : Finset (BoxPoint d) := S.witness.core

/-- The structured core lies in the selected progression. -/
theorem core_subset_progression : S.core ⊆ S.progression.carrier :=
  (Finset.subset_insert 0 S.core).trans S.witness.core_zero_subset

/-- The structured core written in the coefficient lattice of the selected
proper progression. -/
def identifiedCore : Finset (BoxPoint S.dimension) :=
  coordinateImage S.progression S.witness.progression_proper S.core
    S.core_subset_progression

/-- Identification preserves the size of the structured core. -/
@[simp] theorem card_identifiedCore : S.identifiedCore.card = S.core.card :=
  card_coordinateImage S.progression S.witness.progression_proper S.core
    S.core_subset_progression

/-- Every identified core point belongs to the full coefficient box. -/
theorem identifiedCore_subset_coefficientBox :
    S.identifiedCore ⊆ (gapCoefficientBox S.progression).carrier :=
  coordinateImage_subset_coefficientBox S.progression
    S.witness.progression_proper S.core S.core_subset_progression

/-- Nonaveraging passes from the input to its identified structured core. -/
theorem identifiedCore_nonaveraging (hA : IsBoxNonaveraging A) :
    IsBoxNonaveraging S.identifiedCore := by
  apply coordinateImage_nonaveraging S.progression
    S.witness.progression_proper S.core_subset_progression
  exact PZ.isBoxNonaveraging_mono hA S.witness.core_subset

end SelectedCFP

namespace CFPSelector

variable (selector : CFPSelector)

/-- The concrete CFP selection at a nonempty input. -/
abbrev chosen {d : ℕ} (A : Finset (BoxPoint d)) (hA : A.Nonempty) :
    SelectedCFP A := selector.select A hA

end CFPSelector

/-- Translation preserves nonemptiness. -/
theorem pzTranslate_nonempty {d : ℕ} (v : BoxPoint d)
    {A : Finset (BoxPoint d)} (hA : A.Nonempty) :
    (PZ.translate v A).Nonempty := by
  apply Finset.card_pos.mp
  simpa using hA.card_pos

/-- The set obtained from an identified subset by translation in coefficient
space. -/
def identifiedTranslate {r : ℕ} (X : Finset (BoxPoint r))
    (x : BoxPoint r) : Finset (BoxPoint r) :=
  PZ.translate (-x) X

@[simp] theorem card_identifiedTranslate {r : ℕ}
    (X : Finset (BoxPoint r)) (x : BoxPoint r) :
    (identifiedTranslate X x).card = X.card := by
  simp [identifiedTranslate]

theorem identifiedTranslate_nonempty {r : ℕ}
    {X : Finset (BoxPoint r)} (hX : X.Nonempty) (x : BoxPoint r) :
    (identifiedTranslate X x).Nonempty :=
  pzTranslate_nonempty (-x) hX

/-- **Pham--Zakharov Definition 9.**

Every sufficiently dense subset of the identified CFP core, after
translation by a point of the full coefficient box, has the same selected
subset-sum dimension and a selected progression at least a `gamma` fraction
as large as the current progression. -/
def IsCoordinateIrreducible (selector : CFPSelector) {d : ℕ}
    (A : Finset (BoxPoint d)) (hA : A.Nonempty) (δ γ : ℝ) : Prop :=
  let S := selector.chosen A hA
  ∀ (X : Finset (BoxPoint S.dimension)),
    X ⊆ S.identifiedCore → (hXne : X.Nonempty) →
      δ * (A.card : ℝ) ≤ (X.card : ℝ) →
        ∀ x ∈ (gapCoefficientBox S.progression).carrier,
          let shifted := identifiedTranslate X x
          let T := selector.chosen shifted
            (identifiedTranslate_nonempty hXne x)
          T.dimension = S.dimension ∧
            γ * (S.progression.volume : ℝ) ≤
              (T.progression.volume : ℝ)

/-- A concrete witness to failure of Definition 9. -/
structure IrreducibilityFailure (selector : CFPSelector) {d : ℕ}
    (A : Finset (BoxPoint d)) (hA : A.Nonempty) (δ γ : ℝ) where
  retained : Finset (BoxPoint (selector.chosen A hA).dimension)
  retained_subset : retained ⊆ (selector.chosen A hA).identifiedCore
  retained_nonempty : retained.Nonempty
  dense : δ * (A.card : ℝ) ≤ (retained.card : ℝ)
  translationPoint : BoxPoint (selector.chosen A hA).dimension
  translationPoint_mem : translationPoint ∈
    (gapCoefficientBox (selector.chosen A hA).progression).carrier
  fails :
    let shifted := identifiedTranslate retained translationPoint
    let T := selector.chosen shifted
      (identifiedTranslate_nonempty retained_nonempty translationPoint)
    T.dimension ≠ (selector.chosen A hA).dimension ∨
      (T.progression.volume : ℝ) <
        γ * ((selector.chosen A hA).progression.volume : ℝ)

namespace IrreducibilityFailure

variable {selector : CFPSelector} {d : ℕ}
  {A : Finset (BoxPoint d)} {hA : A.Nonempty} {δ γ : ℝ}
  (F : IrreducibilityFailure selector A hA δ γ)

/-- The actual translated next input selected by a failure. -/
def nextPoints :
    Finset (BoxPoint (selector.chosen A hA).dimension) :=
  identifiedTranslate F.retained F.translationPoint

theorem nextPoints_nonempty : F.nextPoints.Nonempty :=
  identifiedTranslate_nonempty F.retained_nonempty F.translationPoint

/-- A failing replacement loses no points before the next CFP core is
selected. -/
@[simp] theorem card_nextPoints : F.nextPoints.card = F.retained.card := by
  simp [nextPoints]

/-- Nonaveraging is preserved by passing to an identified dense subset and
then translating it. -/
theorem nextPoints_nonaveraging (hNA : IsBoxNonaveraging A) :
    IsBoxNonaveraging F.nextPoints := by
  have hidentified : IsBoxNonaveraging
      (selector.chosen A hA).identifiedCore :=
    (selector.chosen A hA).identifiedCore_nonaveraging hNA
  have hretained : IsBoxNonaveraging F.retained :=
    PZ.isBoxNonaveraging_mono hidentified F.retained_subset
  exact PZ.isBoxNonaveraging_translate (-F.translationPoint) hretained

/-- The exact retention inequality before the next CFP loss. -/
theorem dense_nextPoints :
    δ * (A.card : ℝ) ≤ (F.nextPoints.card : ℝ) := by
  simpa using F.dense

end IrreducibilityFailure

/-- Logical normal form of failure of Definition 9. -/
theorem not_coordinateIrreducible_iff
    (selector : CFPSelector) {d : ℕ}
    (A : Finset (BoxPoint d)) (hA : A.Nonempty) (δ γ : ℝ) :
    ¬ IsCoordinateIrreducible selector A hA δ γ ↔
      Nonempty (IrreducibilityFailure selector A hA δ γ) := by
  classical
  let S := selector.chosen A hA
  constructor
  · intro hnot
    simp only [IsCoordinateIrreducible] at hnot
    push Not at hnot
    obtain ⟨X, hXsub, hXne, hdense, x, hx, hfail⟩ := hnot
    refine ⟨{
      retained := X
      retained_subset := hXsub
      retained_nonempty := hXne
      dense := hdense
      translationPoint := x
      translationPoint_mem := hx
      fails := ?_ }⟩
    dsimp only
    by_cases hdim :
        (selector.chosen (identifiedTranslate X x)
          (identifiedTranslate_nonempty hXne x)).dimension = S.dimension
    · exact Or.inr (hfail hdim)
    · exact Or.inl hdim
  · rintro ⟨F⟩ hirr
    have hgood := hirr F.retained F.retained_subset F.retained_nonempty
      F.dense F.translationPoint F.translationPoint_mem
    rcases F.fails with hdim | hvolume
    · exact hdim hgood.1
    · exact (not_lt_of_ge hgood.2) hvolume

end

end Erdos186.PZ.Reduction
