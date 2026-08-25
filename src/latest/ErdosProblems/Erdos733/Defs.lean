/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Util.IncidenceGeometry.IsAffineLine
import Mathlib.Data.Multiset.Sort

/-!
# Erdős Problem 733: definitions

The witnesses use a `Finset` of affine lines.  Thus the geometric lines are
distinct, while equal line cardinalities retain their multiplicity in the
resulting multiset.
-/

namespace Erdos733

open Classical

noncomputable section

/-- The real Euclidean plane used in the incidence theorem. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A nonempty affine subspace of real dimension one. -/
abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

/-- The number of points of `P` lying on `ℓ`. -/
def lineCount (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ.1 : AffineSubspace ℝ Point)).card

/-- The multiset of cardinalities of the distinct lines in `L`. -/
def lineSizeMultiset (P : Finset Point) (L : Finset Line) : Multiset ℕ :=
  L.1.map (lineCount P)

/-- The canonical nondecreasing list representing the line-size multiset. -/
def lineSizeSequence (P : Finset Point) (L : Finset Line) : List ℕ :=
  (lineSizeMultiset P L).sort (· ≤ ·)

/-- Exact line compatibility from Erdős Problem 733.

The finset `L` enforces that the witnessing geometric lines are distinct.
Different members of `L` may have the same value of `lineCount`, which is
why the output is a list (equivalently a multiset) with repetitions. -/
def LineCompatible (n : ℕ) (X : List ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧
    ∃ L : Finset Line,
      (∀ ℓ ∈ L, 2 ≤ lineCount P ℓ) ∧
        X = lineSizeSequence P L

/-- The set counted in the statement of Problem 733. -/
def compatibleSequences (n : ℕ) : Set (List ℕ) :=
  {X | LineCompatible n X}

@[simp]
lemma lineSizeSequence_toMultiset (P : Finset Point) (L : Finset Line) :
    ((lineSizeSequence P L : List ℕ) : Multiset ℕ) = lineSizeMultiset P L := by
  exact Multiset.sort_eq _ _

lemma lineSizeSequence_sorted (P : Finset Point) (L : Finset Line) :
    (lineSizeSequence P L).Pairwise (· ≤ ·) := by
  exact Multiset.pairwise_sort _ _

lemma lineCount_le_card (P : Finset Point) (ℓ : Line) :
    lineCount P ℓ ≤ P.card := by
  exact Finset.card_filter_le _ _

lemma lineSizeMultiset_mem_bounds {P : Finset Point} {L : Finset Line}
    (hL : ∀ ℓ ∈ L, 2 ≤ lineCount P ℓ) {x : ℕ}
    (hx : x ∈ lineSizeMultiset P L) :
    2 ≤ x ∧ x ≤ P.card := by
  rw [lineSizeMultiset, Multiset.mem_map] at hx
  obtain ⟨ℓ, hℓ, rfl⟩ := hx
  have hℓL : ℓ ∈ L := by simpa using hℓ
  exact ⟨hL ℓ hℓL, lineCount_le_card P ℓ⟩

lemma LineCompatible.sorted {n : ℕ} {X : List ℕ}
    (hX : LineCompatible n X) : X.Pairwise (· ≤ ·) := by
  obtain ⟨P, _hP, L, _hL, rfl⟩ := hX
  exact lineSizeSequence_sorted P L

lemma LineCompatible.mem_bounds {n : ℕ} {X : List ℕ}
    (hX : LineCompatible n X) {x : ℕ} (hx : x ∈ X) :
    2 ≤ x ∧ x ≤ n := by
  obtain ⟨P, hP, L, hL, rfl⟩ := hX
  have hx' : x ∈ lineSizeMultiset P L := by
    rw [← lineSizeSequence_toMultiset]
    exact Multiset.mem_coe.mpr hx
  simpa only [hP] using lineSizeMultiset_mem_bounds hL hx'

end

end Erdos733
