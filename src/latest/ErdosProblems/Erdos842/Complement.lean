/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos842.Coefficient

/-!
# Complementation of canonical arc selections for Erdős Problem 842

The canonical indexed orientation has two incoming and two outgoing occurrences at every vertex.
Consequently, the complement of an Eulerian (`Balanced`) occurrence selection is again Eulerian.
On each directed triangle, complementation exchanges the empty and full restrictions and exchanges
the two nondegenerate orientations of the same chord.  This gives a fixed-point-free, sign-
preserving involution on every survivor fibre as soon as the occurrence type is nonempty.
-/

namespace Erdos842.Complement

open Erdos842.Parity
open Erdos842.Coefficient

/-- Full complement of a canonical occurrence selection. -/
def canonicalComplement {n : ℕ}
    (S : Finset (CanonicalOccurrence n)) : Finset (CanonicalOccurrence n) :=
  Finset.univ \ S

@[simp] theorem mem_canonicalComplement {n : ℕ}
    (S : Finset (CanonicalOccurrence n)) (a : CanonicalOccurrence n) :
    a ∈ canonicalComplement S ↔ a ∉ S := by
  simp [canonicalComplement]

/-- Complementation is an involution on all canonical occurrence selections. -/
@[simp] theorem canonicalComplement_involutive {n : ℕ}
    (S : Finset (CanonicalOccurrence n)) :
    canonicalComplement (canonicalComplement S) = S := by
  ext a
  simp [canonicalComplement]

/-- The full canonical occurrence selection is balanced because both its indegree and outdegree
at every vertex are two. -/
theorem canonicalUniv_balanced (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    (canonicalIndexedArcs n triangleCoord).Balanced Finset.univ := by
  intro v
  exact (canonicalIndexedArcs_indegree_two n triangleCoord v).trans
    (canonicalIndexedArcs_outdegree_two n triangleCoord v).symm

/-- Complementation preserves balancedness. -/
theorem canonicalComplement_balanced {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : (canonicalIndexedArcs n triangleCoord).Balanced S) :
    (canonicalIndexedArcs n triangleCoord).Balanced (canonicalComplement S) := by
  exact balanced_sdiff_of_subset (Finset.subset_univ S)
    (canonicalUniv_balanced n triangleCoord) hS

/-- Balancedness is invariant under full complementation. -/
@[simp] theorem canonicalComplement_balanced_iff {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    (canonicalIndexedArcs n triangleCoord).Balanced (canonicalComplement S) ↔
      (canonicalIndexedArcs n triangleCoord).Balanced S := by
  constructor
  · intro hS
    simpa only [canonicalComplement_involutive] using
      (canonicalComplement_balanced triangleCoord hS)
  · exact canonicalComplement_balanced triangleCoord

/-- Restricting the global complement to a canonical triangle gives the complement of the
triangle restriction. -/
theorem canonicalRestriction_complement {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (i : Fin n) :
    (canonicalDirectedTriangle n triangleCoord i).restriction (canonicalComplement S) =
      Finset.univ \ (canonicalDirectedTriangle n triangleCoord i).restriction S := by
  exact (canonicalDirectedTriangle n triangleCoord i).restriction_compl S

/-- A triangle restriction is degenerate after complementation exactly when it was degenerate
before complementation. -/
theorem canonicalRestriction_complement_degenerate_iff {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (i : Fin n) :
    ((canonicalDirectedTriangle n triangleCoord i).restriction (canonicalComplement S) = ∅ ∨
      (canonicalDirectedTriangle n triangleCoord i).restriction (canonicalComplement S) =
        Finset.univ) ↔
      ((canonicalDirectedTriangle n triangleCoord i).restriction S = ∅ ∨
        (canonicalDirectedTriangle n triangleCoord i).restriction S = Finset.univ) := by
  simpa only [canonicalRestriction_complement,
    (canonicalDirectedTriangle n triangleCoord i).restriction_toggle] using
      (canonicalDirectedTriangle n triangleCoord i).restriction_toggle_degenerate_iff S

/-- Complementation leaves the set of degenerate canonical triangles unchanged. -/
@[simp] theorem canonicalDegenerateIndices_complement {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    canonicalDegenerateIndices n triangleCoord (canonicalComplement S) =
      canonicalDegenerateIndices n triangleCoord S := by
  classical
  ext i
  simp only [mem_canonicalDegenerateIndices]
  exact canonicalRestriction_complement_degenerate_iff triangleCoord S i

/-- Full complementation preserves membership in the canonical survivor set. -/
@[simp] theorem canonicalComplement_mem_survivors_iff {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    canonicalComplement S ∈ canonicalSurvivors n triangleCoord ↔
      S ∈ canonicalSurvivors n triangleCoord := by
  rw [mem_canonicalSurvivors, mem_canonicalSurvivors]
  simp only [canonicalComplement_balanced_iff, canonicalDegenerateIndices_complement]

/-- Forward form of survivor preservation, convenient when constructing fibre maps. -/
theorem canonicalComplement_mem_survivors {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivors n triangleCoord) :
    canonicalComplement S ∈ canonicalSurvivors n triangleCoord :=
  (canonicalComplement_mem_survivors_iff triangleCoord S).2 hS

/-- If the canonical occurrence type is nonempty, no selection equals its full complement. -/
theorem canonicalComplement_ne_of_nonempty {n : ℕ}
    (hocc : Nonempty (CanonicalOccurrence n))
    (S : Finset (CanonicalOccurrence n)) : canonicalComplement S ≠ S := by
  classical
  intro h
  let a : CanonicalOccurrence n := Classical.choice hocc
  by_cases ha : a ∈ S
  · have hac : a ∈ canonicalComplement S := by rw [h]; exact ha
    exact (mem_canonicalComplement S a).mp hac ha
  · have hac : a ∉ canonicalComplement S := by rw [h]; exact ha
    exact hac ((mem_canonicalComplement S a).mpr ha)

/-- For positive `n`, the occurrence type is nonempty, hence complementation is fixed-point-free. -/
theorem canonicalComplement_ne {n : ℕ} (hn : 0 < n)
    (S : Finset (CanonicalOccurrence n)) : canonicalComplement S ≠ S := by
  exact canonicalComplement_ne_of_nonempty
    ⟨Sum.inl ⟨0, by omega⟩⟩ S

/-- There are exactly `6n` canonical occurrences: `3n` cycle occurrences and `3n` triangle
occurrences. -/
theorem canonicalOccurrence_card_eq_six_mul (n : ℕ) :
    Fintype.card (CanonicalOccurrence n) = 6 * n := by
  simp [CanonicalOccurrence]
  omega

/-- The canonical occurrence type has even cardinality. -/
theorem canonicalOccurrence_card_even (n : ℕ) : Even (Fintype.card (CanonicalOccurrence n)) := by
  rw [canonicalOccurrence_card_eq_six_mul]
  exact ⟨3 * n, by omega⟩

/-- Full complementation preserves the subset-expansion sign: there are `6n`, hence an even
number, of canonical occurrences. -/
@[simp] theorem selectionSign_canonicalComplement {n : ℕ}
    (S : Finset (CanonicalOccurrence n)) :
    selectionSign (canonicalComplement S) = selectionSign S := by
  unfold selectionSign
  apply neg_one_pow_congr
  have hcard : (canonicalComplement S).card + S.card =
      Fintype.card (CanonicalOccurrence n) := by
    simpa [canonicalComplement] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have hsum : Even ((canonicalComplement S).card + S.card) := by
    rw [hcard]
    exact canonicalOccurrence_card_even n
  exact Nat.even_add.mp hsum

/-- Wrapper form of `canonicalChordKey_compl` using `canonicalComplement`. -/
@[simp] theorem canonicalChordKey_complement {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    canonicalChordKey n triangleCoord (canonicalComplement S) =
      canonicalChordKey n triangleCoord S := by
  exact canonicalChordKey_compl n triangleCoord S

/-- Survivors with a prescribed unoriented canonical chord key. -/
noncomputable def canonicalSurvivorFiber {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) : Finset (Finset (CanonicalOccurrence n)) :=
  (canonicalSurvivors n triangleCoord).filter fun S ↦
    canonicalChordKey n triangleCoord S = key

@[simp] theorem mem_canonicalSurvivorFiber {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (S : Finset (CanonicalOccurrence n)) :
    S ∈ canonicalSurvivorFiber triangleCoord key ↔
      S ∈ canonicalSurvivors n triangleCoord ∧
        canonicalChordKey n triangleCoord S = key := by
  classical
  simp [canonicalSurvivorFiber]

/-- Complementation preserves each survivor fibre, not merely the survivor set. -/
@[simp] theorem canonicalComplement_mem_survivorFiber_iff {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) (S : Finset (CanonicalOccurrence n)) :
    canonicalComplement S ∈ canonicalSurvivorFiber triangleCoord key ↔
      S ∈ canonicalSurvivorFiber triangleCoord key := by
  simp only [mem_canonicalSurvivorFiber, canonicalComplement_mem_survivors_iff,
    canonicalChordKey_complement]

/-- Forward fibre-preservation statement. -/
theorem canonicalComplement_mem_survivorFiber {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivorFiber triangleCoord key) :
    canonicalComplement S ∈ canonicalSurvivorFiber triangleCoord key :=
  (canonicalComplement_mem_survivorFiber_iff triangleCoord key S).2 hS

/-- The exact involutive, fixed-point-free and equal-sign data on a positive-`n` survivor fibre,
ready to be used as the fibre-pairing map. -/
theorem canonicalSurvivorFiber_complement_pairing {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) :
    (∀ S ∈ canonicalSurvivorFiber triangleCoord key,
        canonicalComplement S ∈ canonicalSurvivorFiber triangleCoord key) ∧
      (∀ S ∈ canonicalSurvivorFiber triangleCoord key,
        canonicalComplement (canonicalComplement S) = S) ∧
      (∀ S ∈ canonicalSurvivorFiber triangleCoord key,
        canonicalComplement S ≠ S) ∧
      (∀ S ∈ canonicalSurvivorFiber triangleCoord key,
        selectionSign (canonicalComplement S) = selectionSign S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hS
    exact canonicalComplement_mem_survivorFiber triangleCoord key hS
  · intro S _
    exact canonicalComplement_involutive S
  · intro S _
    exact canonicalComplement_ne hn S
  · intro S _
    exact selectionSign_canonicalComplement S

end Erdos842.Complement
