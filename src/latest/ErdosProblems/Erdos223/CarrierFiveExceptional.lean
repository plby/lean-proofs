/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.CarrierFiveCompletion

/-!
# Exceptional vertices relative to a five-dimensional weak carrier

The two strong orientations of a weak carrier cover exactly its two crossed
spheres.  A point outside that union has affine-rank-at-most-two unit-neighbor
sets on both spheres.  This is the exact conclusion supplied by full-rank
completion; eliminating the remaining low-rank branch needs a separate
extremal or incidence estimate.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos223.FiveWeakCarrier.Carrier

noncomputable section

variable (C : FiveWeakCarrier.Carrier)

/-- The part of `A` in the strong orientation with the first sphere active. -/
def firstOrientedPart (A : Finset (Point 5)) : Finset (Point 5) := by
  classical
  exact A.filter fun x => x ∈ C.firstSphere ∨ x ∈ C.secondCircle

/-- The part of `A` in the opposite strong orientation. -/
def secondOrientedPart (A : Finset (Point 5)) : Finset (Point 5) := by
  classical
  exact A.filter fun x => x ∈ C.firstCircle ∨ x ∈ C.secondSphere

/-- Unit neighbors of `q` which lie in a prescribed carrier set. -/
def unitNeighborsOn (A : Finset (Point 5)) (S : Set (Point 5))
    (q : Point 5) : Finset (Point 5) := by
  classical
  exact A.filter fun x => x ∈ S ∧ dist q x = 1

@[simp] theorem mem_firstOrientedPart {A : Finset (Point 5)} {x : Point 5} :
    x ∈ C.firstOrientedPart A ↔
      x ∈ A ∧ (x ∈ C.firstSphere ∨ x ∈ C.secondCircle) := by
  simp [firstOrientedPart]

@[simp] theorem mem_secondOrientedPart {A : Finset (Point 5)} {x : Point 5} :
    x ∈ C.secondOrientedPart A ↔
      x ∈ A ∧ (x ∈ C.firstCircle ∨ x ∈ C.secondSphere) := by
  simp [secondOrientedPart]

@[simp] theorem mem_unitNeighborsOn {A : Finset (Point 5)}
    {S : Set (Point 5)} {q x : Point 5} :
    x ∈ unitNeighborsOn A S q ↔ x ∈ A ∧ x ∈ S ∧ dist q x = 1 := by
  simp [unitNeighborsOn]

/-- The union of the two oriented parts is exactly the part of `A` on the
weak carrier. -/
theorem mem_firstOrientedPart_or_secondOrientedPart_iff
    {A : Finset (Point 5)} {x : Point 5} :
    x ∈ C.firstOrientedPart A ∨ x ∈ C.secondOrientedPart A ↔
      x ∈ A ∧ (x ∈ C.firstSphere ∨ x ∈ C.secondSphere) := by
  constructor
  · rintro (hx | hx)
    · rcases (C.mem_firstOrientedPart.mp hx) with ⟨hxA, hxS | hxC⟩
      · exact ⟨hxA, Or.inl hxS⟩
      · exact ⟨hxA, Or.inr (C.secondCircle_subset_secondSphere hxC)⟩
    · rcases (C.mem_secondOrientedPart.mp hx) with ⟨hxA, hxC | hxS⟩
      · exact ⟨hxA, Or.inl (C.firstCircle_subset_firstSphere hxC)⟩
      · exact ⟨hxA, Or.inr hxS⟩
  · rintro ⟨hxA, hxS | hxS⟩
    · exact Or.inl (C.mem_firstOrientedPart.mpr ⟨hxA, Or.inl hxS⟩)
    · exact Or.inr (C.mem_secondOrientedPart.mpr ⟨hxA, Or.inr hxS⟩)

/-- A point off the weak carrier has only affine-rank-at-most-two unit
neighbor sets on each of the two carrier spheres. -/
theorem unitNeighbor_ranks_le_two_of_not_mem_weakCarrier
    (A : Finset (Point 5)) (q : Point 5)
    (hq : q ∉ C.firstSphere ∪ C.secondSphere) :
    Module.finrank ℝ
        (affineSpan ℝ (unitNeighborsOn A C.firstSphere q : Set (Point 5))).direction ≤ 2 ∧
      Module.finrank ℝ
        (affineSpan ℝ (unitNeighborsOn A C.secondSphere q : Set (Point 5))).direction ≤ 2 := by
  have hq' : q ∉ C.firstSphere ∧ q ∉ C.secondSphere := by
    simpa only [Set.mem_union, not_or] using hq
  have hqSecondCircle : q ∉ C.secondCircle := fun h =>
    hq'.2 (C.secondCircle_subset_secondSphere h)
  have hqFirstCircle : q ∉ C.firstCircle := fun h =>
    hq'.1 (C.firstCircle_subset_firstSphere h)
  constructor
  · apply C.unitNeighbors_firstSphere_finrank_le_two
    · intro x hx
      exact (mem_unitNeighborsOn.mp hx).2.1
    · exact hqSecondCircle
    · intro x hx
      exact (mem_unitNeighborsOn.mp hx).2.2
  · apply C.unitNeighbors_secondSphere_finrank_le_two
    · intro x hx
      exact (mem_unitNeighborsOn.mp hx).2.1
    · exact hqFirstCircle
    · intro x hx
      exact (mem_unitNeighborsOn.mp hx).2.2

/-- Exact exceptional-vertex dichotomy supplied by the carrier completion
lemmas. -/
theorem mem_weakCarrier_or_unitNeighbor_ranks_le_two
    (A : Finset (Point 5)) (q : Point 5) :
    q ∈ C.firstSphere ∪ C.secondSphere ∨
      (Module.finrank ℝ
          (affineSpan ℝ (unitNeighborsOn A C.firstSphere q : Set (Point 5))).direction ≤ 2 ∧
        Module.finrank ℝ
          (affineSpan ℝ (unitNeighborsOn A C.secondSphere q : Set (Point 5))).direction ≤ 2) := by
  by_cases hq : q ∈ C.firstSphere ∪ C.secondSphere
  · exact Or.inl hq
  · exact Or.inr (C.unitNeighbor_ranks_le_two_of_not_mem_weakCarrier A q hq)

/-- Four independent unit neighbors on one of the carrier spheres put a
point into the corresponding oriented part. -/
theorem mem_orientedPart_of_fullRank_anchor
    {A : Finset (Point 5)} {q : Point 5} (hqA : q ∈ A)
    (hanchor :
      (∃ a : Fin 4 → Point 5, AffineIndependent ℝ a ∧
        (∀ i, a i ∈ C.firstSphere) ∧ (∀ i, dist q (a i) = 1)) ∨
      (∃ b : Fin 4 → Point 5, AffineIndependent ℝ b ∧
        (∀ i, b i ∈ C.secondSphere) ∧ (∀ i, dist q (b i) = 1))) :
    q ∈ C.firstOrientedPart A ∨ q ∈ C.secondOrientedPart A := by
  rcases hanchor with ⟨a, ha, hamem, hqa⟩ | ⟨b, hb, hbmem, hqb⟩
  · left
    exact C.mem_firstOrientedPart.mpr
      ⟨hqA, Or.inr (C.mem_secondCircle_of_unit_to_firstSphere_anchor a ha hamem q hqa)⟩
  · right
    exact C.mem_secondOrientedPart.mpr
      ⟨hqA, Or.inl (C.mem_firstCircle_of_unit_to_secondSphere_anchor b hb hbmem q hqb)⟩

end

end Erdos223.FiveWeakCarrier.Carrier
