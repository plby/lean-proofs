/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularSpatialSpliceKernelDefs
import ErdosProblems.Erdos1165.AnnularSpatialSplice

/-! Boundary facts used by the finite-domain interpretation of spatial splices. -/

open Set

namespace Erdos1165.AnnularSpatialSpliceBoundaryFacts

open AnnularSpatialSpliceKernelDefs Annulus LiteralRealAnnulus
  LiteralRealAnnulusRadialExit PlanarPotential RealDiscFinite ThickPoint

noncomputable section

theorem scaleRadius_zero_nonneg (n : ℕ) : 0 ≤ scaleRadius n 0 := by
  simp only [scaleRadius_of_le (Nat.zero_le n), regularRadius,
    Nat.cast_zero, sub_zero]
  positivity

theorem initial_outerBoundary_subset (n : ℕ) :
    ↑(outerBoundary (literalRealAnnulus (scaleRadius n 1)
      (8 * scaleRadius n 0) ⌈8 * scaleRadius n 0⌉₊)) ⊆
        (↑(discBoundaryFinset 0 (scaleRadius n 1)) : Set Point) ∪
          discBoundary 0 (8 * scaleRadius n 0) := by
  intro y hy
  have hyUnion : y ∈
      literalRealAnnulusInnerExit (scaleRadius n 1) (8 * scaleRadius n 0)
          ⌈8 * scaleRadius n 0⌉₊ ∪
        literalRealAnnulusOuterExit (scaleRadius n 1) (8 * scaleRadius n 0)
          ⌈8 * scaleRadius n 0⌉₊ := by
    rwa [literalRealAnnulus_exit_union]
  rcases Finset.mem_union.mp hyUnion with hyInner | hyOuter
  · exact Or.inl (mem_discBoundaryFinset.mpr
      (literalRealAnnulusInnerExit_subset_discBoundary hyInner))
  · exact Or.inr (literalRealAnnulusOuterExit_subset_discBoundary
      (mul_nonneg (by norm_num) (scaleRadius_zero_nonneg n))
      (Nat.le_ceil _) hyOuter)

theorem initial_interior_avoids_boundary (n : ℕ) :
    ∀ y, y ∈ literalRealAnnulus (scaleRadius n 1)
      (8 * scaleRadius n 0) ⌈8 * scaleRadius n 0⌉₊ →
      y ∉ (↑(discBoundaryFinset 0 (scaleRadius n 1)) : Set Point) ∪
        discBoundary 0 (8 * scaleRadius n 0) := by
  intro y hyD hyBoundary
  rcases hyBoundary with hyInner | hyOuter
  · exact (mem_literalRealAnnulus_raw.mp hyD).2.2.2
      (mem_discBoundaryFinset.mp hyInner).1
  · exact (mem_literalRealAnnulus_raw.mp hyD).2.2.1 hyOuter

theorem initial_interior_disjoint_mark (n : ℕ) :
    Disjoint (literalRealAnnulus (scaleRadius n 1)
      (8 * scaleRadius n 0) ⌈8 * scaleRadius n 0⌉₊)
      (discBoundaryFinset 0 (scaleRadius n 1)) := by
  rw [Finset.disjoint_left]
  intro y hyD hyB
  exact (mem_literalRealAnnulus_raw.mp hyD).2.2.2
    (mem_discBoundaryFinset.mp hyB).1

theorem final_outerBoundary_subset (n : ℕ) :
    ↑(outerBoundary (literalRealAnnulus (scaleRadius n 1)
      (32 * scaleRadius n 0) ⌈32 * scaleRadius n 0⌉₊)) ⊆
        discBoundary 0 (scaleRadius n 1) ∪
          (↑(discBoundaryFinset 0 (32 * scaleRadius n 0)) : Set Point) := by
  intro y hy
  have hyUnion : y ∈
      literalRealAnnulusInnerExit (scaleRadius n 1) (32 * scaleRadius n 0)
          ⌈32 * scaleRadius n 0⌉₊ ∪
        literalRealAnnulusOuterExit (scaleRadius n 1) (32 * scaleRadius n 0)
          ⌈32 * scaleRadius n 0⌉₊ := by
    rwa [literalRealAnnulus_exit_union]
  rcases Finset.mem_union.mp hyUnion with hyInner | hyOuter
  · exact Or.inl (literalRealAnnulusInnerExit_subset_discBoundary hyInner)
  · exact Or.inr (mem_discBoundaryFinset.mpr
      (literalRealAnnulusOuterExit_subset_discBoundary
        (mul_nonneg (by norm_num) (scaleRadius_zero_nonneg n))
        (Nat.le_ceil _) hyOuter))

theorem final_interior_avoids_boundary (n : ℕ) :
    ∀ y, y ∈ literalRealAnnulus (scaleRadius n 1)
      (32 * scaleRadius n 0) ⌈32 * scaleRadius n 0⌉₊ →
      y ∉ discBoundary 0 (scaleRadius n 1) ∪
        (↑(discBoundaryFinset 0 (32 * scaleRadius n 0)) : Set Point) := by
  intro y hyD hyBoundary
  rcases hyBoundary with hyInner | hyOuter
  · exact (mem_literalRealAnnulus_raw.mp hyD).2.2.2 hyInner.1
  · exact (mem_literalRealAnnulus_raw.mp hyD).2.2.1
      (mem_discBoundaryFinset.mp hyOuter)

theorem final_interior_disjoint_mark (n : ℕ) :
    Disjoint (literalRealAnnulus (scaleRadius n 1)
      (32 * scaleRadius n 0) ⌈32 * scaleRadius n 0⌉₊)
      (discBoundaryFinset 0 (32 * scaleRadius n 0)) := by
  rw [Finset.disjoint_left]
  intro y hyD hyB
  exact (mem_literalRealAnnulus_raw.mp hyD).2.2.1
    (mem_discBoundaryFinset.mp hyB)

end

end Erdos1165.AnnularSpatialSpliceBoundaryFacts
