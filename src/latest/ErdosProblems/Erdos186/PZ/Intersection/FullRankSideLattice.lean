/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProjectionCardinality
import ErdosProblems.Erdos186.PZ.Intersection.SideLatticeAssembly

/-!
# Full-rank side lattices from the projection count

This file composes the quantitative projection-cardinality contradiction
with the concrete step-lattice construction.  It eliminates the abstract
`FullRankLatticeCovolumeConclusion` input once each side progression is
known to lie in a controlled integer box and its proper dilation is large
enough to beat every codimension-one projection of that box.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Two source-controlled square progressions give the complete common
covering-radius conclusion for their step lattices. -/
theorem fullRankLatticeCovolumeConclusion_of_projectionBounds
    {d k₁ k₂ : ℕ}
    {A₁ A₂ : Finset (LatticePoint (d + 1))}
    {a : LatticePoint (d + 1)}
    (I₁ : IntersectionSideInput A₁ a .forward)
    (I₂ : IntersectionSideInput A₂ a .reverse)
    (P₁ P₂ : GAP (d + 1) (d + 1))
    (hlattice₁ : I₁.lattice =
      (stepLattice P₁ : Set (LatticePoint (d + 1))))
    (hlattice₂ : I₂.lattice =
      (stepLattice P₂ : Set (LatticePoint (d + 1))))
    (B₁ B₂ : CFP.IntegerBox (d + 1))
    (t₁ t₂ : LatticePoint (d + 1))
    (hcontain₁ : P₁.carrier ⊆ CFP.translate t₁ B₁.carrier)
    (hcontain₂ : P₂.carrier ⊆ CFP.translate t₂ B₂.carrier)
    (hnondegenerate₁ : P₁.Nondegenerate)
    (hnondegenerate₂ : P₂.Nondegenerate)
    (hproper₁ : (P₁.dilate k₁).Proper)
    (hproper₂ : (P₂.dilate k₂).Proper)
    (hlarge₁ : ∀ j₀ : Fin (d + 1),
      2 ^ (d + 1) *
          (∏ j : Fin d,
            (2 * projectionRadius k₁ B₁ (j₀.succAbove j) + 1)) <
        k₁ ^ (d + 1) * P₁.volume)
    (hlarge₂ : ∀ j₀ : Fin (d + 1),
      2 ^ (d + 1) *
          (∏ j : Fin d,
            (2 * projectionRadius k₂ B₂ (j₀.succAbove j) + 1)) <
        k₂ ^ (d + 1) * P₂.volume) :
    FullRankLatticeCovolumeConclusion I₁ I₂
      ((stepMatrix P₁).det.natAbs ^ (d + 1) *
        (stepMatrix P₂).det.natAbs ^ (d + 1)) := by
  have hdet₁ : (stepMatrix P₁).det ≠ 0 :=
    det_ne_zero_of_pow_mul_volume_gt_projection_bound P₁ B₁ t₁ hcontain₁
      hnondegenerate₁ hproper₁ hlarge₁
  have hdet₂ : (stepMatrix P₂).det ≠ 0 :=
    det_ne_zero_of_pow_mul_volume_gt_projection_bound P₂ B₂ t₂ hcontain₂
      hnondegenerate₂ hproper₂ hlarge₂
  exact fullRankLatticeCovolumeConclusion_of_stepLattices I₁ I₂ P₁ P₂
    hlattice₁ hlattice₂ hdet₁ hdet₂

end

end Erdos186.PZ.Intersection
