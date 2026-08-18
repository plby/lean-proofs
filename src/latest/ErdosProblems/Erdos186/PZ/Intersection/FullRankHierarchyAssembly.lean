/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProjectionNumerics
import ErdosProblems.Erdos186.PZ.Intersection.SideLatticeAssembly

/-!
# Full-rank side lattices from the source parameter hierarchy

This is the two-side assembly consumed by the Theorem 4 construction.  The
selected progressions share one controlled integer box and each retain a
`gamma` fraction of the reference progression volume.  The hierarchy makes
their proper dilation scale large enough for the projection-cardinality
criterion, so their step lattices are full rank and have the required common
covering radius.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Two selected side progressions satisfying the source box, volume, and
scale hierarchy give the complete lattice conclusion used in Theorem 4. -/
theorem fullRankLatticeCovolumeConclusion_of_controlledBoxGammaHierarchy
    {d k₁ k₂ ambient rank Q : ℕ}
    {A₁ A₂ : Finset (LatticePoint (d + 1))}
    {a : LatticePoint (d + 1)}
    (I₁ : IntersectionSideInput A₁ a .forward)
    (I₂ : IntersectionSideInput A₂ a .reverse)
    (P₁ P₂ : GAP (d + 1) (d + 1))
    (S : GAP ambient rank)
    (hlattice₁ : I₁.lattice =
      (stepLattice P₁ : Set (LatticePoint (d + 1))))
    (hlattice₂ : I₂.lattice =
      (stepLattice P₂ : Set (LatticePoint (d + 1))))
    (B : CFP.IntegerBox (d + 1))
    (t₁ t₂ : LatticePoint (d + 1))
    (gamma : ℝ)
    (hcontain₁ : P₁.carrier ⊆ CFP.translate t₁ B.carrier)
    (hcontain₂ : P₂.carrier ⊆ CFP.translate t₂ B.carrier)
    (hnondegenerate₁ : P₁.Nondegenerate)
    (hnondegenerate₂ : P₂.Nondegenerate)
    (hproper₁ : (P₁.dilate k₁).Proper)
    (hproper₂ : (P₂.dilate k₂).Proper)
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hbox : B.carrier.card ≤ Q * S.volume)
    (hvolume₁ : gamma * (S.volume : ℝ) ≤ (P₁.volume : ℝ))
    (hvolume₂ : gamma * (S.volume : ℝ) ≤ (P₂.volume : ℝ))
    (hgamma : 0 < gamma)
    (hhierarchy₁ :
      ((2 ^ (d + 1) * (2 * (d + 1) + 1) ^ d * Q : ℕ) : ℝ) <
        (k₁ : ℝ) * gamma)
    (hhierarchy₂ :
      ((2 ^ (d + 1) * (2 * (d + 1) + 1) ^ d * Q : ℕ) : ℝ) <
        (k₂ : ℝ) * gamma) :
    FullRankLatticeCovolumeConclusion I₁ I₂
      ((stepMatrix P₁).det.natAbs ^ (d + 1) *
        (stepMatrix P₂).det.natAbs ^ (d + 1)) := by
  have hdet₁ : (stepMatrix P₁).det ≠ 0 :=
    det_ne_zero_of_controlled_box_gamma_hierarchy
      P₁ S B t₁ gamma hcontain₁ hnondegenerate₁ hproper₁ hk₁
      hbox hvolume₁ hgamma hhierarchy₁
  have hdet₂ : (stepMatrix P₂).det ≠ 0 :=
    det_ne_zero_of_controlled_box_gamma_hierarchy
      P₂ S B t₂ gamma hcontain₂ hnondegenerate₂ hproper₂ hk₂
      hbox hvolume₂ hgamma hhierarchy₂
  exact fullRankLatticeCovolumeConclusion_of_stepLattices
    I₁ I₂ P₁ P₂ hlattice₁ hlattice₂ hdet₁ hdet₂

end

end Erdos186.PZ.Intersection
