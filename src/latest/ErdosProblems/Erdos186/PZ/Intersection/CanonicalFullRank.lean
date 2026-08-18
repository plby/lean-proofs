/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProjectionNumerics
import ErdosProblems.Erdos186.PZ.Intersection.SideLattice
import ErdosProblems.Erdos186.PZ.Intersection.RankCastGAP

/-!
# Full rank for the canonical side-witness lattices

Lemma 11 identifies each selected progression rank with the ambient
coefficient dimension.  After transporting across that equality, the
controlled-box `k * gamma` hierarchy applies directly.  This file packages
the resulting common covering-radius theorem in terms of the original
enhanced witnesses, exactly matching the canonical targets in
`SideTarget.lean`.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The two enhanced side witnesses have full-rank step lattices and the
explicit determinant-power common covering radius. -/
theorem enhancedWitnesses_commonCoveringRadius_of_controlledBoxGammaHierarchy
    {d s₁ D₁ k₁ loss₁ s₂ D₂ k₂ loss₂ ambient rank Q : ℕ}
    {X₁ X₂ : Finset (LatticePoint (d + 1))}
    (W₁ : CFP.EnhancedCFPWitness X₁ s₁ D₁ k₁ loss₁)
    (W₂ : CFP.EnhancedCFPWitness X₂ s₂ D₂ k₂ loss₂)
    (hrank₁ : W₁.rank = d + 1) (hrank₂ : W₂.rank = d + 1)
    (S : GAP ambient rank) (B : CFP.IntegerBox (d + 1))
    (t₁ t₂ : LatticePoint (d + 1)) (gamma : ℝ)
    (hcontain₁ : W₁.progression.carrier ⊆ CFP.translate t₁ B.carrier)
    (hcontain₂ : W₂.progression.carrier ⊆ CFP.translate t₂ B.carrier)
    (hbox : B.carrier.card ≤ Q * S.volume)
    (hvolume₁ : gamma * (S.volume : ℝ) ≤ (W₁.progression.volume : ℝ))
    (hvolume₂ : gamma * (S.volume : ℝ) ≤ (W₂.progression.volume : ℝ))
    (hgamma : 0 < gamma)
    (hhierarchy₁ :
      ((2 ^ (d + 1) * (2 * (d + 1) + 1) ^ d * Q : ℕ) : ℝ) <
        (k₁ : ℝ) * gamma)
    (hhierarchy₂ :
      ((2 ^ (d + 1) * (2 * (d + 1) + 1) ^ d * Q : ℕ) : ℝ) <
        (k₂ : ℝ) * gamma) :
    HasCommonCoveringRadius
      (gapStepLattice W₁.progression : Set (LatticePoint (d + 1)))
      (gapStepLattice W₂.progression : Set (LatticePoint (d + 1)))
      ((stepMatrix (rankCastGAP W₁.progression hrank₁)).det.natAbs ^ (d + 1) *
        (stepMatrix (rankCastGAP W₂.progression hrank₂)).det.natAbs ^
          (d + 1)) := by
  let P₁ := rankCastGAP W₁.progression hrank₁
  let P₂ := rankCastGAP W₂.progression hrank₂
  have hdet₁ : (stepMatrix P₁).det ≠ 0 := by
    apply det_ne_zero_of_controlled_box_gamma_hierarchy P₁ S B t₁ gamma
    · simpa only [P₁, rankCastGAP_carrier] using hcontain₁
    · exact rankCastGAP_nondegenerate hrank₁ W₁.progression_nondegenerate
    · exact rankCastGAP_dilate_proper hrank₁ W₁.dilate_proper
    · exact W₁.k_pos
    · exact hbox
    · simpa [P₁, rankCastGAP_volume] using hvolume₁
    · exact hgamma
    · exact hhierarchy₁
  have hdet₂ : (stepMatrix P₂).det ≠ 0 := by
    apply det_ne_zero_of_controlled_box_gamma_hierarchy P₂ S B t₂ gamma
    · simpa only [P₂, rankCastGAP_carrier] using hcontain₂
    · exact rankCastGAP_nondegenerate hrank₂ W₂.progression_nondegenerate
    · exact rankCastGAP_dilate_proper hrank₂ W₂.dilate_proper
    · exact W₂.k_pos
    · exact hbox
    · simpa [P₂, rankCastGAP_volume] using hvolume₂
    · exact hgamma
    · exact hhierarchy₂
  have hcover := stepLattices_commonCoveringRadius P₁ P₂ hdet₁ hdet₂
  simpa [P₁, P₂, rankCastGAP_stepLattice] using hcover

end

end Erdos186.PZ.Intersection
