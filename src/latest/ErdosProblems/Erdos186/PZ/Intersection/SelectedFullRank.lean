/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionContainment
import ErdosProblems.Erdos186.PZ.Intersection.ProjectionNumerics
import ErdosProblems.Erdos186.PZ.Intersection.FullRankObstruction
import ErdosProblems.Erdos186.PZ.Intersection.SideLattice

/-!
# Full rank for the two selected side progressions

This file feeds the concrete Lemma-11 control box and volume lower bound into
the projection-cardinality criterion.  A side progression whose selected
rank equals its ambient coefficient dimension is transported to a square GAP;
the transport changes no carrier, volume, properness, or step lattice.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Transport only the displayed rank of a GAP. -/
def castGAPRank {d r r' : ℕ} (P : GAP d r) (h : r = r') : GAP d r' := by
  subst r'
  exact P

@[simp] theorem castGAPRank_carrier {d r r' : ℕ} (P : GAP d r)
    (h : r = r') : (castGAPRank P h).carrier = P.carrier := by
  subst r'
  rfl

@[simp] theorem castGAPRank_volume {d r r' : ℕ} (P : GAP d r)
    (h : r = r') : (castGAPRank P h).volume = P.volume := by
  subst r'
  rfl

theorem castGAPRank_nondegenerate {d r r' : ℕ} (P : GAP d r)
    (h : r = r') (hP : P.Nondegenerate) :
    (castGAPRank P h).Nondegenerate := by
  subst r'
  exact hP

theorem castGAPRank_dilate_proper {d r r' k : ℕ} (P : GAP d r)
    (h : r = r') (hP : (P.dilate k).Proper) :
    ((castGAPRank P h).dilate k).Proper := by
  subst r'
  exact hP

theorem gapStepLattice_castGAPRank {d r : ℕ} (P : GAP d r)
    (h : r = d) :
    gapStepLattice P = stepLattice (castGAPRank P h) := by
  subst r
  rfl

/-- A selected progression becomes square when its selected dimension equals
the ambient lattice dimension. -/
def selectedSquareProgression {d : ℕ} {A : Finset (LatticePoint d)}
    (T : Reduction.SelectedCFP A)
    (h : T.dimension = d) : GAP d d :=
  castGAPRank T.progression h

@[simp] theorem squareProgression_carrier
    {d : ℕ} {A : Finset (LatticePoint d)}
    (T : Reduction.SelectedCFP A) (h : T.dimension = d) :
    (selectedSquareProgression T h).carrier = T.progression.carrier :=
  castGAPRank_carrier T.progression h

@[simp] theorem squareProgression_volume
    {d : ℕ} {A : Finset (LatticePoint d)}
    (T : Reduction.SelectedCFP A) (h : T.dimension = d) :
    (selectedSquareProgression T h).volume = T.progression.volume :=
  castGAPRank_volume T.progression h

theorem squareProgression_nondegenerate
    {d : ℕ} {A : Finset (LatticePoint d)}
    (T : Reduction.SelectedCFP A) (h : T.dimension = d) :
    (selectedSquareProgression T h).Nondegenerate :=
  castGAPRank_nondegenerate T.progression h
    T.witness.progression_nondegenerate

theorem squareProgression_dilate_proper
    {d : ℕ} {A : Finset (LatticePoint d)}
    (T : Reduction.SelectedCFP A) (h : T.dimension = d) :
    ((selectedSquareProgression T h).dilate T.dilation).Proper :=
  castGAPRank_dilate_proper T.progression h T.witness.dilate_proper

theorem gapStepLattice_squareProgression
    {d : ℕ} {A : Finset (LatticePoint d)}
    (T : Reduction.SelectedCFP A) (h : T.dimension = d) :
    gapStepLattice T.progression =
      stepLattice (selectedSquareProgression T h) :=
  gapStepLattice_castGAPRank T.progression h

/-- The exact quantitative Lemma-11-to-full-rank bridge for one selected
side.  The only numerical input is the source hierarchy inequality after the
control-box cardinality has been made explicit. -/
theorem selectedSquareProgression_det_ne_zero
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (S : Reduction.SelectedCFP A)
    {X : Finset (LatticePoint S.dimension)}
    (T : Reduction.SelectedCFP X)
    (hdim : T.dimension = S.dimension)
    (hdimpos : 0 < S.dimension)
    (m : ℕ) (gamma : ℝ) (t : LatticePoint S.dimension)
    (hcontain : T.progression.carrier ⊆ PZ.translate t
      (controlIntegerBox S.progression m).carrier)
    (hvolume : gamma * (S.progression.volume : ℝ) ≤
      (T.progression.volume : ℝ))
    (hgamma : 0 < gamma)
    (hhierarchy :
      ((2 ^ S.dimension * (2 * S.dimension + 1) ^
          (S.dimension - 1) *
          (((m + 1) ^ S.dimension) * 2 ^ S.dimension) : ℕ) : ℝ) <
        (T.dilation : ℝ) * gamma) :
    (stepMatrix (selectedSquareProgression T hdim)).det ≠ 0 := by
  apply det_ne_zero_of_controlled_box_gamma_hierarchy_pos hdimpos
    (selectedSquareProgression T hdim) S.progression
    (controlIntegerBox S.progression m) t gamma
  · rw [← pzTranslate_eq_cfpTranslate]
    simpa only [squareProgression_carrier T hdim] using hcontain
  · exact squareProgression_nondegenerate T hdim
  · exact squareProgression_dilate_proper T hdim
  · exact T.witness.k_pos
  · exact controlIntegerBox_card_le S.progression m
  · simpa only [squareProgression_volume T hdim] using hvolume
  · exact hgamma
  · simpa only [Nat.mul_assoc] using hhierarchy

/-- Two quantitative full-rank conclusions give the concrete common covering
radius for the step lattices used by the canonical side targets. -/
theorem selectedSideProgressions_commonCoveringRadius
    {ambient : ℕ} {A : Finset (LatticePoint ambient)}
    (S : Reduction.SelectedCFP A)
    {X₁ X₂ : Finset (LatticePoint S.dimension)}
    (T₁ : Reduction.SelectedCFP X₁) (T₂ : Reduction.SelectedCFP X₂)
    (hdim₁ : T₁.dimension = S.dimension)
    (hdim₂ : T₂.dimension = S.dimension)
    (hdet₁ : (stepMatrix (selectedSquareProgression T₁ hdim₁)).det ≠ 0)
    (hdet₂ : (stepMatrix (selectedSquareProgression T₂ hdim₂)).det ≠ 0) :
    HasCommonCoveringRadius
      (gapStepLattice T₁.progression : Set (LatticePoint S.dimension))
      (gapStepLattice T₂.progression : Set (LatticePoint S.dimension))
      ((stepMatrix (selectedSquareProgression T₁ hdim₁)).det.natAbs ^ S.dimension *
        (stepMatrix (selectedSquareProgression T₂ hdim₂)).det.natAbs ^
          S.dimension) := by
  rw [gapStepLattice_squareProgression T₁ hdim₁,
    gapStepLattice_squareProgression T₂ hdim₂]
  exact stepLattices_commonCoveringRadius
    (selectedSquareProgression T₁ hdim₁)
    (selectedSquareProgression T₂ hdim₂) hdet₁ hdet₂

end

end Erdos186.PZ.Intersection
