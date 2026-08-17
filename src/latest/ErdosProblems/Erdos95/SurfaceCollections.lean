/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.WallIncidences
import ErdosProblems.Erdos95.Hilbert

/-!
# Collections of low-degree irreducible surfaces

Distinct normalized irreducible surfaces of degree at most `D` have only a
bounded number of common Elekes--Sharir lines.  This is the finite overlap
input in Guth's pruning argument.
-/

namespace Erdos95.SurfaceCollections

open Erdos95.Algebraic Erdos95.ES Erdos95.Hilbert
open Erdos95.LineFamilies Erdos95.SurfaceFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

/-- A degree-only upper bound for lines common to two distinct normalized
irreducible surfaces. -/
def commonLineConstant (D : ℕ) : ℕ :=
  D * D * (2 * (D * D) + D + D + 2)

theorem commonLineConstant_mono : Monotone commonLineConstant := by
  intro a b hab
  unfold commonLineConstant
  gcongr

/-- Lines of `L` contained in both surfaces. -/
noncomputable def commonSurfaceLines (L : Finset LineIndex)
    (Q R : Poly3) : Finset LineIndex := by
  classical
  exact (surfaceLines L Q).filter fun l ↦ LineContained R
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2)

theorem mem_commonSurfaceLines_iff {L : Finset LineIndex}
    {Q R : Poly3} {l : LineIndex} :
    l ∈ commonSurfaceLines L Q R ↔
      l ∈ L ∧ LineContained Q
        (linePoint l.1 l.2 0) (lineDirection l.1 l.2) ∧
      LineContained R
        (linePoint l.1 l.2 0) (lineDirection l.1 l.2) := by
  classical
  simp [commonSurfaceLines, mem_surfaceLines_iff]
  tauto

theorem card_commonSurfaceLines_le
    (L : Finset LineIndex) {Q R : Poly3} {D : ℕ}
    (hQirr : Irreducible Q) (hRirr : Irreducible R)
    (hQnorm : normalize Q = Q) (hRnorm : normalize R = R)
    (hQR : Q ≠ R) (hQdeg : Q.totalDegree ≤ D)
    (hRdeg : R.totalDegree ≤ D) :
    (commonSurfaceLines L Q R).card ≤ commonLineConstant D := by
  classical
  let I := {l // l ∈ commonSurfaceLines L Q R}
  let idx : I → LineIndex := fun l ↦ l.1
  have hinj : Function.Injective idx := Subtype.val_injective
  have hI := card_le_of_lines_in_two_surfaces idx hinj
    hQirr.ne_zero hRirr.ne_zero hQirr
    (not_dvd_of_ne_of_normalized_irreducible hQirr hRirr
      hQnorm hRnorm hQR)
    rfl rfl
    (fun i ↦ (mem_commonSurfaceLines_iff.mp i.2).2.1)
    (fun i ↦ (mem_commonSurfaceLines_iff.mp i.2).2.2)
  have hcardI : Fintype.card I = (commonSurfaceLines L Q R).card := by
    simp [I]
  rw [hcardI] at hI
  exact hI.trans <| by
    unfold commonLineConstant
    gcongr

end Erdos95.SurfaceCollections
