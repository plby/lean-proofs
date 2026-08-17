/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.WallFactors

/-!
# Low-degree walls for subfamilies of an Elekes--Sharir family

The non-clustering theorem is stated for the full family `P × P`.  The
incidence induction repeatedly passes to subfamilies, so this file records
the monotone form which is used at every descendant node.
-/

namespace Erdos95.SpecialFamily

open Erdos95.ES Erdos95.LineFamilies Erdos95.NonClustering
open Erdos95.SurfaceFactors

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

theorem surfaceLines_subset_lineIndicesOnSurface
    {P : Finset PlanePoint} {L : Finset LineIndex} (hL : L ⊆ P.product P)
    (Q : Poly3) :
    surfaceLines L Q ⊆ lineIndicesOnSurface P Q := by
  classical
  intro l hl
  have hldata := mem_surfaceLines_iff.mp hl
  exact Finset.mem_filter.mpr ⟨hL hldata.1, hldata.2⟩

/-- Every irreducible surface of degree at most `d` contains only linearly
many lines of any subfamily of the special `P × P` line family. -/
theorem card_surfaceLines_le_degree
    {P : Finset PlanePoint} {L : Finset LineIndex} (hL : L ⊆ P.product P)
    {Q : Poly3} (hQirr : Irreducible Q) {d : ℕ}
    (hdeg : Q.totalDegree ≤ d) :
    (surfaceLines L Q).card ≤
      surfaceLineConstant d * (P.card + 1) := by
  exact (Finset.card_le_card
    (surfaceLines_subset_lineIndicesOnSurface hL Q)).trans
      (card_lineIndicesOnSurface_le_degree P hQirr hdeg)

/-- A subfamily has at most `|P|` members through one point. -/
theorem card_linesThrough_le_points
    {P : Finset PlanePoint} {L : Finset LineIndex} (hL : L ⊆ P.product P)
    (x : Space3) :
    (linesThrough L x).card ≤ P.card := by
  classical
  let S := linesThrough L x
  have hinj : Set.InjOn Prod.fst (S : Set LineIndex) := by
    intro a ha b hb hab
    have ha' := mem_linesThrough_iff.mp ha
    have hb' := mem_linesThrough_iff.mp hb
    have hint : Intersects a.1 a.2 b.1 b.2 :=
      ⟨x, ha'.2, hb'.2⟩
    have hdist : dist a.1 b.1 = dist a.2 b.2 :=
      sqDist_eq_iff_dist_eq.mp (sqDist_eq_of_intersects hint)
    have hsecond : a.2 = b.2 := by
      apply dist_eq_zero.mp
      simpa [hab] using hdist.symm
    exact Prod.ext hab hsecond
  have hcard : (S.image Prod.fst).card = S.card :=
    Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp
      (hL (mem_linesThrough_iff.mp hl).1)).1
  calc
    S.card = (S.image Prod.fst).card := hcard.symm
    _ ≤ P.card := Finset.card_le_card hsub

end Erdos95.SpecialFamily
