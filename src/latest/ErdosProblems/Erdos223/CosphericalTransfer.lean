/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Geometry.Euclidean.Circumcenter

/-!
# Transferring a cosphere from a full-rank anchor

A cospherical set contained in the affine span of an affinely independent
anchor inherits every sphere equation already satisfied by that anchor, even
when the original cosphere center lies outside the affine span.  Orthogonal
projection to the anchor span removes the irrelevant normal displacement.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos223

noncomputable section

/-- A cospherical set contained in the affine span of a simplex inherits a
prescribed common distance from the simplex vertices. -/
theorem dist_eq_of_cospherical_of_affineSpan_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {n : ℕ} {F : Set E}
    (a : Fin (n + 1) → E) (ha : AffineIndependent ℝ a)
    (haF : ∀ i, a i ∈ F)
    (hFspan : F ⊆ affineSpan ℝ (Set.range a))
    (hcos : EuclideanGeometry.Cospherical F)
    (c : E) (r : ℝ)
    (hc : c ∈ affineSpan ℝ (Set.range a))
    (har : ∀ i, dist (a i) c = r) :
    ∀ x ∈ F, dist x c = r := by
  let S : Affine.Simplex ℝ E n := ⟨a, ha⟩
  obtain ⟨d, s, hds⟩ := hcos
  have hcCirc : c = S.circumcenter := by
    apply S.eq_circumcenter_of_dist_eq
    · simpa [S] using hc
    · intro i
      simpa [S] using har i
  have hproj : ↑(S.orthogonalProjectionSpan d) = c := by
    rw [hcCirc]
    apply S.orthogonalProjection_eq_circumcenter_of_dist_eq
    intro i
    simpa [S] using hds (a i) (haF i)
  intro x hx
  have hxpyth := S.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    d (by simpa [S] using hFspan hx)
  have ha0span : a 0 ∈ affineSpan ℝ (Set.range a) :=
    mem_affineSpan ℝ ⟨0, rfl⟩
  have h0pyth := S.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    d (by simpa [S] using ha0span)
  rw [hproj, hds x hx] at hxpyth
  rw [hproj, hds (a 0) (haF 0), har 0] at h0pyth
  have hr0 : 0 ≤ r := by
    rw [← har 0]
    positivity
  nlinarith [dist_nonneg (x := x) (y := c)]

end

end Erdos223
