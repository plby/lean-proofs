/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# The complete-bipartite Euclidean geometry lemma

This file proves the geometric lemma used in Swanepoel's analysis of diameter
graphs.  If every cross-distance between two nonempty point sets is constant,
then their affine direction spaces are orthogonal.  For unit cross-distance,
both sets lie on spheres with one common center and radii whose squares sum to
one.

The result is stated first for arbitrary nonempty sets.  The final theorem is
the finite, cardinality-at-least-three form used for Erdős Problem 223.  The
cardinality hypotheses are not needed for this geometric conclusion, but are
included in that interface because they are the hypotheses in Swanepoel's
lemma.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos223

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Constant cross-distance makes the affine direction spaces of the two
point sets orthogonal. -/
theorem affineSpan_direction_isOrtho_of_cross_dist_eq
    {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty) (radius : ℝ)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b = radius) :
    (affineSpan ℝ A).direction ⟂ (affineSpan ℝ B).direction := by
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  rw [direction_affineSpan, direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ ha₀,
    vectorSpan_eq_span_vsub_set_right ℝ hb₀, Submodule.isOrtho_span]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  apply EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
  · simpa [dist_comm] using
      (hcross a₀ ha₀ b₀ hb₀).trans (hcross a₀ ha₀ b hb).symm
  · simpa [dist_comm] using
      (hcross a ha b₀ hb₀).trans (hcross a ha b hb).symm

/-- A unit complete bipartite distance pattern has orthogonal affine
directions.  Projecting `B` to the affine span of `A` gives a point about
which both sets are cospherical, with squared radii summing to one.  The
chosen point need not lie in the affine span of `B`; in particular this does
not assert that the two affine spans intersect. -/
theorem completeBipartiteGeometry
    [FiniteDimensional ℝ E] {A B : Set E} (hA : A.Nonempty) (hB : B.Nonempty)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b = 1) :
    (affineSpan ℝ A).direction ⟂ (affineSpan ℝ B).direction ∧
      ∃ c : E, ∃ r s : ℝ,
        c ∈ affineSpan ℝ A ∧
          0 ≤ r ∧ 0 ≤ s ∧
          (∀ a ∈ A, dist a c = r) ∧
          (∀ b ∈ B, dist b c = s) ∧
          r ^ 2 + s ^ 2 = 1 := by
  classical
  obtain ⟨a₀, ha₀⟩ := hA
  obtain ⟨b₀, hb₀⟩ := hB
  let S : AffineSubspace ℝ E := affineSpan ℝ A
  have hS : Nonempty S := ⟨⟨a₀, mem_affineSpan ℝ ha₀⟩⟩
  let c : E := EuclideanGeometry.orthogonalProjection S b₀
  have hc : c ∈ S := EuclideanGeometry.orthogonalProjection_mem _
  have hcenter : ∃ r : ℝ, ∀ a ∈ A, dist a c = r := by
    have hbefore : ∃ r : ℝ, ∀ a ∈ A, dist a b₀ = r :=
      ⟨1, fun a ha ↦ hcross a ha b₀ hb₀⟩
    simpa [c] using
      (EuclideanGeometry.exists_dist_eq_iff_exists_dist_orthogonalProjection_eq
        (s := S) (subset_affineSpan ℝ A) b₀).mp hbefore
  obtain ⟨r, hr⟩ := hcenter
  let s : ℝ := dist b₀ c
  have horth : S.direction ⟂ (affineSpan ℝ B).direction := by
    simpa [S] using
      affineSpan_direction_isOrtho_of_cross_dist_eq ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩ 1 hcross
  have hprojection : ∀ b ∈ B,
      (EuclideanGeometry.orthogonalProjection S b : E) = c := by
    intro b hb
    have hbb₀ : b -ᵥ b₀ ∈ (affineSpan ℝ B).direction :=
      AffineSubspace.vsub_mem_direction
        (mem_affineSpan ℝ hb) (mem_affineSpan ℝ hb₀)
    have hbb₀orth : b -ᵥ b₀ ∈ S.directionᗮ := horth.ge hbb₀
    have hb₀corth : b₀ -ᵥ c ∈ S.directionᗮ := by
      simpa [c] using
        EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal S b₀
    have hbcorth : b -ᵥ c ∈ S.directionᗮ := by
      rw [← vsub_add_vsub_cancel b b₀ c]
      exact S.directionᗮ.add_mem hbb₀orth hb₀corth
    have hproj := EuclideanGeometry.orthogonalProjection_vadd_eq_self hc hbcorth
    have hproj' : EuclideanGeometry.orthogonalProjection S b = ⟨c, hc⟩ := by
      simpa only [vsub_vadd] using hproj
    exact congrArg (fun x : S ↦ (x : E)) hproj'
  have hpythag : ∀ b ∈ B,
      dist a₀ b * dist a₀ b = r * r + dist b c * dist b c := by
    intro b hb
    have h :=
      EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
        (s := S) b (mem_affineSpan ℝ ha₀)
    rw [hprojection b hb] at h
    simpa [hr a₀ ha₀] using h
  have hsphereB : ∀ b ∈ B, dist b c = s := by
    intro b hb
    have hbEq := hpythag b hb
    have hb₀Eq := hpythag b₀ hb₀
    rw [hcross a₀ ha₀ b hb] at hbEq
    rw [hcross a₀ ha₀ b₀ hb₀] at hb₀Eq
    have hdb : 0 ≤ dist b c := dist_nonneg
    have hds : 0 ≤ s := by exact dist_nonneg
    dsimp [s] at hds ⊢
    nlinarith
  have hr_nonneg : 0 ≤ r := by
    rw [← hr a₀ ha₀]
    exact dist_nonneg
  have hs_nonneg : 0 ≤ s := by
    exact dist_nonneg
  have hrsum : r ^ 2 + s ^ 2 = 1 := by
    have h := hpythag b₀ hb₀
    rw [hcross a₀ ha₀ b₀ hb₀] at h
    dsimp [s]
    nlinarith
  refine ⟨horth, c, r, s, ?_, hr_nonneg, hs_nonneg, hr, hsphereB, hrsum⟩
  simpa [S] using hc

/-- Swanepoel's complete-bipartite geometry lemma in its finite form.  The
lower bounds of three on the two cardinalities are the hypotheses needed by
the later carrier analysis. -/
theorem completeBipartiteGeometry_finset
    [FiniteDimensional ℝ E] (A B : Finset E) (hAcard : 3 ≤ A.card)
    (hBcard : 3 ≤ B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b = 1) :
    (affineSpan ℝ (↑A : Set E)).direction ⟂
        (affineSpan ℝ (↑B : Set E)).direction ∧
      ∃ c : E, ∃ r s : ℝ,
        c ∈ affineSpan ℝ (↑A : Set E) ∧
          0 ≤ r ∧ 0 ≤ s ∧
          (∀ a ∈ A, dist a c = r) ∧
          (∀ b ∈ B, dist b c = s) ∧
          r ^ 2 + s ^ 2 = 1 := by
  have hA : (↑A : Set E).Nonempty := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 3) hAcard)
    exact ⟨a, ha⟩
  have hB : (↑B : Set E).Nonempty := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega : 0 < 3) hBcard)
    exact ⟨b, hb⟩
  exact completeBipartiteGeometry hA hB hcross

/-- The radii in the finite form are in fact positive.  This is the version
that treats the carriers as nondegenerate spheres. -/
theorem completeBipartiteGeometry_finset_pos
    [FiniteDimensional ℝ E] (A B : Finset E) (hAcard : 3 ≤ A.card)
    (hBcard : 3 ≤ B.card)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, dist a b = 1) :
    (affineSpan ℝ (↑A : Set E)).direction ⟂
        (affineSpan ℝ (↑B : Set E)).direction ∧
      ∃ c : E, ∃ r s : ℝ,
        c ∈ affineSpan ℝ (↑A : Set E) ∧
          0 < r ∧ 0 < s ∧
          (∀ a ∈ A, dist a c = r) ∧
          (∀ b ∈ B, dist b c = s) ∧
          r ^ 2 + s ^ 2 = 1 := by
  obtain ⟨horth, c, r, s, hc, hr0, hs0, hAr, hBs, hrs⟩ :=
    completeBipartiteGeometry_finset A B hAcard hBcard hcross
  have hrpos : 0 < r := by
    obtain ⟨a, ha, a', ha', haa'⟩ :=
      Finset.one_lt_card.mp (lt_of_lt_of_le (by omega : 1 < 3) hAcard)
    refine lt_of_le_of_ne hr0 ?_
    intro hrzero
    have hac : a = c := dist_eq_zero.mp ((hAr a ha).trans hrzero.symm)
    have ha'c : a' = c := dist_eq_zero.mp ((hAr a' ha').trans hrzero.symm)
    exact haa' (hac.trans ha'c.symm)
  have hspos : 0 < s := by
    obtain ⟨b, hb, b', hb', hbb'⟩ :=
      Finset.one_lt_card.mp (lt_of_lt_of_le (by omega : 1 < 3) hBcard)
    refine lt_of_le_of_ne hs0 ?_
    intro hszero
    have hbc : b = c := dist_eq_zero.mp ((hBs b hb).trans hszero.symm)
    have hb'c : b' = c := dist_eq_zero.mp ((hBs b' hb').trans hszero.symm)
    exact hbb' (hbc.trans hb'c.symm)
  exact ⟨horth, c, r, s, hc, hrpos, hspos, hAr, hBs, hrs⟩

end

end Erdos223
