/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.RichPointCombinatorics

/-!
# Pruning collections of algebraic surfaces

Distinct normalized irreducible surfaces of bounded degree share only a
bounded number of Elekes--Sharir lines.  The finite bounded-overlap lemma
therefore controls how many such surfaces can each contain many lines.
-/

namespace Erdos95.SurfacePruning

open Erdos95.ES Erdos95.LineFamilies Erdos95.SurfaceCollections
open Erdos95.SetFamilyBounds Erdos95.SurfaceFactors
open Erdos95.RichPointCombinatorics

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

noncomputable local instance : StrongNormalizationMonoid Poly3 :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

theorem filter_surfaceLines_eq_commonSurfaceLines
    (L : Finset LineIndex) (Q R : Poly3) :
    (surfaceLines L Q).filter (fun l ↦ l ∈ surfaceLines L R) =
      commonSurfaceLines L Q R := by
  classical
  ext l
  simp only [Finset.mem_filter, mem_surfaceLines_iff,
    mem_commonSurfaceLines_iff]
  tauto

/-- Guth's many-large-surfaces lemma, with a slightly stronger quadratic
hypothesis convenient for denominator-free natural-number arithmetic. -/
theorem large_surface_collection_bound
    (L : Finset LineIndex) (F : Finset Poly3) (A D : ℕ)
    (hirr : ∀ Q ∈ F, Irreducible Q)
    (hnorm : ∀ Q ∈ F, normalize Q = Q)
    (hdegree : ∀ Q ∈ F, Q.totalDegree ≤ D)
    (hlarge : ∀ Q ∈ F, A ≤ (surfaceLines L Q).card)
    (hquadratic : 4 * commonLineConstant D * L.card < A ^ 2) :
    A * F.card ≤ 2 * L.card := by
  classical
  apply large_family_bound L F (surfaceLines L) A (commonLineConstant D)
  · intro Q hQ
    exact surfaceLines_subset L Q
  · exact hlarge
  · intro Q hQ R hR hQR
    rw [filter_surfaceLines_eq_commonSurfaceLines]
    exact card_commonSurfaceLines_le L
      (hirr Q hQ) (hirr R hR) (hnorm Q hQ) (hnorm R hR)
      hQR (hdegree Q hQ) (hdegree R hR)
  · exact hquadratic

/-- Surfaces in a collection whose line count lies in a half-open dyadic
window. -/
noncomputable def lineCountWindow (L : Finset LineIndex)
    (F : Finset Poly3) (A B : ℕ) : Finset Poly3 := by
  classical
  exact F.filter fun Q ↦
    A ≤ (surfaceLines L Q).card ∧ (surfaceLines L Q).card < B

theorem mem_lineCountWindow_iff {L : Finset LineIndex}
    {F : Finset Poly3} {A B : ℕ} {Q : Poly3} :
    Q ∈ lineCountWindow L F A B ↔
      Q ∈ F ∧ A ≤ (surfaceLines L Q).card ∧
        (surfaceLines L Q).card < B := by
  classical
  simp [lineCountWindow]

/-! ## Threshold pruning -/

/-- The members of `F` containing at least `A` lines of `L`. -/
noncomputable def largeSurfaces (L : Finset LineIndex)
    (F : Finset Poly3) (A : ℕ) : Finset Poly3 := by
  classical
  exact F.filter fun Q ↦ A ≤ (surfaceLines L Q).card

/-- The members discarded at threshold `A`. -/
noncomputable def smallSurfaces (L : Finset LineIndex)
    (F : Finset Poly3) (A : ℕ) : Finset Poly3 := by
  classical
  exact F.filter fun Q ↦ (surfaceLines L Q).card < A

theorem mem_largeSurfaces_iff {L : Finset LineIndex}
    {F : Finset Poly3} {A : ℕ} {Q : Poly3} :
    Q ∈ largeSurfaces L F A ↔
      Q ∈ F ∧ A ≤ (surfaceLines L Q).card := by
  classical
  simp [largeSurfaces]

theorem mem_smallSurfaces_iff {L : Finset LineIndex}
    {F : Finset Poly3} {A : ℕ} {Q : Poly3} :
    Q ∈ smallSurfaces L F A ↔
      Q ∈ F ∧ (surfaceLines L Q).card < A := by
  classical
  simp [smallSurfaces]

theorem surfaces_subset_large_union_small
    (L : Finset LineIndex) (F : Finset Poly3) (A : ℕ) :
    F ⊆ largeSurfaces L F A ∪ smallSurfaces L F A := by
  intro Q hQ
  by_cases hlarge : A ≤ (surfaceLines L Q).card
  · exact Finset.mem_union_left _
      (mem_largeSurfaces_iff.mpr ⟨hQ, hlarge⟩)
  · exact Finset.mem_union_right _
      (mem_smallSurfaces_iff.mpr ⟨hQ, Nat.lt_of_not_ge hlarge⟩)

theorem surfaceRichPoints_subset_pruned_union
    (L : Finset LineIndex) (F : Finset Poly3) (A r : ℕ) :
    surfaceRichPoints L F r ⊆
      surfaceRichPoints L (largeSurfaces L F A) r ∪
        surfaceRichPoints L (smallSurfaces L F A) r := by
  intro x hx
  obtain ⟨Q, hQ, hxQ⟩ := mem_surfaceRichPoints_iff.mp hx
  rcases Finset.mem_union.mp (surfaces_subset_large_union_small L F A hQ) with
      hQlarge | hQsmall
  · exact Finset.mem_union_left _
      (mem_surfaceRichPoints_iff.mpr ⟨Q, hQlarge, hxQ⟩)
  · exact Finset.mem_union_right _
      (mem_surfaceRichPoints_iff.mpr ⟨Q, hQsmall, hxQ⟩)

/-- The sum of squared line counts over the discarded collection is bounded
by its cardinality times the square of the threshold. -/
theorem sum_sq_surfaceLines_small_le
    (L : Finset LineIndex) (F : Finset Poly3) (A : ℕ) :
    ∑ Q ∈ smallSurfaces L F A, (surfaceLines L Q).card ^ 2 ≤
      F.card * A ^ 2 := by
  calc
    ∑ Q ∈ smallSurfaces L F A, (surfaceLines L Q).card ^ 2 ≤
        ∑ _Q ∈ smallSurfaces L F A, A ^ 2 := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact Nat.pow_le_pow_left (Nat.le_of_lt
        (mem_smallSurfaces_iff.mp hQ).2) 2
    _ = (smallSurfaces L F A).card * A ^ 2 := by simp
    _ ≤ F.card * A ^ 2 := by
      exact Nat.mul_le_mul_right (A ^ 2)
        (Finset.card_le_card (show smallSurfaces L F A ⊆ F by
          exact Finset.filter_subset _ _))

end Erdos95.SurfacePruning
