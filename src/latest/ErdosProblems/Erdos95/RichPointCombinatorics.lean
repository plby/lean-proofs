/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.SetFamilyBounds
import ErdosProblems.Erdos95.SurfaceCollections

/-!
# Combinatorics of rich Elekes--Sharir line points

This file contains the elementary large-richness estimate used in Guth's
low-degree induction.  Its only geometric input is that two distinct points
of parameter space lie on at most one indexed Elekes--Sharir line.
-/

namespace Erdos95.RichPointCombinatorics

open Erdos95.ES Erdos95.LineFamilies Erdos95.SetFamilyBounds

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- Two distinct points of parameter space share at most one line of an
Elekes--Sharir subfamily. -/
theorem card_common_linesThrough_le_one (L : Finset LineIndex)
    {x y : Space3} (hxy : x ≠ y) :
    ((linesThrough L x).filter fun l ↦ l ∈ linesThrough L y).card ≤ 1 := by
  classical
  by_contra hcard
  have hone : 1 < ((linesThrough L x).filter
      fun l ↦ l ∈ linesThrough L y).card := by omega
  obtain ⟨l, m, hl, hm, hlm⟩ := Finset.one_lt_card_iff.mp hone
  have hlx : OnLine l.1 l.2 x :=
    (mem_linesThrough_iff.mp (Finset.mem_filter.mp hl).1).2
  have hly : OnLine l.1 l.2 y :=
    (mem_linesThrough_iff.mp (Finset.mem_filter.mp hl).2).2
  have hmx : OnLine m.1 m.2 x :=
    (mem_linesThrough_iff.mp (Finset.mem_filter.mp hm).1).2
  have hmy : OnLine m.1 m.2 y :=
    (mem_linesThrough_iff.mp (Finset.mem_filter.mp hm).2).2
  exact hxy (intersection_unique hlm hlx hmx hly hmy)

/-- Proposition 2.2 of Guth's low-degree paper, in denominator-free form.
When `r² > 4|L|`, the number of `r`-rich points is at most `2|L|/r`. -/
theorem richness_mul_card_le_two_mul_lines
    (L : Finset LineIndex) (r : ℕ) (hlarge : 4 * L.card < r ^ 2) :
    r * (richPoints L r).card ≤ 2 * L.card := by
  classical
  apply large_family_bound L (richPoints L r) (fun x ↦ linesThrough L x) r 1
  · intro x hx
    exact Finset.filter_subset _ _
  · intro x hx
    exact (mem_richPoints_iff.mp hx).2
  · intro x hx y hy hxy
    exact card_common_linesThrough_le_one L hxy
  · simpa using hlarge

/-- Rich points contributed by at least one surface in a finite collection. -/
noncomputable def surfaceRichPoints (L : Finset LineIndex)
    (F : Finset Poly3) (r : ℕ) : Finset Space3 := by
  classical
  exact F.biUnion fun Q ↦ richPoints (surfaceLines L Q) r

theorem mem_surfaceRichPoints_iff {L : Finset LineIndex}
    {F : Finset Poly3} {r : ℕ} {x : Space3} :
    x ∈ surfaceRichPoints L F r ↔
      ∃ Q ∈ F, x ∈ richPoints (surfaceLines L Q) r := by
  classical
  simp [surfaceRichPoints]

theorem card_surfaceRichPoints_le_sum (L : Finset LineIndex)
    (F : Finset Poly3) (r : ℕ) :
    (surfaceRichPoints L F r).card ≤
      ∑ Q ∈ F, (richPoints (surfaceLines L Q) r).card := by
  classical
  unfold surfaceRichPoints
  exact Finset.card_biUnion_le

theorem surfaceRichPoints_mono_collection
    (L : Finset LineIndex) {F G : Finset Poly3} (hFG : F ⊆ G) (r : ℕ) :
    surfaceRichPoints L F r ⊆ surfaceRichPoints L G r := by
  intro x hx
  obtain ⟨Q, hQF, hxQ⟩ := mem_surfaceRichPoints_iff.mp hx
  exact mem_surfaceRichPoints_iff.mpr ⟨Q, hFG hQF, hxQ⟩

/-- The elementary ordered-pair estimate, summed over a surface collection. -/
theorem richness_mul_pred_mul_card_surfaceRichPoints_le
    (L : Finset LineIndex) (F : Finset Poly3) (r : ℕ) :
    r * (r - 1) * (surfaceRichPoints L F r).card ≤
      ∑ Q ∈ F, (surfaceLines L Q).card ^ 2 := by
  classical
  calc
    r * (r - 1) * (surfaceRichPoints L F r).card ≤
        r * (r - 1) *
          ∑ Q ∈ F, (richPoints (surfaceLines L Q) r).card :=
      Nat.mul_le_mul_left _ (card_surfaceRichPoints_le_sum L F r)
    _ = ∑ Q ∈ F,
        r * (r - 1) * (richPoints (surfaceLines L Q) r).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ Q ∈ F, (surfaceLines L Q).card ^ 2 := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact richness_mul_pred_mul_card_le_sq (surfaceLines L Q) r

end Erdos95.RichPointCombinatorics
