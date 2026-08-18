/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.CanonicalRoundingCore
import ErdosProblems.Erdos186.PZ.Intersection.CenteredZonotope

/-!
# Center error after reserving and discarding CFP generators

The common convex-combination center is formed with all generators of a
side.  Equation (15) rounds only with the canonical core
`W.core \ W.reserved`, and its structured part is based at the covered CFP
translation point.  This file proves that the resulting coordinatewise
center error is controlled by exactly the discarded and reserved budgets.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- At most `loss + s` input elements lie outside the canonical rounding
core. -/
theorem card_sdiff_canonicalRoundingCore_le
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    (A \ canonicalRoundingCore W).card ≤ loss + s := by
  have hsubset : A \ canonicalRoundingCore W ⊆
      (A \ W.core) ∪ W.reserved := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hcore : x ∈ W.core
    · apply Finset.mem_union_right
      by_contra hreserved
      exact hx.2 (Finset.mem_sdiff.mpr ⟨hcore, hreserved⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx.1, hcore⟩)
  have hdiscarded : (A \ W.core).card ≤ loss := by
    exact W.toCFPWitness.card_sdiff_core_le
  calc
    (A \ canonicalRoundingCore W).card ≤
        ((A \ W.core) ∪ W.reserved).card := Finset.card_le_card hsubset
    _ ≤ (A \ W.core).card + W.reserved.card :=
      Finset.card_union_le _ _
    _ ≤ loss + s := Nat.add_le_add hdiscarded W.reserved_small

/-- The CFP translation point is itself a subset sum of the reserved set,
because zero belongs to the symmetric covered dilate. -/
theorem translatePoint_mem_subsetSums_reserved
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) :
    W.translatePoint ∈ GAP.subsetSums W.reserved := by
  apply W.covered
  apply CFP.mem_translate_iff.mpr
  refine ⟨0, ?_, by simp⟩
  exact (W.progression_symmetric.dilate k).zero_mem_carrier

/-- A subset sum of at most `s` coordinate-bounded reserved generators has
coordinate size at most `s * width`. -/
theorem abs_translatePoint_le_reserveBound_mul
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    {width : ℝ} (hwidth : 0 ≤ width)
    (hbound : ∀ x ∈ W.reserved, ∀ i, |(x i : ℝ)| ≤ width)
    (i : Fin d) :
    |(W.translatePoint i : ℝ)| ≤ (s : ℝ) * width := by
  obtain ⟨T, hT, hsum⟩ :=
    GAP.mem_subsetSums_iff.mp (translatePoint_mem_subsetSums_reserved W)
  have hcard : T.card ≤ s :=
    (Finset.card_le_card hT).trans W.reserved_small
  have hsumBound : |∑ x ∈ T, (x i : ℝ)| ≤ (T.card : ℝ) * width := by
    calc
      |∑ x ∈ T, (x i : ℝ)| ≤ ∑ x ∈ T, |(x i : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ T, width := by
        apply Finset.sum_le_sum
        intro x hx
        exact hbound x (hT hx) i
      _ = (T.card : ℝ) * width := by simp
  have hcoord : (W.translatePoint i : ℝ) = ∑ x ∈ T, (x i : ℝ) := by
    have hi : W.translatePoint i = ∑ x ∈ T, x i := by
      simpa using congrFun hsum.symm i
    exact_mod_cast hi
  rw [hcoord]
  exact hsumBound.trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hwidth)

/-- Removing a subset changes a weighted center by at most one half times
the number of removed generators times the coordinate width. -/
theorem abs_zonotopeCenter_sub_le_card_sdiff_mul
    {d : ℕ} {A B : Finset (LatticePoint d)}
    (hBA : B ⊆ A) (q : LatticePoint d → ℝ)
    {width : ℝ} (hwidth : 0 ≤ width)
    (hq : ∀ x ∈ A, 0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hbound : ∀ x ∈ A, ∀ i, |(x i : ℝ)| ≤ width)
    (i : Fin d) :
    |zonotopeCenter A q i - zonotopeCenter B q i| ≤
      ((A \ B).card : ℝ) * ((1 : ℝ) / 2 * width) := by
  change |∑ x ∈ A, q x * (x i : ℝ) -
      ∑ x ∈ B, q x * (x i : ℝ)| ≤ _
  rw [← Finset.sum_sdiff_eq_sub hBA]
  calc
    |∑ x ∈ A \ B, q x * (x i : ℝ)| ≤
        ∑ x ∈ A \ B, |q x * (x i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ A \ B, ((1 : ℝ) / 2 * width) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxA := (Finset.mem_sdiff.mp hx).1
      rw [abs_mul, abs_of_nonneg (hq x hxA).1]
      exact mul_le_mul (hq x hxA).2 (hbound x hxA i)
        (abs_nonneg _) (by positivity)
    _ = ((A \ B).card : ℝ) * ((1 : ℝ) / 2 * width) := by simp

/-- Concrete center-error estimate for the canonical target based at the
covered CFP translate. -/
theorem canonicalRoundingCore_center_error
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    (q : LatticePoint d → ℝ) {width : ℝ} (hwidth : 0 ≤ width)
    (hq : ∀ x ∈ A, 0 ≤ q x ∧ q x ≤ (1 : ℝ) / 2)
    (hbound : ∀ x ∈ A, ∀ i, |(x i : ℝ)| ≤ width)
    (i : Fin d) :
    |zonotopeCenter A q i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W) q) i| ≤
      ((((loss + s : ℕ) : ℝ) * ((1 : ℝ) / 2 * width)) +
        (s : ℝ) * width) := by
  have hcore := abs_zonotopeCenter_sub_le_card_sdiff_mul
    (canonicalRoundingCore_subset_input W) q hwidth hq hbound i
  have hcard : ((A \ canonicalRoundingCore W).card : ℝ) ≤
      (loss + s : ℕ) := by
    exact_mod_cast card_sdiff_canonicalRoundingCore_le W
  have hcore' : |zonotopeCenter A q i -
      zonotopeCenter (canonicalRoundingCore W) q i| ≤
      ((loss + s : ℕ) : ℝ) * ((1 : ℝ) / 2 * width) :=
    hcore.trans (mul_le_mul_of_nonneg_right hcard (by positivity))
  have hreserved : ∀ x ∈ W.reserved, ∀ j, |(x j : ℝ)| ≤ width := by
    intro x hx j
    exact hbound x (W.reserved_subset hx) j
  have htranslate :=
    abs_translatePoint_le_reserveBound_mul W hwidth hreserved i
  change |zonotopeCenter A q i -
      ((W.translatePoint i : ℝ) +
        zonotopeCenter (canonicalRoundingCore W) q i)| ≤ _
  calc
    |zonotopeCenter A q i -
        ((W.translatePoint i : ℝ) +
          zonotopeCenter (canonicalRoundingCore W) q i)| =
        |(zonotopeCenter A q i -
          zonotopeCenter (canonicalRoundingCore W) q i) -
            (W.translatePoint i : ℝ)| := by
          congr 1
          ring
    _ ≤ |zonotopeCenter A q i -
          zonotopeCenter (canonicalRoundingCore W) q i| +
        |(W.translatePoint i : ℝ)| := abs_sub _ _
    _ ≤ (((loss + s : ℕ) : ℝ) * ((1 : ℝ) / 2 * width)) +
        (s : ℝ) * width := add_le_add hcore' htranslate

end

end Erdos186.PZ.Intersection
