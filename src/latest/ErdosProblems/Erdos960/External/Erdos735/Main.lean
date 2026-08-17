/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
import ErdosProblems.Erdos960.External.Erdos735.SylvesterGallai
import ErdosProblems.Erdos960.External.Erdos735.ProjectiveDuality

/-!
# Erdős Problem 735: magic point configurations

This file formalizes the classification theorem of Ackerman, Buchin, Knauer,
Pinchasi, and Rote.  The accompanying mathematical proof and Leanization map
are in `tex/735.tex`.

*References:*
- [Erdős Problem 735](https://www.erdosproblems.com/735)
- E. Ackerman, K. Buchin, C. Knauer, R. Pinchasi, G. Rote,
  *There Are Not Too Many Magic Configurations*, Discrete Comput. Geom. 39
  (2008), 3--16.
-/

namespace Erdos735

open scoped BigOperators

noncomputable section

/-- The concrete real affine plane used in Problem 735. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The affine orientation determinant of three planar points. -/
def orientationDet (p q r : Point) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- Three concrete planar points are collinear when their orientation determinant vanishes. -/
def Collinear3 (p q r : Point) : Prop := orientationDet p q r = 0

/-- The points of `P` on the affine line spanned by the distinct points `p,q`. -/
noncomputable def lineFiber (P : Finset Point) (p q : Point) : Finset Point := by
  classical
  exact P.filter fun r ↦ Collinear3 p q r

/-- Positive point weights with one common sum on every line spanned by `P`. -/
def IsMagic (P : Finset Point) : Prop :=
  ∃ (w : Point → ℝ) (c : ℝ),
    (∀ p ∈ P, 0 < w p) ∧ 0 < c ∧
      ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c

/-- Every spanned line contains all of `P`. -/
def IsCollinearConfig (P : Finset Point) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → lineFiber P p q = P

/-- Every spanned line contains exactly its two spanning points. -/
def InGeneralPosition (P : Finset Point) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → lineFiber P p q = {p, q}

/-- Exactly one point is off a line containing all remaining points.

The two fiber clauses are the intrinsic incidence form of a noncollinear
near-pencil.  The cardinality condition makes the main line genuine. -/
def IsNearPencil (P : Finset Point) : Prop :=
  ∃ z ∈ P,
    2 ≤ (P.erase z).card ∧
      (∀ p ∈ P.erase z, ∀ q ∈ P.erase z, p ≠ q →
        lineFiber P p q = P.erase z) ∧
      ∀ q ∈ P.erase z, lineFiber P z q = {z, q}

/-- Labels for the seven points of the failed Fano configuration.

Labels `0,1,2` are the three diagonal points and labels `3,4,5,6` are the
four vertices of the complete quadrangle. -/
abbrev FailedFanoLabel := Fin 7

/-- The nine lines spanned by the canonical failed Fano configuration. -/
def failedFanoBlocks : Finset (Finset FailedFanoLabel) :=
  { {0, 3, 4}, {0, 5, 6},
    {1, 3, 5}, {1, 4, 6},
    {2, 3, 6}, {2, 4, 5},
    {0, 1}, {0, 2}, {1, 2} }

/-- The canonical line fiber through two failed-Fano labels. -/
def failedFanoLine (i j : FailedFanoLabel) : Finset FailedFanoLabel :=
  Finset.univ.filter fun k ↦
    ∃ B ∈ failedFanoBlocks, i ∈ B ∧ j ∈ B ∧ k ∈ B

/-- Integer weights scaled by four: diagonal points have weight two and base points one. -/
def failedFanoWeight4 (i : FailedFanoLabel) : ℕ :=
  if i.1 < 3 then 2 else 1

/-- Every canonical failed-Fano line has scaled weight four. -/
lemma failedFanoLine_weight4 (i j : FailedFanoLabel) (hij : i ≠ j) :
    ∑ k ∈ failedFanoLine i j, failedFanoWeight4 k = 4 := by
  decide +revert

/-- An intrinsic failed Fano configuration: an injectively labelled copy of the
canonical seven-point incidence table, with exact fibers for every spanned line. -/
def IsFailedFano (P : Finset Point) : Prop :=
  ∃ e : FailedFanoLabel ↪ Point,
    P = Finset.univ.map e ∧
      ∀ i j : FailedFanoLabel, i ≠ j →
        lineFiber P (e i) (e j) = (failedFanoLine i j).map e

/-! ## Affine geometry and the near-pencil bridge -/

lemma orientationDet_cycle (p q r : Point) :
    orientationDet q r p = orientationDet p q r := by
  simp [orientationDet]
  ring

lemma collinear3_cycle {p q r : Point} : Collinear3 p q r ↔ Collinear3 q r p := by
  simp only [Collinear3, orientationDet_cycle]

/-- Determinant collinearity agrees with membership in the affine line through
two distinct points. -/
lemma collinear3_iff_mem_affineSpan_pair {p q r : Point} (hpq : p ≠ q) :
    Collinear3 p q r ↔ r ∈ line[ℝ, p, q] := by
  constructor
  · intro hdet
    have hcoord : q 0 - p 0 ≠ 0 ∨ q 1 - p 1 ≠ 0 := by
      by_contra h
      simp only [not_or, not_not] at h
      apply hpq
      apply PiLp.ext
      intro i
      fin_cases i
      · exact (sub_eq_zero.mp h.1).symm
      · exact (sub_eq_zero.mp h.2).symm
    rcases hcoord with hx | hy
    · have heq : AffineMap.lineMap p q ((r 0 - p 0) / (q 0 - p 0)) = r := by
        ext i
        fin_cases i
        · change (r 0 - p 0) / (q 0 - p 0) * (q 0 - p 0) + p 0 = r 0
          rw [div_mul_cancel₀ _ hx]
          ring
        · change (r 0 - p 0) / (q 0 - p 0) * (q 1 - p 1) + p 1 = r 1
          field_simp [hx]
          dsimp [Collinear3, orientationDet] at hdet
          nlinarith
      exact mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨_, heq⟩
    · have heq : AffineMap.lineMap p q ((r 1 - p 1) / (q 1 - p 1)) = r := by
        ext i
        fin_cases i
        · change (r 1 - p 1) / (q 1 - p 1) * (q 0 - p 0) + p 0 = r 0
          field_simp [hy]
          dsimp [Collinear3, orientationDet] at hdet
          nlinarith
        · change (r 1 - p 1) / (q 1 - p 1) * (q 1 - p 1) + p 1 = r 1
          rw [div_mul_cancel₀ _ hy]
          ring
      exact mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ⟨_, heq⟩
  · intro hr
    rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hr with ⟨t, rfl⟩
    simp [Collinear3, orientationDet, AffineMap.lineMap_apply_module']
    ring

/-- The standard affine-geometric formulation of a near-pencil. -/
def IsAffineNearPencil (P : Finset Point) : Prop :=
  ∃ z ∈ P,
    2 ≤ (P.erase z).card ∧
      Collinear ℝ (P.erase z : Set Point) ∧
      z ∉ affineSpan ℝ (P.erase z : Set Point)

private lemma exists_two_mem_of_two_le_card {s : Finset Point} (hs : 2 ≤ s.card) :
    ∃ p ∈ s, ∃ q ∈ s, p ≠ q := by
  exact Finset.one_lt_card.mp (by omega)

/-- The intrinsic fiber formulation of a near-pencil is equivalent to its
usual affine formulation. -/
lemma isNearPencil_iff_isAffineNearPencil (P : Finset Point) :
    IsNearPencil P ↔ IsAffineNearPencil P := by
  classical
  constructor
  · rintro ⟨z, hzP, hcard, hmain, hcross⟩
    obtain ⟨p, hp, q, hq, hpq⟩ := exists_two_mem_of_two_le_card hcard
    have hmainpq := hmain p hp q hq hpq
    have hcol : Collinear ℝ (P.erase z : Set Point) := by
      rw [collinear_iff_exists_forall_eq_smul_vadd]
      refine ⟨p, q - p, ?_⟩
      intro r hr
      have hrfiber : r ∈ lineFiber P p q := by
        rw [hmainpq]
        exact hr
      have hdet : Collinear3 p q r := (Finset.mem_filter.mp hrfiber).2
      have hrline := (collinear3_iff_mem_affineSpan_pair hpq).mp hdet
      rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hrline with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simpa [AffineMap.lineMap_apply_module'] using ht.symm
    refine ⟨z, hzP, hcard, hcol, ?_⟩
    intro hzspan
    have hspan : line[ℝ, p, q] = affineSpan ℝ (P.erase z : Set Point) :=
      hcol.affineSpan_eq_of_ne hp hq hpq
    have hzline : z ∈ line[ℝ, p, q] := by simpa [hspan] using hzspan
    have hzdet : Collinear3 p q z := (collinear3_iff_mem_affineSpan_pair hpq).mpr hzline
    have hzfiber : z ∈ lineFiber P p q := by
      simp [lineFiber, hzP, hzdet]
    rw [hmainpq] at hzfiber
    exact (Finset.mem_erase.mp hzfiber).1 rfl
  · rintro ⟨z, hzP, hcard, hcol, hzspan⟩
    refine ⟨z, hzP, hcard, ?_, ?_⟩
    · intro p hp q hq hpq
      have hspan : line[ℝ, p, q] = affineSpan ℝ (P.erase z : Set Point) :=
        hcol.affineSpan_eq_of_ne hp hq hpq
      ext r
      constructor
      · intro hrfiber
        have hrparts := Finset.mem_filter.mp hrfiber
        have hrP : r ∈ P := hrparts.1
        have hrline : r ∈ line[ℝ, p, q] :=
          (collinear3_iff_mem_affineSpan_pair hpq).mp hrparts.2
        have hrspan : r ∈ affineSpan ℝ (P.erase z : Set Point) := by
          simpa [hspan] using hrline
        have hrz : r ≠ z := by
          intro hrz
          subst r
          exact hzspan hrspan
        exact Finset.mem_erase.mpr ⟨hrz, hrP⟩
      · intro hr
        have hrP := Finset.mem_of_mem_erase hr
        have hrspan : r ∈ affineSpan ℝ (P.erase z : Set Point) :=
          subset_affineSpan ℝ (P.erase z : Set Point) hr
        have hrline : r ∈ line[ℝ, p, q] := by simpa [hspan] using hrspan
        have hrdet := (collinear3_iff_mem_affineSpan_pair hpq).mpr hrline
        exact Finset.mem_filter.mpr ⟨hrP, hrdet⟩
    · intro q hq
      have hqP := Finset.mem_of_mem_erase hq
      have hzq : z ≠ q := by
        exact fun hzq ↦ (Finset.mem_erase.mp (hzq ▸ hq)).1 rfl
      ext r
      constructor
      · intro hrfiber
        have hrparts := Finset.mem_filter.mp hrfiber
        have hrP : r ∈ P := hrparts.1
        have hdet : Collinear3 z q r := hrparts.2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases hrz : r = z
        · exact Or.inl hrz
        right
        have hr : r ∈ P.erase z := Finset.mem_erase.mpr ⟨hrz, hrP⟩
        by_contra hrq
        have hqr : q ≠ r := Ne.symm hrq
        have hzline : z ∈ line[ℝ, q, r] :=
          (collinear3_iff_mem_affineSpan_pair hqr).mp (collinear3_cycle.mp hdet)
        have hspan : line[ℝ, q, r] = affineSpan ℝ (P.erase z : Set Point) :=
          hcol.affineSpan_eq_of_ne hq hr hqr
        exact hzspan (by simpa [hspan] using hzline)
      · intro hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hzP, by simp [Collinear3, orientationDet]⟩
        · exact Finset.mem_filter.mpr ⟨hqP, by simp [Collinear3, orientationDet]; ring⟩

lemma not_isNearPencil_iff (P : Finset Point) :
    ¬ IsNearPencil P ↔
      ∀ z ∈ P, 2 ≤ (P.erase z).card →
        ¬ (Collinear ℝ (P.erase z : Set Point) ∧
          z ∉ affineSpan ℝ (P.erase z : Set Point)) := by
  rw [isNearPencil_iff_isAffineNearPencil]
  simp only [IsAffineNearPencil, not_exists, not_and]

lemma mem_affineSpan_erase_of_not_isNearPencil
    {P : Finset Point} (hnp : ¬ IsNearPencil P) {z : Point} (hz : z ∈ P)
    (hcard : 2 ≤ (P.erase z).card)
    (hcol : Collinear ℝ (P.erase z : Set Point)) :
    z ∈ affineSpan ℝ (P.erase z : Set Point) := by
  by_contra hzspan
  exact ((not_isNearPencil_iff P).mp hnp z hz hcard) ⟨hcol, hzspan⟩

lemma erase_not_collinear_of_not_nearPencil
    {P : Finset Point} (hP : ¬ Collinear ℝ (P : Set Point))
    (hnp : ¬ IsNearPencil P) {z : Point} (hz : z ∈ P)
    (hcard : 2 ≤ (P.erase z).card) :
    ¬ Collinear ℝ (P.erase z : Set Point) := by
  intro hcol
  have hzspan := mem_affineSpan_erase_of_not_isNearPencil hnp hz hcard hcol
  have hinsert : Collinear ℝ (insert z (P.erase z : Set Point)) := by
    rwa [collinear_insert_iff_of_mem_affineSpan hzspan]
  apply hP
  simpa [Set.ext_iff, hz] using hinsert

/-- Excluding collinearity and a near-pencil makes every point-deleted set
noncollinear. -/
lemma every_erase_not_collinear_of_not_nearPencil
    {P : Finset Point} (hcard : 3 ≤ P.card)
    (hP : ¬ Collinear ℝ (P : Set Point)) (hnp : ¬ IsNearPencil P) :
    ∀ z ∈ P, ¬ Collinear ℝ (P.erase z : Set Point) := by
  intro z hz
  apply erase_not_collinear_of_not_nearPencil hP hnp hz
  rw [Finset.card_erase_of_mem hz]
  omega

/-- A mathematically collinear finite set satisfies the exact line-fiber
predicate used in the classification. -/
lemma isCollinearConfig_of_collinear {P : Finset Point}
    (hcol : Collinear ℝ (P : Set Point)) : IsCollinearConfig P := by
  classical
  intro p hp q hq hpq
  ext r
  constructor
  · exact fun hr ↦ (Finset.mem_filter.mp hr).1
  · intro hr
    have hrline : r ∈ line[ℝ, p, q] :=
      hcol.mem_affineSpan_of_mem_of_ne hp hq hr hpq
    exact Finset.mem_filter.mpr
      ⟨hr, (collinear3_iff_mem_affineSpan_pair hpq).mpr hrline⟩

/-- With at least two points, the exact line-fiber predicate implies ordinary
affine collinearity. -/
lemma collinear_of_isCollinearConfig {P : Finset Point} (hcard : 2 ≤ P.card)
    (hcfg : IsCollinearConfig P) : Collinear ℝ (P : Set Point) := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_two_mem_of_two_le_card hcard
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨p, q - p, ?_⟩
  intro r hr
  have hrfiber : r ∈ lineFiber P p q := by
    rw [hcfg p hp q hq hpq]
    exact hr
  have hrline : r ∈ line[ℝ, p, q] :=
    (collinear3_iff_mem_affineSpan_pair hpq).mp (Finset.mem_filter.mp hrfiber).2
  rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hrline with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  simpa [AffineMap.lineMap_apply_module'] using ht.symm

/-! ## The primal weight reduction -/

/-- A pair of points of `P` spanning an ordinary line. -/
def IsOrdinaryPair (P : Finset Point) (p q : Point) : Prop :=
  p ∈ P ∧ q ∈ P ∧ p ≠ q ∧ lineFiber P p q = {p, q}

/-- Sylvester--Gallai, translated from affine-span lines to the determinant
fibers used in this development. -/
theorem exists_ordinaryPair_of_not_collinear {P : Finset Point}
    (hncol : ¬ Collinear ℝ (P : Set Point)) :
    ∃ p q, IsOrdinaryPair P p q := by
  classical
  obtain ⟨p, hp, q, hq, hord⟩ :=
    SylvesterGallai.sylvester_gallai (P : Set Point) P.finite_toSet hncol
  refine ⟨p, q, hp, hq, hord.2.2.1, ?_⟩
  ext r
  constructor
  · intro hr
    have hrP : r ∈ P := (Finset.mem_filter.mp hr).1
    have hrline : r ∈ line[ℝ, p, q] :=
      (collinear3_iff_mem_affineSpan_pair hord.2.2.1).mp (Finset.mem_filter.mp hr).2
    have := hord.2.2.2 r hrP hrline
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  · intro hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hp, by simp [Collinear3, orientationDet]⟩
    · exact Finset.mem_filter.mpr ⟨hq, by simp [Collinear3, orientationDet]; ring⟩

/-- The points of `P` incident with an ordinary line. -/
noncomputable def ordinaryPoints (P : Finset Point) : Finset Point := by
  classical
  exact P.filter fun p ↦ ∃ q, IsOrdinaryPair P p q

/-- The complementary set of nonordinary points. -/
noncomputable def nonordinaryPoints (P : Finset Point) : Finset Point :=
  P \ ordinaryPoints P

lemma orientationDet_self_left (p q : Point) : orientationDet p q p = 0 := by
  simp [orientationDet]

lemma orientationDet_self_right (p q : Point) : orientationDet p q q = 0 := by
  simp [orientationDet]
  ring

lemma collinear3_swap_left (p q r : Point) : Collinear3 q p r ↔ Collinear3 p q r := by
  have hdet : orientationDet q p r = -orientationDet p q r := by
    simp only [orientationDet]
    ring
  simp only [Collinear3, hdet, neg_eq_zero]

lemma lineFiber_swap (P : Finset Point) (p q : Point) :
    lineFiber P q p = lineFiber P p q := by
  ext r
  simp only [lineFiber, Finset.mem_filter, and_congr_right_iff]
  intro _
  exact collinear3_swap_left p q r

lemma left_mem_lineFiber {P : Finset Point} {p q : Point} (hp : p ∈ P) :
    p ∈ lineFiber P p q := by
  classical
  rw [lineFiber, Finset.mem_filter]
  exact ⟨hp, orientationDet_self_left p q⟩

lemma right_mem_lineFiber {P : Finset Point} {p q : Point} (hq : q ∈ P) :
    q ∈ lineFiber P p q := by
  classical
  rw [lineFiber, Finset.mem_filter]
  exact ⟨hq, orientationDet_self_right p q⟩

lemma pair_subset_lineFiber {P : Finset Point} {p q : Point} (hp : p ∈ P) (hq : q ∈ P) :
    {p, q} ⊆ lineFiber P p q := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact left_mem_lineFiber hp
  · exact right_mem_lineFiber hq

/-- Positivity makes the weight of any pair at most the weight of its line. -/
lemma pair_weight_le_line_sum {P : Finset Point} {w : Point → ℝ}
    (hpos : ∀ x ∈ P, 0 < w x) {p q : Point} (hp : p ∈ P) (hq : q ∈ P)
    (hpq : p ≠ q) :
    w p + w q ≤ ∑ x ∈ lineFiber P p q, w x := by
  classical
  rw [← Finset.sum_pair hpq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (pair_subset_lineFiber hp hq) <| by
    intro x hx _
    exact (hpos x (Finset.mem_filter.mp hx).1).le

/-- If two positive weights already exhaust their line sum, the line is ordinary. -/
lemma lineFiber_eq_pair_of_pair_weight_eq {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    {p q : Point} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (heq : w p + w q = c) :
    lineFiber P p q = {p, q} := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    by_contra hxin
    have hxp : x ≠ p := by
      intro h
      subst x
      exact hxin (by simp)
    have hxq : x ≠ q := by
      intro h
      subst x
      exact hxin (by simp)
    have htriple : {p, q, x} ⊆ lineFiber P p q := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact left_mem_lineFiber hp
      · exact right_mem_lineFiber hq
      · exact hx
    have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
    have hle : w p + w q + w x ≤ ∑ y ∈ lineFiber P p q, w y := by
      have hle' : (∑ y ∈ {p, q, x}, w y) ≤ ∑ y ∈ lineFiber P p q, w y :=
        Finset.sum_le_sum_of_subset_of_nonneg htriple <| by
        intro y hy _
        exact (hpos y (Finset.mem_filter.mp hy).1).le
      have hsumtriple : (∑ y ∈ {p, q, x}, w y) = w p + w q + w x := by
        simp [hpq, hxp.symm, hxq.symm, add_assoc]
      rw [hsumtriple] at hle'
      exact hle'
    have hcx : c < w p + w q + w x := by
      rw [heq]
      linarith [hpos x hxP]
    have := hsum p hp q hq hpq
    linarith
  · exact pair_subset_lineFiber hp hq

/-- An avoiding ordinary line supplies two comparison points for every point. -/
def HasAvoidingOrdinaryLine (P : Finset Point) : Prop :=
  ∀ p ∈ P, ∃ q r, IsOrdinaryPair P q r ∧ p ∉ lineFiber P q r

lemma mem_ordinaryPoints_iff {P : Finset Point} {p : Point} :
    p ∈ ordinaryPoints P ↔ p ∈ P ∧ ∃ q, IsOrdinaryPair P p q := by
  simp [ordinaryPoints]

lemma ordinaryPair_left_mem {P : Finset Point} {p q : Point}
    (h : IsOrdinaryPair P p q) : p ∈ ordinaryPoints P := by
  rw [mem_ordinaryPoints_iff]
  exact ⟨h.1, q, h⟩

lemma line_sum_of_ordinaryPair {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    {p q : Point} (h : IsOrdinaryPair P p q) : w p + w q = c := by
  rw [← hsum p h.1 q h.2.1 h.2.2.1, h.2.2.2]
  simp [h.2.2.1]

/-- Every point has weight at most half the common line weight. -/
lemma weight_le_half_of_avoiding {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P) {p : Point} (hp : p ∈ P) :
    w p ≤ c / 2 := by
  obtain ⟨q, r, hqr, hpavoid⟩ := havoid p hp
  have hpq : p ≠ q := by
    intro h
    subst q
    exact hpavoid (left_mem_lineFiber hp)
  have hpr : p ≠ r := by
    intro h
    subst r
    exact hpavoid (right_mem_lineFiber hp)
  have hpqle : w p + w q ≤ c := by
    calc
      w p + w q ≤ ∑ x ∈ lineFiber P p q, w x :=
        pair_weight_le_line_sum hpos hp hqr.1 hpq
      _ = c := hsum p hp q hqr.1 hpq
  have hprle : w p + w r ≤ c := by
    calc
      w p + w r ≤ ∑ x ∈ lineFiber P p r, w x :=
        pair_weight_le_line_sum hpos hp hqr.2.1 hpr
      _ = c := hsum p hp r hqr.2.1 hpr
  have hqr_eq : w q + w r = c := line_sum_of_ordinaryPair hsum hqr
  linarith

/-- The endpoints of every ordinary line have the common weight `c/2`. -/
lemma ordinaryPair_weights_eq_half {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P) {p q : Point} (hpqOrd : IsOrdinaryPair P p q) :
    w p = c / 2 ∧ w q = c / 2 := by
  have hp_le := weight_le_half_of_avoiding hpos hsum havoid hpqOrd.1
  have hq_le := weight_le_half_of_avoiding hpos hsum havoid hpqOrd.2.1
  have hpq_eq := line_sum_of_ordinaryPair hsum hpqOrd
  constructor <;> linarith

lemma weight_eq_half_of_mem_ordinaryPoints {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P) {p : Point} (hp : p ∈ ordinaryPoints P) :
    w p = c / 2 := by
  rw [mem_ordinaryPoints_iff] at hp
  obtain ⟨_, q, hpq⟩ := hp
  exact (ordinaryPair_weights_eq_half hpos hsum havoid hpq).1

/-- Every line between two distinct ordinary points is ordinary. -/
lemma ordinaryPair_of_mem_ordinaryPoints {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P) {p q : Point}
    (hp : p ∈ ordinaryPoints P) (hq : q ∈ ordinaryPoints P) (hpq : p ≠ q) :
    IsOrdinaryPair P p q := by
  have hpP := (mem_ordinaryPoints_iff.mp hp).1
  have hqP := (mem_ordinaryPoints_iff.mp hq).1
  refine ⟨hpP, hqP, hpq, lineFiber_eq_pair_of_pair_weight_eq hpos hsum hpP hqP hpq ?_⟩
  rw [weight_eq_half_of_mem_ordinaryPoints hpos hsum havoid hp,
    weight_eq_half_of_mem_ordinaryPoints hpos hsum havoid hq]
  linarith

/-- Ordinary lines are exactly the lines joining two distinct points of `ordinaryPoints`. -/
theorem ordinaryPair_iff_mem_ordinaryPoints {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P) {p q : Point} :
    IsOrdinaryPair P p q ↔ p ∈ ordinaryPoints P ∧ q ∈ ordinaryPoints P ∧ p ≠ q := by
  constructor
  · intro h
    have hp := ordinaryPair_left_mem h
    have hsym : IsOrdinaryPair P q p := by
      refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_⟩
      rw [lineFiber_swap, h.2.2.2]
      exact Finset.pair_comm p q
    exact ⟨hp, ordinaryPair_left_mem hsym, h.2.2.1⟩
  · rintro ⟨hp, hq, hpq⟩
    exact ordinaryPair_of_mem_ordinaryPoints hpos hsum havoid hp hq hpq

/-- Every nonordinary point has weight strictly less than `c/2`. -/
theorem weight_lt_half_of_mem_nonordinaryPoints {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P) {p : Point} (hp : p ∈ nonordinaryPoints P) :
    w p < c / 2 := by
  have hpP : p ∈ P := (Finset.mem_sdiff.mp hp).1
  have hple := weight_le_half_of_avoiding hpos hsum havoid hpP
  apply lt_of_le_of_ne hple
  intro heq
  obtain ⟨q, r, hqr, hpavoid⟩ := havoid p hpP
  have hpq : p ≠ q := by
    intro h
    subst q
    exact hpavoid (left_mem_lineFiber hpP)
  have hqhalf := (ordinaryPair_weights_eq_half hpos hsum havoid hqr).1
  have hpqOrd : IsOrdinaryPair P p q := by
    refine ⟨hpP, hqr.1, hpq,
      lineFiber_eq_pair_of_pair_weight_eq hpos hsum hpP hqr.1 hpq ?_⟩
    rw [heq, hqhalf]
    linarith
  have hpA := ordinaryPair_left_mem hpqOrd
  exact (Finset.mem_sdiff.mp hp).2 hpA

/-- Bundled primal reduction used after the geometric avoiding-line lemma. -/
theorem magic_weight_reduction {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P) :
    (∀ p ∈ ordinaryPoints P, w p = c / 2) ∧
      (∀ p ∈ nonordinaryPoints P, w p < c / 2) ∧
      (∀ p ∈ ordinaryPoints P, ∀ q ∈ ordinaryPoints P, p ≠ q →
        lineFiber P p q = {p, q}) ∧
      (∀ p q, IsOrdinaryPair P p q →
        p ∈ ordinaryPoints P ∧ q ∈ ordinaryPoints P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact weight_eq_half_of_mem_ordinaryPoints hpos hsum havoid hp
  · intro p hp
    exact weight_lt_half_of_mem_nonordinaryPoints hpos hsum havoid hp
  · intro p hp q hq hpq
    exact (ordinaryPair_of_mem_ordinaryPoints hpos hsum havoid hp hq hpq).2.2.2
  · intro p q hpq
    have h := (ordinaryPair_iff_mem_ordinaryPoints hpos hsum havoid).mp hpq
    exact ⟨h.1, h.2.1⟩

/-! ## The reduced red--blue configuration -/

/-- The ordinary points really form a subset of the original configuration. -/
lemma ordinaryPoints_subset (P : Finset Point) : ordinaryPoints P ⊆ P := by
  intro p hp
  exact (mem_ordinaryPoints_iff.mp hp).1

/-- The nonordinary points really form a subset of the original configuration. -/
lemma nonordinaryPoints_subset (P : Finset Point) : nonordinaryPoints P ⊆ P := by
  intro p hp
  exact (Finset.mem_sdiff.mp hp).1

/-- The ordinary and nonordinary points partition `P`. -/
lemma ordinaryPoints_union_nonordinaryPoints (P : Finset Point) :
    ordinaryPoints P ∪ nonordinaryPoints P = P := by
  apply Finset.Subset.antisymm
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ordinaryPoints_subset P hp
    · exact nonordinaryPoints_subset P hp
  · intro p hp
    by_cases hpA : p ∈ ordinaryPoints P
    · exact Finset.mem_union_left _ hpA
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp, hpA⟩)

/-- The two colour classes in the primal reduction are disjoint. -/
lemma disjoint_ordinaryPoints_nonordinaryPoints (P : Finset Point) :
    Disjoint (ordinaryPoints P) (nonordinaryPoints P) := by
  rw [Finset.disjoint_left]
  intro p hpA hpB
  exact (Finset.mem_sdiff.mp hpB).2 hpA

/-- If every point is incident with an ordinary line, all spanned lines are
ordinary and the configuration is in general position. -/
theorem inGeneralPosition_of_nonordinaryPoints_eq_empty
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P)
    (hB : nonordinaryPoints P = ∅) : InGeneralPosition P := by
  intro p hp q hq hpq
  have hpA : p ∈ ordinaryPoints P := by
    by_contra hpa
    have : p ∈ nonordinaryPoints P := Finset.mem_sdiff.mpr ⟨hp, hpa⟩
    simpa [hB] using this
  have hqA : q ∈ ordinaryPoints P := by
    by_contra hqa
    have : q ∈ nonordinaryPoints P := Finset.mem_sdiff.mpr ⟨hq, hqa⟩
    simpa [hB] using this
  exact (ordinaryPair_of_mem_ordinaryPoints hpos hsum havoid hpA hqA hpq).2.2.2

/-- The exact hypotheses passed from the metric weight argument to the
projective-arrangement part of the ABKPR proof.  Red points are the ordinary
points; blue points are their complement. -/
def IsReducedMagic (P : Finset Point) (w : Point → ℝ) (c : ℝ) : Prop :=
  0 < c ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (∑ x ∈ lineFiber P p q, w x) = c) ∧
    (∀ p ∈ ordinaryPoints P, w p = c / 2) ∧
    (∀ p ∈ nonordinaryPoints P, 0 < w p ∧ w p < c / 2) ∧
    (∀ p ∈ ordinaryPoints P, ∀ q ∈ ordinaryPoints P, p ≠ q →
      lineFiber P p q = {p, q}) ∧
    (∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (lineFiber P p q = {p, q} ↔
        p ∈ ordinaryPoints P ∧ q ∈ ordinaryPoints P))

/-- The avoiding-line weight argument supplies all reduced red--blue
hypotheses, including the exact characterization of ordinary fibers. -/
theorem isReducedMagic_of_magic_and_avoiding
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hpos : ∀ x ∈ P, 0 < w x)
    (hc : 0 < c)
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → (∑ x ∈ lineFiber P p q, w x) = c)
    (havoid : HasAvoidingOrdinaryLine P) : IsReducedMagic P w c := by
  have hred := magic_weight_reduction hpos hsum havoid
  refine ⟨hc, hsum, hred.1, ?_, hred.2.2.1, ?_⟩
  · intro p hp
    exact ⟨hpos p (nonordinaryPoints_subset P hp), hred.2.1 p hp⟩
  · intro p hp q hq hpq
    constructor
    · intro hline
      have hord : IsOrdinaryPair P p q := ⟨hp, hq, hpq, hline⟩
      exact (ordinaryPair_iff_mem_ordinaryPoints hpos hsum havoid).mp hord |>.1
        |> fun hpA ↦ ⟨hpA,
          ((ordinaryPair_iff_mem_ordinaryPoints hpos hsum havoid).mp hord).2.1⟩
    · rintro ⟨hpA, hqA⟩
      exact (ordinaryPair_of_mem_ordinaryPoints hpos hsum havoid hpA hqA hpq).2.2.2

/-- An avoiding ordinary line for an ordinary point supplies two further
ordinary points, so the red class has at least three elements. -/
lemma three_le_card_ordinaryPoints_of_avoiding {P : Finset Point}
    (hA : (ordinaryPoints P).Nonempty)
    (havoid : HasAvoidingOrdinaryLine P) :
    3 ≤ (ordinaryPoints P).card := by
  classical
  obtain ⟨p, hpA⟩ := hA
  have hpP := ordinaryPoints_subset P hpA
  obtain ⟨q, r, hqr, hpavoid⟩ := havoid p hpP
  have hqA := ordinaryPair_left_mem hqr
  have hrA : r ∈ ordinaryPoints P := by
    have hsym : IsOrdinaryPair P r q := by
      refine ⟨hqr.2.1, hqr.1, hqr.2.2.1.symm, ?_⟩
      rw [lineFiber_swap, hqr.2.2.2]
      exact Finset.pair_comm q r
    exact ordinaryPair_left_mem hsym
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact hpavoid (left_mem_lineFiber hpP)
  have hpr : p ≠ r := by
    intro hpr
    subst r
    exact hpavoid (right_mem_lineFiber hpP)
  have hsubset : {p, q, r} ⊆ ordinaryPoints P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hpA
    · exact hqA
    · exact hrA
  have hcard := Finset.card_le_card hsubset
  simpa [hpq, hpr, hqr.2.2.1] using hcard

/-- Once the two genuinely geometric inputs are supplied, the forward
classification is a formal consequence of Sylvester--Gallai and the weight
reduction above.  This theorem fixes the exact interface of those inputs. -/
theorem classified_of_magic_of_geometric_cores
    (avoidingCore : ∀ {P : Finset Point},
      ¬ Collinear ℝ (P : Set Point) → ¬ IsNearPencil P →
        HasAvoidingOrdinaryLine P)
    (reducedCore : ∀ {P : Finset Point} {w : Point → ℝ} {c : ℝ},
      3 ≤ (ordinaryPoints P).card → (nonordinaryPoints P).Nonempty →
        IsReducedMagic P w c → IsFailedFano P)
    {P : Finset Point} (hcard : 2 ≤ P.card) (hmagic : IsMagic P) :
    IsCollinearConfig P ∨ InGeneralPosition P ∨
      IsNearPencil P ∨ IsFailedFano P := by
  classical
  by_cases hcol : IsCollinearConfig P
  · exact Or.inl hcol
  have hncol : ¬ Collinear ℝ (P : Set Point) := by
    intro h
    exact hcol (isCollinearConfig_of_collinear h)
  by_cases hgp : InGeneralPosition P
  · exact Or.inr (Or.inl hgp)
  by_cases hnp : IsNearPencil P
  · exact Or.inr (Or.inr (Or.inl hnp))
  obtain ⟨w, c, hpos, hc, hsum⟩ := hmagic
  have havoid := avoidingCore hncol hnp
  have hA : (ordinaryPoints P).Nonempty := by
    obtain ⟨p, q, hpq⟩ := exists_ordinaryPair_of_not_collinear hncol
    exact ⟨p, ordinaryPair_left_mem hpq⟩
  have hB : (nonordinaryPoints P).Nonempty := by
    by_contra hBempty
    rw [Finset.not_nonempty_iff_eq_empty] at hBempty
    exact hgp (inGeneralPosition_of_nonordinaryPoints_eq_empty
      hpos hsum havoid hBempty)
  have hAcard := three_le_card_ordinaryPoints_of_avoiding hA havoid
  exact Or.inr (Or.inr (Or.inr <|
    reducedCore hAcard hB
      (isReducedMagic_of_magic_and_avoiding hpos hc hsum havoid)))

/-! ## Concrete projective duality for the reduced configuration -/

/-- Points of the homogeneous projective plane used by the dual arrangement. -/
abbrev DualPoint := ProjectiveDuality.Homogeneous

/-- The primal points whose dual projective lines pass through `h`. -/
noncomputable def dualIncidentFiber (P : Finset Point) (h : DualPoint) : Finset Point := by
  classical
  exact P.filter fun p ↦ h ∈ ProjectiveDuality.dualLine p

/-- A genuine crossing of at least two distinct dual lines of `P`. -/
def IsDualCrossing (P : Finset Point) (h : DualPoint) : Prop :=
  h ≠ ProjectiveDuality.homZero ∧
    ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧
      h ∈ ProjectiveDuality.dualLine p ∧
      h ∈ ProjectiveDuality.dualLine q

private lemma local_collinear3_iff_projective_collinear3 (p q r : Point) :
    Collinear3 p q r ↔ ProjectiveDuality.Collinear3 p q r := by
  rfl

/-- Any common point of the dual lines of two distinct points lies on the
dual line of every point collinear with them.  This is the arbitrary-witness
form of projective concurrency needed to identify whole line fibers. -/
lemma mem_dualLine_of_collinear3 {p q r : Point} {h : DualPoint}
    (hpq : p ≠ q) (hp : h ∈ ProjectiveDuality.dualLine p)
    (hq : h ∈ ProjectiveDuality.dualLine q) (hcol : Collinear3 p q r) :
    h ∈ ProjectiveDuality.dualLine r := by
  rcases h with ⟨u, v, z⟩
  simp only [ProjectiveDuality.dualLine, ProjectiveDuality.dot,
    ProjectiveDuality.embed, Set.mem_setOf_eq] at hp hq ⊢
  have hcoord : q 0 - p 0 ≠ 0 ∨ q 1 - p 1 ≠ 0 := by
    by_contra hn
    simp only [not_or, not_not] at hn
    apply hpq
    apply PiLp.ext
    intro i
    fin_cases i
    · exact sub_eq_zero.mp hn.1 |>.symm
    · exact sub_eq_zero.mp hn.2 |>.symm
  rw [local_collinear3_iff_projective_collinear3] at hcol
  simp only [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet] at hcol
  rcases hcoord with hx | hy
  · have hmul :
        (q 0 - p 0) * (r 0 * u + r 1 * v + 1 * z) = 0 := by
        linear_combination
          (q 0 - p 0) * hp + (r 0 - p 0) * (hq - hp) + v * hcol
    exact (mul_eq_zero.mp hmul).resolve_left hx
  · have hmul :
        (q 1 - p 1) * (r 0 * u + r 1 * v + 1 * z) = 0 := by
        linear_combination
          (q 1 - p 1) * hp + (r 1 - p 1) * (hq - hp) - u * hcol
    exact (mul_eq_zero.mp hmul).resolve_left hy

/-- A nonzero common point of three dual lines forces primal collinearity. -/
lemma collinear3_of_mem_three_dualLines {p q r : Point} {h : DualPoint}
    (hpq : p ≠ q) (hne : h ≠ ProjectiveDuality.homZero)
    (hp : h ∈ ProjectiveDuality.dualLine p)
    (hq : h ∈ ProjectiveDuality.dualLine q)
    (hr : h ∈ ProjectiveDuality.dualLine r) : Collinear3 p q r := by
  rw [local_collinear3_iff_projective_collinear3]
  exact (ProjectiveDuality.collinear3_iff_threeConcurrent hpq).mpr
    ⟨h, hne, hp, hq, hr⟩

/-- Every dual crossing has exactly the same incident-point finset as the
primal line fiber of any two distinct incident points. -/
theorem dualIncidentFiber_eq_lineFiber {P : Finset Point} {h : DualPoint}
    (hne : h ≠ ProjectiveDuality.homZero) {p q : Point}
    (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (hph : h ∈ ProjectiveDuality.dualLine p)
    (hqh : h ∈ ProjectiveDuality.dualLine q) :
    dualIncidentFiber P h = lineFiber P p q := by
  classical
  ext r
  simp only [dualIncidentFiber, lineFiber, Finset.mem_filter]
  apply and_congr_right
  intro hrP
  constructor
  · intro hrh
    exact collinear3_of_mem_three_dualLines hpq hne hph hqh hrh
  · intro hcol
    exact mem_dualLine_of_collinear3 hpq hph hqh hcol

/-- The common primal line-sum equation becomes the total incident-circle
weight equation at every dual crossing. -/
theorem dualCrossing_weight_eq {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hsum : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (∑ x ∈ lineFiber P p q, w x) = c)
    {h : DualPoint} (hc : IsDualCrossing P h) :
    (∑ p ∈ dualIncidentFiber P h, w p) = c := by
  rcases hc with ⟨hne, p, hp, q, hq, hpq, hph, hqh⟩
  rw [dualIncidentFiber_eq_lineFiber hne hp hq hpq hph hqh]
  exact hsum p hp q hq hpq

/-- A dual crossing is ordinary when exactly two dual lines pass through it. -/
def IsOrdinaryDualCrossing (P : Finset Point) (h : DualPoint) : Prop :=
  IsDualCrossing P h ∧ (dualIncidentFiber P h).card = 2

/-- Under the reduced hypotheses, the ordinary dual crossings are exactly
the crossings of two red (ordinary-point) lines. -/
theorem ordinaryDualCrossing_iff_red {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {h : DualPoint} :
    IsOrdinaryDualCrossing P h ↔
      ∃ p ∈ ordinaryPoints P, ∃ q ∈ ordinaryPoints P, p ≠ q ∧
        h ≠ ProjectiveDuality.homZero ∧
        h ∈ ProjectiveDuality.dualLine p ∧
        h ∈ ProjectiveDuality.dualLine q := by
  classical
  rcases hred with ⟨hc, hsum, hwA, hwB, hAA, hord⟩
  constructor
  · rintro ⟨⟨hne, p, hp, q, hq, hpq, hph, hqh⟩, hcard⟩
    have hfiber := dualIncidentFiber_eq_lineFiber hne hp hq hpq hph hqh
    have hpq_subset : {p, q} ⊆ lineFiber P p q := pair_subset_lineFiber hp hq
    have hline : lineFiber P p q = {p, q} := by
      symm
      apply Finset.eq_of_subset_of_card_le hpq_subset
      rw [← hfiber, hcard]
      simp [hpq]
    have hpqA := (hord p hp q hq hpq).mp hline
    exact ⟨p, hpqA.1, q, hpqA.2, hpq, hne, hph, hqh⟩
  · rintro ⟨p, hpA, q, hqA, hpq, hne, hph, hqh⟩
    have hp : p ∈ P := ordinaryPoints_subset P hpA
    have hq : q ∈ P := ordinaryPoints_subset P hqA
    refine ⟨⟨hne, p, hp, q, hq, hpq, hph, hqh⟩, ?_⟩
    rw [dualIncidentFiber_eq_lineFiber hne hp hq hpq hph hqh,
      hAA p hpA q hqA hpq]
    simp [hpq]

/-- Every crossing lying on a blue dual line contains a second blue line.
This is the dual form of the observation that a lone blue--red crossing would
have total weight strictly smaller than the common line weight, while two red
lines already form an ordinary crossing and leave no room for a blue line. -/
theorem exists_second_blue_of_blue_incident
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {h : DualPoint}
    (hcross : IsDualCrossing P h) {b : Point}
    (hbB : b ∈ nonordinaryPoints P)
    (hbh : h ∈ ProjectiveDuality.dualLine b) :
    ∃ b' ∈ nonordinaryPoints P, b' ≠ b ∧
      h ∈ ProjectiveDuality.dualLine b' := by
  classical
  rcases hred with ⟨hc, hsum, hwA, hwB, hAA, hord⟩
  rcases hcross with ⟨hne, p, hp, q, hq, hpq, hph, hqh⟩
  have hbP : b ∈ P := nonordinaryPoints_subset P hbB
  have hbS : b ∈ dualIncidentFiber P h := by
    simp [dualIncidentFiber, hbP, hbh]
  by_contra hex
  push Not at hex
  have blue_eq_b {x : Point} (hxB : x ∈ nonordinaryPoints P)
      (hxh : h ∈ ProjectiveDuality.dualLine x) : x = b := by
    by_contra hxb
    exact hex x hxB hxb hxh
  have hpS : p ∈ dualIncidentFiber P h := by
    simp [dualIncidentFiber, hp, hph]
  have hqS : q ∈ dualIncidentFiber P h := by
    simp [dualIncidentFiber, hq, hqh]
  obtain ⟨a, haP, haS, hab⟩ :
      ∃ a ∈ P, a ∈ dualIncidentFiber P h ∧ a ≠ b := by
    by_cases hpb : p = b
    · refine ⟨q, hq, hqS, ?_⟩
      intro hqb
      exact hpq (hpb.trans hqb.symm)
    · exact ⟨p, hp, hpS, hpb⟩
  have haBnot : a ∉ nonordinaryPoints P := by
    intro haB
    have hah : h ∈ ProjectiveDuality.dualLine a :=
      (Finset.mem_filter.mp haS).2
    exact hab (blue_eq_b haB hah)
  have haA : a ∈ ordinaryPoints P := by
    by_contra haAnot
    exact haBnot (Finset.mem_sdiff.mpr ⟨haP, haAnot⟩)
  have red_eq_a {x : Point} (hxA : x ∈ ordinaryPoints P)
      (hxh : h ∈ ProjectiveDuality.dualLine x) : x = a := by
    by_contra hxa
    have hxP : x ∈ P := ordinaryPoints_subset P hxA
    have hah : h ∈ ProjectiveDuality.dualLine a :=
      (Finset.mem_filter.mp haS).2
    have hfiber := dualIncidentFiber_eq_lineFiber hne haP hxP (Ne.symm hxa) hah hxh
    rw [hAA a haA x hxA (Ne.symm hxa)] at hfiber
    have hbpair : b ∈ ({a, x} : Finset Point) := by
      rw [← hfiber]
      exact hbS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbpair
    rcases hbpair with hba | hbx
    · exact hab hba.symm
    · exact (Finset.disjoint_left.mp
        (disjoint_ordinaryPoints_nonordinaryPoints P)) hxA (hbx ▸ hbB)
  have hS : dualIncidentFiber P h = {b, a} := by
    ext x
    constructor
    · intro hxS
      have hxP : x ∈ P := (Finset.mem_filter.mp hxS).1
      have hxh : h ∈ ProjectiveDuality.dualLine x :=
        (Finset.mem_filter.mp hxS).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hxA : x ∈ ordinaryPoints P
      · exact Or.inr (red_eq_a hxA hxh)
      · have hxB : x ∈ nonordinaryPoints P := Finset.mem_sdiff.mpr ⟨hxP, hxA⟩
        exact Or.inl (blue_eq_b hxB hxh)
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hbS
      · exact haS
  have hweight := dualCrossing_weight_eq hsum
    (show IsDualCrossing P h from ⟨hne, p, hp, q, hq, hpq, hph, hqh⟩)
  rw [hS] at hweight
  have hwa := hwA a haA
  have hwb := (hwB b hbB).2
  simp [hab.symm] at hweight
  linarith

/-! ## The constructive direction -/

/-- Swapping the two spanning points does not change a line fiber. -/
lemma lineFiber_comm (P : Finset Point) (p q : Point) :
    lineFiber P p q = lineFiber P q p := by
  classical
  ext r
  simp only [lineFiber, Finset.mem_filter, and_congr_right_iff]
  intro _
  unfold Collinear3 orientationDet
  constructor <;> intro h
  · nlinarith
  · nlinarith

/-- A nonempty collinear configuration is magic (use unit weights). -/
theorem isMagic_of_isCollinearConfig {P : Finset Point} (hP : P.Nonempty)
    (hcol : IsCollinearConfig P) : IsMagic P := by
  classical
  refine ⟨fun _ ↦ 1, P.card, by simp, ?_, ?_⟩
  · exact_mod_cast hP.card_pos
  · intro p hp q hq hpq
    rw [hcol p hp q hq hpq]
    simp

/-- A configuration in general position is magic (use unit weights). -/
theorem isMagic_of_inGeneralPosition {P : Finset Point}
    (hgp : InGeneralPosition P) : IsMagic P := by
  classical
  refine ⟨fun _ ↦ 1, 2, by simp, by norm_num, ?_⟩
  intro p hp q hq hpq
  rw [hgp p hp q hq hpq]
  simp [hpq]

/-- An intrinsic near-pencil is magic: main-line points have weight one and
the apex has weight one less than the number of main-line points. -/
theorem isMagic_of_isNearPencil {P : Finset Point}
    (hnp : IsNearPencil P) : IsMagic P := by
  classical
  rcases hnp with ⟨z, hzP, hcard, hmain, hapex⟩
  let w : Point → ℝ := fun x ↦
    if x = z then ((P.erase z).card : ℝ) - 1 else 1
  refine ⟨w, (P.erase z).card, ?_, ?_, ?_⟩
  · intro x hxP
    by_cases hxz : x = z
    · simp only [w, if_pos hxz]
      have hn : (1 : ℝ) < (P.erase z).card := by
        exact_mod_cast (show 1 < (P.erase z).card from hcard)
      linarith
    · simp [w, hxz]
  · exact_mod_cast (show 0 < (P.erase z).card from lt_of_lt_of_le Nat.zero_lt_two hcard)
  · intro p hpP q hqP hpq
    by_cases hpz : p = z
    · subst p
      have hqz : q ≠ z := hpq.symm
      have hqM : q ∈ P.erase z := Finset.mem_erase.mpr ⟨hqz, hqP⟩
      rw [hapex q hqM]
      simp [w, hpq, hqz]
    · have hpM : p ∈ P.erase z := Finset.mem_erase.mpr ⟨hpz, hpP⟩
      by_cases hqz : q = z
      · subst q
        rw [lineFiber_comm, hapex p hpM]
        simp [w, hpz, Ne.symm hpz]
      · have hqM : q ∈ P.erase z := Finset.mem_erase.mpr ⟨hqz, hqP⟩
        rw [hmain p hpM q hqM hpq]
        calc
          (∑ x ∈ P.erase z, w x) = ∑ x ∈ P.erase z, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro x hx
            have hxz : x ≠ z := (Finset.mem_erase.mp hx).1
            simp [w, hxz]
          _ = (P.erase z).card := by simp

/-- A labelled failed-Fano configuration is magic: the three diagonal points
have weight two and the four base points weight one. -/
theorem isMagic_of_isFailedFano {P : Finset Point}
    (hff : IsFailedFano P) : IsMagic P := by
  classical
  rcases hff with ⟨e, hP, hlines⟩
  subst P
  let w : Point → ℝ := fun p ↦ (failedFanoWeight4 (Function.invFun e p) : ℝ)
  have hinv : ∀ i, Function.invFun e (e i) = i :=
    Function.leftInverse_invFun e.injective
  refine ⟨w, 4, ?_, by norm_num, ?_⟩
  · intro p hp
    rcases Finset.mem_map.mp hp with ⟨i, -, rfl⟩
    have hw : 0 < failedFanoWeight4 i := by
      unfold failedFanoWeight4
      split <;> omega
    simpa [w, hinv] using (show (0 : ℝ) < failedFanoWeight4 i by exact_mod_cast hw)
  · intro p hp q hq hpq
    rcases Finset.mem_map.mp hp with ⟨i, -, rfl⟩
    rcases Finset.mem_map.mp hq with ⟨j, -, rfl⟩
    have hij : i ≠ j := fun h ↦ hpq (congrArg e h)
    rw [hlines i j hij]
    rw [Finset.sum_map]
    simp only [w, hinv]
    rw [← Nat.cast_sum]
    exact_mod_cast failedFanoLine_weight4 i j hij

/-- The four configurations listed in the resolution all admit positive equal
line weights. -/
theorem isMagic_of_classified {P : Finset Point} (hcard : 2 ≤ P.card)
    (h : IsCollinearConfig P ∨ InGeneralPosition P ∨
      IsNearPencil P ∨ IsFailedFano P) : IsMagic P := by
  rcases h with hcol | hgp | hnp | hff
  · exact isMagic_of_isCollinearConfig
      (Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hcard)) hcol
  · exact isMagic_of_inGeneralPosition hgp
  · exact isMagic_of_isNearPencil hnp
  · exact isMagic_of_isFailedFano hff

end

end Erdos735
