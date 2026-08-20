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
import ErdosProblems.Erdos735.SylvesterGallai
import ErdosProblems.Erdos735.AvoidingOrdinary
import ErdosProblems.Erdos735.ProjectiveDuality

/-!
# Erdős Problem 735: primal incidence and weight reduction

This module contains the affine incidence definitions, the constructive cases,
the ordinary-line weight reduction, and the failed-Fano recognition lemmas used
by the final classification theorem in `ErdosProblems.Erdos735`.

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

lemma three_le_card_of_not_collinear {P : Finset Point}
    (hP : ¬ Collinear ℝ (P : Set Point)) : 3 ≤ P.card := by
  by_contra h
  have hle : P.card ≤ 2 := by omega
  have hcases : P.card = 0 ∨ P.card = 1 ∨ P.card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hzero
    subst P
    exact hP (by simpa only [Finset.coe_empty] using (collinear_empty ℝ Point))
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hone
    exact hP (by simpa using collinear_singleton ℝ p)
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp htwo
    exact hP (by simpa [hpq] using collinear_pair ℝ p q)

lemma isOrdinaryPair_of_erase_of_not_collinear
    {P : Finset Point} {p q r : Point}
    (hqr : IsOrdinaryPair (P.erase p) q r)
    (havoid : ¬ Collinear3 q r p) : IsOrdinaryPair P q r := by
  classical
  refine ⟨Finset.mem_of_mem_erase hqr.1, Finset.mem_of_mem_erase hqr.2.1,
    hqr.2.2.1, ?_⟩
  ext x
  constructor
  · intro hx
    have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
    have hxcol : Collinear3 q r x := (Finset.mem_filter.mp hx).2
    have hxp : x ≠ p := by
      intro h
      subst x
      exact havoid hxcol
    have hxErase : x ∈ lineFiber (P.erase p) q r :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hxp, hxP⟩, hxcol⟩
    rw [hqr.2.2.2] at hxErase
    exact hxErase
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact left_mem_lineFiber (Finset.mem_of_mem_erase hqr.1)
    · exact right_mem_lineFiber (Finset.mem_of_mem_erase hqr.2.1)

lemma not_mem_lineFiber_of_not_collinear
    {P : Finset Point} {p q r : Point} (h : ¬ Collinear3 q r p) :
    p ∉ lineFiber P q r := by
  classical
  intro hp
  exact h (Finset.mem_filter.mp hp).2

/-- Exact bookkeeping bridge from prescribed-external-point Sylvester--Gallai
to the input required by the weight reduction. -/
theorem hasAvoidingOrdinaryLine_of_directional
    (directional : ∀ (Q : Finset Point) (p : Point), p ∉ Q →
      ¬ Collinear ℝ (Q : Set Point) →
        ∃ q r, IsOrdinaryPair Q q r ∧ ¬ Collinear3 q r p)
    {P : Finset Point} (hP : ¬ Collinear ℝ (P : Set Point))
    (hnp : ¬ IsNearPencil P) : HasAvoidingOrdinaryLine P := by
  classical
  have hcard : 3 ≤ P.card := three_le_card_of_not_collinear hP
  intro p hp
  have hQncol := every_erase_not_collinear_of_not_nearPencil hcard hP hnp p hp
  obtain ⟨q, r, hqr, havoid⟩ :=
    directional (P.erase p) p (Finset.notMem_erase p P) hQncol
  refine ⟨q, r, isOrdinaryPair_of_erase_of_not_collinear hqr havoid,
    not_mem_lineFiber_of_not_collinear havoid⟩

/-- The unconditional avoiding-line core, obtained from the projective chart
and anisotropic Kelly minimization theorem. -/
theorem hasAvoidingOrdinaryLine_of_not_collinear_not_nearPencil
    {P : Finset Point} (hP : ¬ Collinear ℝ (P : Set Point))
    (hnp : ¬ IsNearPencil P) : HasAvoidingOrdinaryLine P := by
  classical
  apply hasAvoidingOrdinaryLine_of_directional (hP := hP) (hnp := hnp)
  intro Q p hp hncol
  obtain ⟨q, hq, r, hr, hqr, hfiber, havoid⟩ :=
    Erdos735DirectionalKelly.exists_ordinary_filter_avoiding_external Q hp hncol
  have hordinary : IsOrdinaryPair Q q r := by
    refine ⟨hq, hr, hqr, ?_⟩
    change Q.filter (fun c : Point ↦ orientationDet q r c = 0) = {q, r}
    change Q.filter (fun c : Point ↦ orientationDet q r c = 0) = {q, r} at hfiber
    exact hfiber
  refine ⟨q, r, hordinary, ?_⟩
  simpa [Collinear3, orientationDet,
    Erdos735DirectionalKelly.euclideanDet] using havoid

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

/-- Outside the three elementary alternatives, a magic configuration canonically
supplies a nontrivial reduced red--blue magic configuration.  The avoiding-line
input is unconditional here: it is discharged by the projective-anisotropic
directional Sylvester--Gallai theorem above. -/
theorem exists_reducedMagic_of_magic_of_nonexceptional
    {P : Finset Point} (hmagic : IsMagic P)
    (hncol : ¬ Collinear ℝ (P : Set Point))
    (hnp : ¬ IsNearPencil P) (hgp : ¬ InGeneralPosition P) :
    ∃ (w : Point → ℝ) (c : ℝ),
      3 ≤ (ordinaryPoints P).card ∧
        (nonordinaryPoints P).Nonempty ∧ IsReducedMagic P w c := by
  classical
  obtain ⟨w, c, hpos, hc, hsum⟩ := hmagic
  have havoid : HasAvoidingOrdinaryLine P :=
    hasAvoidingOrdinaryLine_of_not_collinear_not_nearPencil hncol hnp
  have hA : (ordinaryPoints P).Nonempty := by
    obtain ⟨p, q, hpq⟩ := exists_ordinaryPair_of_not_collinear hncol
    exact ⟨p, ordinaryPair_left_mem hpq⟩
  have hB : (nonordinaryPoints P).Nonempty := by
    by_contra hBempty
    rw [Finset.not_nonempty_iff_eq_empty] at hBempty
    exact hgp (inGeneralPosition_of_nonordinaryPoints_eq_empty
      hpos hsum havoid hBempty)
  exact ⟨w, c, three_le_card_ordinaryPoints_of_avoiding hA havoid, hB,
    isReducedMagic_of_magic_and_avoiding hpos hc hsum havoid⟩

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

/-- With the avoiding-line theorem discharged, the forward classification has
only the reduced red--blue case left.  This is a reduction lemma, not the final
resolution: its sole geometric input is intended to be proved below. -/
theorem classified_of_magic_of_reduced_core
    (reducedCore : ∀ {P : Finset Point} {w : Point → ℝ} {c : ℝ},
      3 ≤ (ordinaryPoints P).card → (nonordinaryPoints P).Nonempty →
        IsReducedMagic P w c → IsFailedFano P)
    {P : Finset Point} (hcard : 2 ≤ P.card) (hmagic : IsMagic P) :
    IsCollinearConfig P ∨ InGeneralPosition P ∨
      IsNearPencil P ∨ IsFailedFano P := by
  exact classified_of_magic_of_geometric_cores
    (fun hP hnp ↦ hasAvoidingOrdinaryLine_of_not_collinear_not_nearPencil hP hnp)
    reducedCore hcard hmagic

/-- A coarser but especially simple reduction interface: proving that every
reduced magic configuration is failed Fano suffices for the full forward
classification. -/
theorem classified_of_magic_of_reducedMagic
    (reducedCore : ∀ {P : Finset Point} {w : Point → ℝ} {c : ℝ},
      IsReducedMagic P w c → IsFailedFano P)
    {P : Finset Point} (hcard : 2 ≤ P.card) (hmagic : IsMagic P) :
    IsCollinearConfig P ∨ InGeneralPosition P ∨
      IsNearPencil P ∨ IsFailedFano P := by
  apply classified_of_magic_of_reduced_core (hcard := hcard) (hmagic := hmagic)
  intro Q w c _ _ hred
  exact reducedCore hred

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

/-- Every primal line joining a red point to a blue point contains a second
blue point.  This is the affine incarnation of
`exists_second_blue_of_blue_incident`, obtained by taking the concrete
projective intersection of the two corresponding dual lines. -/
theorem exists_second_nonordinary_on_red_blue_line
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {a b : Point}
    (haA : a ∈ ordinaryPoints P) (hbB : b ∈ nonordinaryPoints P) :
    ∃ b' ∈ nonordinaryPoints P, b' ≠ b ∧ Collinear3 a b b' := by
  have haP : a ∈ P := ordinaryPoints_subset P haA
  have hbP : b ∈ P := nonordinaryPoints_subset P hbB
  have hab : a ≠ b := by
    intro hab
    subst b
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) haA hbB
  let h : DualPoint := ProjectiveDuality.pairIntersection a b
  have hcross : IsDualCrossing P h := by
    exact ⟨ProjectiveDuality.pairIntersection_ne_zero hab,
      a, haP, b, hbP, hab,
      ProjectiveDuality.pairIntersection_mem_left a b,
      ProjectiveDuality.pairIntersection_mem_right a b⟩
  obtain ⟨b', hb'B, hb'ne, hb'h⟩ :=
    exists_second_blue_of_blue_incident hred hcross hbB
      (ProjectiveDuality.pairIntersection_mem_right a b)
  refine ⟨b', hb'B, hb'ne, ?_⟩
  rw [local_collinear3_iff_projective_collinear3]
  exact (ProjectiveDuality.collinear3_iff_pairIntersection_mem a b b').mpr hb'h

/-- In a reduced magic configuration with at least two red points and at
least one blue point, the blue points are not collinear.  Indeed, every
red--blue line contains a second blue point; if all blue points lay on one
line, this would put every red point on that same line, contradicting the
fact that a line through two red points is ordinary. -/
theorem not_collinear_nonordinaryPoints_of_reducedMagic
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hAcard : 2 ≤ (ordinaryPoints P).card)
    (hB : (nonordinaryPoints P).Nonempty)
    (hred : IsReducedMagic P w c) :
    ¬ Collinear ℝ (nonordinaryPoints P : Set Point) := by
  classical
  intro hBcol
  obtain ⟨a₀, ha₀A⟩ : (ordinaryPoints P).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_two hAcard)
  obtain ⟨b₀, hb₀B⟩ := hB
  obtain ⟨b₁, hb₁B, hb₁ne, ha₀b₀b₁⟩ :=
    exists_second_nonordinary_on_red_blue_line hred ha₀A hb₀B
  have hb₀ne : b₀ ≠ b₁ := hb₁ne.symm
  have allA_mem : ∀ a ∈ ordinaryPoints P, a ∈ line[ℝ, b₀, b₁] := by
    intro a haA
    obtain ⟨b, hbB, hbne, habcol⟩ :=
      exists_second_nonordinary_on_red_blue_line hred haA hb₀B
    have hbline : b ∈ line[ℝ, b₀, b₁] :=
      hBcol.mem_affineSpan_of_mem_of_ne hb₀B hb₁B hbB hb₀ne
    have habline : a ∈ line[ℝ, b₀, b] :=
      (collinear3_iff_mem_affineSpan_pair hbne.symm).mp
        (collinear3_cycle.mp habcol)
    have hlines : line[ℝ, b₀, b] = line[ℝ, b₀, b₁] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (left_mem_affineSpan_pair ℝ b₀ b₁) hbline hbne.symm
    rwa [hlines] at habline
  obtain ⟨a₁, ha₁A, a₂, ha₂A, ha₁a₂⟩ :=
    Finset.one_lt_card.mp (show 1 < (ordinaryPoints P).card by omega)
  have ha₁line := allA_mem a₁ ha₁A
  have ha₂line := allA_mem a₂ ha₂A
  have hredline : line[ℝ, a₁, a₂] = line[ℝ, b₀, b₁] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne ha₁line ha₂line ha₁a₂
  have hb₀line : b₀ ∈ line[ℝ, a₁, a₂] := by
    rw [hredline]
    exact left_mem_affineSpan_pair ℝ b₀ b₁
  have hb₀fiber : b₀ ∈ lineFiber P a₁ a₂ := by
    rw [lineFiber, Finset.mem_filter]
    exact ⟨nonordinaryPoints_subset P hb₀B,
      (collinear3_iff_mem_affineSpan_pair ha₁a₂).mpr hb₀line⟩
  have hAA := hred.2.2.2.2.1 a₁ ha₁A a₂ ha₂A ha₁a₂
  rw [hAA] at hb₀fiber
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb₀fiber
  rcases hb₀fiber with hb₀a₁ | hb₀a₂
  · exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A (hb₀a₁ ▸ hb₀B)
  · exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₂A (hb₀a₂ ▸ hb₀B)


noncomputable section

open scoped BigOperators

/-- The projective blue vertices on the blue dual line of `s`, represented
primitively as the distinct primal line fibers through `s` and another blue
point. -/
noncomputable def blueDirectionsThrough (P : Finset Point) (s : Point) :
    Finset (Finset Point) := by
  classical
  exact (nonordinaryPoints P).erase s |>.image (lineFiber P s)

/-- A bad blue vertex on the dual line of `s`: the corresponding primal
fiber contains exactly two blue points. -/
def IsDoubleBlueDirection (P : Finset Point) (s b : Point) : Prop :=
  s ∈ nonordinaryPoints P ∧ b ∈ nonordinaryPoints P ∧ s ≠ b ∧
    (lineFiber P s b ∩ nonordinaryPoints P).card = 2

/-- No three distinct blue points of the primal configuration are collinear;
dually, no three blue circles share a crossing. -/
def BlueGeneralPosition (P : Finset Point) : Prop :=
  ∀ x ∈ nonordinaryPoints P, ∀ y ∈ nonordinaryPoints P,
    ∀ z ∈ nonordinaryPoints P,
      x ≠ y → x ≠ z → y ≠ z → ¬ Collinear3 x y z

/-- Two distinct spanning pairs determine the same concrete fiber whenever
both points of the first pair lie on the line of the second pair. -/
lemma lineFiber_eq_of_mem_lineFiber {P : Finset Point} {p q r s : Point}
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hp : p ∈ lineFiber P r s) (hq : q ∈ lineFiber P r s) :
    lineFiber P p q = lineFiber P r s := by
  classical
  have hpLine : p ∈ line[ℝ, r, s] :=
    (collinear3_iff_mem_affineSpan_pair hrs).mp (Finset.mem_filter.mp hp).2
  have hqLine : q ∈ line[ℝ, r, s] :=
    (collinear3_iff_mem_affineSpan_pair hrs).mp (Finset.mem_filter.mp hq).2
  have hspan : line[ℝ, p, q] = line[ℝ, r, s] :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hpLine hqLine hpq
  ext x
  simp only [lineFiber, Finset.mem_filter, and_congr_right_iff]
  intro _
  rw [collinear3_iff_mem_affineSpan_pair hpq,
    collinear3_iff_mem_affineSpan_pair hrs, hspan]

/-- Four blue points in general position give exactly three blue vertices on
the dual line of each chosen blue point. -/
lemma blueDirectionsThrough_card_eq_three
    {P : Finset Point} (hBcard : (nonordinaryPoints P).card = 4)
    (hgp : BlueGeneralPosition P) {s : Point}
    (hsB : s ∈ nonordinaryPoints P) :
    (blueDirectionsThrough P s).card = 3 := by
  classical
  have hinj : Set.InjOn (lineFiber P s) (↑((nonordinaryPoints P).erase s) : Set Point) := by
    intro b hb b' hb' heq
    by_contra hbb'
    have hbParts := Finset.mem_erase.mp hb
    have hb'Parts := Finset.mem_erase.mp hb'
    have hb'P := nonordinaryPoints_subset P hb'Parts.2
    have hb'Line : b' ∈ lineFiber P s b := by
      rw [heq]
      exact right_mem_lineFiber hb'P
    have hcol : Collinear3 s b b' := (Finset.mem_filter.mp hb'Line).2
    exact hgp s hsB b hbParts.2 b' hb'Parts.2
      hbParts.1.symm hb'Parts.1.symm hbb' hcol
  rw [blueDirectionsThrough, Finset.card_image_iff.mpr hinj,
    Finset.card_erase_of_mem hsB, hBcard]

/-- In blue general position every crossing of two blue dual lines is
double-blue. -/
lemma isDoubleBlueDirection_of_blueGeneralPosition
    {P : Finset Point} (hgp : BlueGeneralPosition P)
    {s b : Point} (hsB : s ∈ nonordinaryPoints P)
    (hbB : b ∈ nonordinaryPoints P) (hsb : s ≠ b) :
    IsDoubleBlueDirection P s b := by
  classical
  refine ⟨hsB, hbB, hsb, ?_⟩
  have hsP := nonordinaryPoints_subset P hsB
  have hbP := nonordinaryPoints_subset P hbB
  have hblue : lineFiber P s b ∩ nonordinaryPoints P = {s, b} := by
    ext x
    constructor
    · intro hx
      have hxLine := (Finset.mem_inter.mp hx).1
      have hxB := (Finset.mem_inter.mp hx).2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hxs : x = s
      · exact Or.inl hxs
      right
      by_contra hxb
      have hcol : Collinear3 s b x := (Finset.mem_filter.mp hxLine).2
      exact hgp s hsB b hbB x hxB hsb (Ne.symm hxs) (Ne.symm hxb) hcol
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨left_mem_lineFiber hsP, hsB⟩
      · exact Finset.mem_inter.mpr ⟨right_mem_lineFiber hbP, hbB⟩
  rw [hblue]
  simp [hsb]

/-- The cardinality clause in a double-blue direction identifies its blue
part with the two named endpoints. -/
lemma blue_part_eq_pair_of_doubleBlue
    {P : Finset Point} {s b : Point}
    (hbad : IsDoubleBlueDirection P s b) :
    lineFiber P s b ∩ nonordinaryPoints P = {s, b} := by
  classical
  rcases hbad with ⟨hsB, hbB, hsb, hcard⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl
    · exact Finset.mem_inter.mpr
        ⟨left_mem_lineFiber (nonordinaryPoints_subset P hsB), hsB⟩
    · exact Finset.mem_inter.mpr
        ⟨right_mem_lineFiber (nonordinaryPoints_subset P hbB), hbB⟩
  · rw [hcard]
    simp [hsb]

/-- For any fixed blue point, sending a red point to the blue direction in
which its dual line meets the fixed blue dual line is injective.  This is the
projective-line pigeonhole principle used twice in ABKPR Lemma 1. -/
lemma card_ordinaryPoints_le_blueDirectionsThrough
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {s : Point}
    (hsB : s ∈ nonordinaryPoints P) :
    (ordinaryPoints P).card ≤ (blueDirectionsThrough P s).card := by
  classical
  have hsP : s ∈ P := nonordinaryPoints_subset P hsB
  have hdisj := Finset.disjoint_left.mp (disjoint_ordinaryPoints_nonordinaryPoints P)
  have direction_mem : ∀ a : ↑(ordinaryPoints P),
      lineFiber P s a.1 ∈ blueDirectionsThrough P s := by
    intro a
    have haP : a.1 ∈ P := ordinaryPoints_subset P a.2
    have hsa : s ≠ a.1 := by
      intro h
      exact hdisj a.2 (h ▸ hsB)
    let h := ProjectiveDuality.pairIntersection s a.1
    have hhne : h ≠ ProjectiveDuality.homZero :=
      ProjectiveDuality.pairIntersection_ne_zero hsa
    have hhs : h ∈ ProjectiveDuality.dualLine s :=
      ProjectiveDuality.pairIntersection_mem_left s a.1
    have hha : h ∈ ProjectiveDuality.dualLine a.1 :=
      ProjectiveDuality.pairIntersection_mem_right s a.1
    have hcross : IsDualCrossing P h :=
      ⟨hhne, s, hsP, a.1, haP, hsa, hhs, hha⟩
    obtain ⟨b, hbB, hbs, hhb⟩ :=
      exists_second_blue_of_blue_incident hred hcross hsB hhs
    have hbP : b ∈ P := nonordinaryPoints_subset P hbB
    have hEqA : dualIncidentFiber P h = lineFiber P s a.1 :=
      dualIncidentFiber_eq_lineFiber hhne hsP haP hsa hhs hha
    have hEqB : dualIncidentFiber P h = lineFiber P s b :=
      dualIncidentFiber_eq_lineFiber hhne hsP hbP hbs.symm hhs hhb
    simp only [blueDirectionsThrough, Finset.mem_image]
    exact ⟨b, Finset.mem_erase.mpr ⟨hbs, hbB⟩, hEqB.symm.trans hEqA⟩
  let f : ↑(ordinaryPoints P) → ↑(blueDirectionsThrough P s) :=
    fun a ↦ ⟨lineFiber P s a.1, direction_mem a⟩
  have hf : Function.Injective f := by
    intro a a' haa'
    apply Subtype.ext
    by_contra hne
    have hsa : s ≠ a.1 := by
      intro h
      exact hdisj a.2 (h ▸ hsB)
    have ha'a : a'.1 ∈ lineFiber P s a.1 := by
      have hfib : lineFiber P s a.1 = lineFiber P s a'.1 :=
        congrArg (fun x : ↑(blueDirectionsThrough P s) ↦ x.1) haa'
      rw [hfib]
      exact right_mem_lineFiber (ordinaryPoints_subset P a'.2)
    have hsRedLine : s ∈ lineFiber P a.1 a'.1 :=
      Finset.mem_filter.mpr ⟨hsP, collinear3_cycle.mp
        (Finset.mem_filter.mp ha'a).2⟩
    have hline := hred.2.2.2.2.1 a.1 a.2 a'.1 a'.2 hne
    rw [hline] at hsRedLine
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsRedLine
    exact hsRedLine.elim hsa (fun h ↦ hdisj a'.2 (h ▸ hsB))
  simpa using Fintype.card_le_of_injective f hf

/-- A red point cannot lie on two blue-blue lines sharing a blue endpoint
when the other three blue points are distinct. -/
lemma ordinaryPoint_not_on_adjacent_blue_lines
    {P : Finset Point} (hgp : BlueGeneralPosition P)
    {a b₀ b₁ b₂ : Point}
    (haA : a ∈ ordinaryPoints P)
    (hb₀B : b₀ ∈ nonordinaryPoints P)
    (hb₁B : b₁ ∈ nonordinaryPoints P)
    (hb₂B : b₂ ∈ nonordinaryPoints P)
    (hb₀₁ : b₀ ≠ b₁) (hb₀₂ : b₀ ≠ b₂) (hb₁₂ : b₁ ≠ b₂)
    (ha₀₁ : a ∈ lineFiber P b₀ b₁)
    (ha₀₂ : a ∈ lineFiber P b₀ b₂) : False := by
  classical
  have hb₀P := nonordinaryPoints_subset P hb₀B
  have ha_ne_b₀ : a ≠ b₀ := by
    intro h
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) haA (h ▸ hb₀B)
  have h₁ : lineFiber P a b₀ = lineFiber P b₀ b₁ :=
    lineFiber_eq_of_mem_lineFiber ha_ne_b₀ hb₀₁ ha₀₁ (left_mem_lineFiber hb₀P)
  have h₂ : lineFiber P a b₀ = lineFiber P b₀ b₂ :=
    lineFiber_eq_of_mem_lineFiber ha_ne_b₀ hb₀₂ ha₀₂ (left_mem_lineFiber hb₀P)
  have hb₂Line : b₂ ∈ lineFiber P b₀ b₁ := by
    rw [← h₁, h₂]
    exact right_mem_lineFiber (nonordinaryPoints_subset P hb₂B)
  exact hgp b₀ hb₀B b₁ hb₁B b₂ hb₂B hb₀₁ hb₀₂ hb₁₂
    (Finset.mem_filter.mp hb₂Line).2

private lemma ordinaryPoint_eq_diagonalLabel
    {P : Finset Point} (e : FailedFanoLabel ↪ Point)
    (hP : P = Finset.univ.map e)
    (hbase : ∀ i : FailedFanoLabel, 3 ≤ i.1 → e i ∈ nonordinaryPoints P)
    {a : Point} (haA : a ∈ ordinaryPoints P) :
    a = e 0 ∨ a = e 1 ∨ a = e 2 := by
  classical
  have haP := ordinaryPoints_subset P haA
  rw [hP] at haP
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp haP
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  all_goals
    exfalso
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) haA (hbase _ (by decide))

/-- If a blue dual line has exactly three blue crossing vertices, the reduced
hypotheses and the lower bound of three red lines force exactly three red
lines.  This is the first counting step in ABKPR Lemma 1. -/
lemma card_ordinaryPoints_eq_three_of_blueDirections
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    {s : Point} (hsB : s ∈ nonordinaryPoints P)
    (hthree : (blueDirectionsThrough P s).card = 3) :
    (ordinaryPoints P).card = 3 := by
  classical
  have hsP : s ∈ P := nonordinaryPoints_subset P hsB
  have hdisj := Finset.disjoint_left.mp (disjoint_ordinaryPoints_nonordinaryPoints P)
  have direction_mem : ∀ a : ↥(ordinaryPoints P),
      lineFiber P s a.1 ∈ blueDirectionsThrough P s := by
    intro a
    have haP : a.1 ∈ P := ordinaryPoints_subset P a.2
    have hsa : s ≠ a.1 := by
      intro h
      exact hdisj a.2 (h ▸ hsB)
    let h := ProjectiveDuality.pairIntersection s a.1
    have hhne : h ≠ ProjectiveDuality.homZero :=
      ProjectiveDuality.pairIntersection_ne_zero hsa
    have hhs : h ∈ ProjectiveDuality.dualLine s :=
      ProjectiveDuality.pairIntersection_mem_left s a.1
    have hha : h ∈ ProjectiveDuality.dualLine a.1 :=
      ProjectiveDuality.pairIntersection_mem_right s a.1
    have hcross : IsDualCrossing P h :=
      ⟨hhne, s, hsP, a.1, haP, hsa, hhs, hha⟩
    obtain ⟨b, hbB, hbs, hhb⟩ :=
      exists_second_blue_of_blue_incident hred hcross hsB hhs
    have hbP : b ∈ P := nonordinaryPoints_subset P hbB
    have hEqA : dualIncidentFiber P h = lineFiber P s a.1 :=
      dualIncidentFiber_eq_lineFiber hhne hsP haP hsa hhs hha
    have hEqB : dualIncidentFiber P h = lineFiber P s b :=
      dualIncidentFiber_eq_lineFiber hhne hsP hbP hbs.symm hhs hhb
    simp only [blueDirectionsThrough, Finset.mem_image]
    exact ⟨b, Finset.mem_erase.mpr ⟨hbs, hbB⟩, hEqB.symm.trans hEqA⟩
  let f : ↥(ordinaryPoints P) → ↥(blueDirectionsThrough P s) :=
    fun a ↦ ⟨lineFiber P s a.1, direction_mem a⟩
  have hf : Function.Injective f := by
    intro a a' haa'
    apply Subtype.ext
    by_contra hne
    have hsa : s ≠ a.1 := by
      intro h
      exact hdisj a.2 (h ▸ hsB)
    have ha'a' : a'.1 ∈ lineFiber P s a'.1 := right_mem_lineFiber
      (ordinaryPoints_subset P a'.2)
    have ha'a : a'.1 ∈ lineFiber P s a.1 := by
      have hfib : lineFiber P s a.1 = lineFiber P s a'.1 :=
        congrArg (fun x : ↥(blueDirectionsThrough P s) ↦ x.1) haa'
      rw [hfib]
      exact ha'a'
    have hcol : Collinear3 s a.1 a'.1 := (Finset.mem_filter.mp ha'a).2
    have hscol : Collinear3 a.1 a'.1 s := collinear3_cycle.mp hcol
    have hsRedLine : s ∈ lineFiber P a.1 a'.1 :=
      Finset.mem_filter.mpr ⟨hsP, hscol⟩
    rcases hred with ⟨_, _, _, _, hAA, _⟩
    have hline := hAA a.1 a.2 a'.1 a'.2 hne
    rw [hline] at hsRedLine
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsRedLine
    exact hsRedLine.elim hsa (fun h ↦ hdisj a'.2 (h ▸ hsB))
  have hcardle : (ordinaryPoints P).card ≤ (blueDirectionsThrough P s).card := by
    simpa using Fintype.card_le_of_injective f hf
  omega

/-- A double-blue direction contains exactly one red point.  Existence uses
the strict blue weight bound; uniqueness uses that every red-red fiber is
ordinary. -/
lemma existsUnique_ordinaryPoint_on_doubleBlue
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {s b : Point}
    (hbad : IsDoubleBlueDirection P s b) :
    ∃! a, a ∈ ordinaryPoints P ∧ a ∈ lineFiber P s b := by
  classical
  rcases hbad with ⟨hsB, hbB, hsb, hblueCard⟩
  have hsP := nonordinaryPoints_subset P hsB
  have hbP := nonordinaryPoints_subset P hbB
  rcases hred with ⟨hc, hsum, _, hwB, hAA, _⟩
  have hatMost : ∀ ⦃a a'⦄,
      a ∈ ordinaryPoints P ∧ a ∈ lineFiber P s b →
      a' ∈ ordinaryPoints P ∧ a' ∈ lineFiber P s b → a = a' := by
    intro a a' ha ha'
    by_contra haa'
    have hsame := lineFiber_eq_of_mem_lineFiber
      (P := P) (p := a) (q := a') (r := s) (s := b)
      haa' hsb ha.2 ha'.2
    have hsline : s ∈ lineFiber P a a' := by
      rw [hsame]
      exact left_mem_lineFiber hsP
    have hredLine := hAA a ha.1 a' ha'.1 haa'
    rw [hredLine] at hsline
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsline
    have hdisj := Finset.disjoint_left.mp (disjoint_ordinaryPoints_nonordinaryPoints P)
    exact hsline.elim
      (fun h ↦ hdisj ha.1 (h ▸ hsB))
      (fun h ↦ hdisj ha'.1 (h ▸ hsB))
  have hExists : ∃ a, a ∈ ordinaryPoints P ∧ a ∈ lineFiber P s b := by
    by_contra hnone
    push Not at hnone
    have hallBlue : lineFiber P s b = lineFiber P s b ∩ nonordinaryPoints P := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
        have hxA : x ∉ ordinaryPoints P := by
          intro hxA
          exact hnone x hxA hx
        exact Finset.mem_inter.mpr ⟨hx, Finset.mem_sdiff.mpr ⟨hxP, hxA⟩⟩
      · exact Finset.inter_subset_left
    have hfiberCard : (lineFiber P s b).card = 2 := by
      rw [hallBlue]
      exact hblueCard
    obtain ⟨x, y, hxy, hfiber⟩ := Finset.card_eq_two.mp hfiberCard
    have hxB : x ∈ nonordinaryPoints P := by
      have : x ∈ lineFiber P s b := by rw [hfiber]; simp
      rw [hallBlue] at this
      exact (Finset.mem_inter.mp this).2
    have hyB : y ∈ nonordinaryPoints P := by
      have : y ∈ lineFiber P s b := by rw [hfiber]; simp
      rw [hallBlue] at this
      exact (Finset.mem_inter.mp this).2
    have hlineSum := hsum s hsP b hbP hsb
    rw [hfiber] at hlineSum
    simp [hxy] at hlineSum
    linarith [(hwB x hxB).2, (hwB y hyB).2]
  obtain ⟨a, ha⟩ := hExists
  exact ⟨a, ha, fun y hy ↦ hatMost hy ha⟩

/-- Once the unique red point on a double-blue direction is named, its whole
primal line fiber is exactly the corresponding red-blue-blue triple. -/
lemma lineFiber_eq_triple_of_doubleBlue
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {s b a : Point}
    (hbad : IsDoubleBlueDirection P s b)
    (haA : a ∈ ordinaryPoints P) (haLine : a ∈ lineFiber P s b) :
    lineFiber P s b = {a, s, b} := by
  classical
  rcases hbad with ⟨hsB, hbB, hsb, hblueCard⟩
  have hsP := nonordinaryPoints_subset P hsB
  have hbP := nonordinaryPoints_subset P hbB
  have hblue : lineFiber P s b ∩ nonordinaryPoints P = {s, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨left_mem_lineFiber hsP, hsB⟩
      · exact Finset.mem_inter.mpr ⟨right_mem_lineFiber hbP, hbB⟩
    · rw [hblueCard]
      simp [hsb]
  have haUnique := existsUnique_ordinaryPoint_on_doubleBlue hred
    ⟨hsB, hbB, hsb, hblueCard⟩
  ext x
  constructor
  · intro hx
    have hxP : x ∈ P := (Finset.mem_filter.mp hx).1
    by_cases hxA : x ∈ ordinaryPoints P
    · have hxa : x = a := haUnique.unique ⟨hxA, hx⟩ ⟨haA, haLine⟩
      subst x
      simp
    · have hxB : x ∈ nonordinaryPoints P := Finset.mem_sdiff.mpr ⟨hxP, hxA⟩
      have : x ∈ ({s, b} : Finset Point) := by
        rw [← hblue]
        exact Finset.mem_inter.mpr ⟨hx, hxB⟩
      simpa only [Finset.mem_insert, Finset.mem_singleton] using Or.inr this
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haLine
    · exact left_mem_lineFiber hsP
    · exact right_mem_lineFiber hbP

/-- The incidence-counting heart of ABKPR Lemma 1, in primal language.
Once the three red points and the three directions on `s` have been named,
projection from the second bad blue point injects the third direction into
three possible nonordinary directions. -/
private lemma third_direction_card_le_three
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    {s s₂ s₃ a₀ a₁ a₂ : Point}
    (hbad₂ : IsDoubleBlueDirection P s s₂)
    (hbad₃ : IsDoubleBlueDirection P s s₃)
    (ha₀A : a₀ ∈ ordinaryPoints P)
    (ha₁A : a₁ ∈ ordinaryPoints P)
    (ha₂A : a₂ ∈ ordinaryPoints P)
    (ha₀a₁ : a₀ ≠ a₁) (ha₀a₂ : a₀ ≠ a₂)
    (ha₁a₂ : a₁ ≠ a₂)
    (hA : ordinaryPoints P = {a₀, a₁, a₂})
    (ha₀line : a₀ ∈ lineFiber P s s₂)
    (ha₂line : a₂ ∈ lineFiber P s s₃)
    (hdirs : blueDirectionsThrough P s =
      {lineFiber P s s₂, lineFiber P s s₃, lineFiber P s a₁}) :
    (lineFiber P s a₁).card ≤ 3 := by
  classical
  rcases hbad₂ with ⟨hsB, hs₂B, hss₂, hbad₂card⟩
  rcases hbad₃ with ⟨_, hs₃B, hss₃, hbad₃card⟩
  have hsP := nonordinaryPoints_subset P hsB
  have hs₂P := nonordinaryPoints_subset P hs₂B
  have hs₃P := nonordinaryPoints_subset P hs₃B
  have ha₁P := ordinaryPoints_subset P ha₁A
  have hsa₁ : s ≠ a₁ := by
    intro h
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A (h ▸ hsB)
  have hs₂a₁ : s₂ ≠ a₁ := by
    intro h
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A (h ▸ hs₂B)
  have hs₃a₁ : s₃ ≠ a₁ := by
    intro h
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A (h ▸ hs₃B)
  have hs₂notL : s₂ ∉ lineFiber P s a₁ := by
    intro hs₂L
    have heq : lineFiber P s a₁ = lineFiber P s s₂ :=
      (lineFiber_eq_of_mem_lineFiber hss₂ hsa₁
        (left_mem_lineFiber hsP) hs₂L).symm
    have ha₁bad : a₁ ∈ lineFiber P s s₂ := by
      rw [← heq]
      exact right_mem_lineFiber ha₁P
    have hu := existsUnique_ordinaryPoint_on_doubleBlue hred
      ⟨hsB, hs₂B, hss₂, hbad₂card⟩
    exact ha₀a₁ (hu.unique ⟨ha₀A, ha₀line⟩ ⟨ha₁A, ha₁bad⟩)
  have hs₃notL : s₃ ∉ lineFiber P s a₁ := by
    intro hs₃L
    have heq : lineFiber P s a₁ = lineFiber P s s₃ :=
      (lineFiber_eq_of_mem_lineFiber hss₃ hsa₁
        (left_mem_lineFiber hsP) hs₃L).symm
    have ha₁bad : a₁ ∈ lineFiber P s s₃ := by
      rw [← heq]
      exact right_mem_lineFiber ha₁P
    have hu := existsUnique_ordinaryPoint_on_doubleBlue hred
      ⟨hsB, hs₃B, hss₃, hbad₃card⟩
    exact ha₁a₂ (hu.unique ⟨ha₁A, ha₁bad⟩ ⟨ha₂A, ha₂line⟩)
  have hblue₂ : lineFiber P s s₂ ∩ nonordinaryPoints P = {s, s₂} :=
    blue_part_eq_pair_of_doubleBlue ⟨hsB, hs₂B, hss₂, hbad₂card⟩
  have hblue₃ : lineFiber P s s₃ ∩ nonordinaryPoints P = {s, s₃} :=
    blue_part_eq_pair_of_doubleBlue ⟨hsB, hs₃B, hss₃, hbad₃card⟩
  have blue_classify {b : Point} (hbB : b ∈ nonordinaryPoints P) :
      b = s ∨ b = s₂ ∨ b = s₃ ∨ b ∈ lineFiber P s a₁ := by
    by_cases hbs : b = s
    · exact Or.inl hbs
    have hbdir : lineFiber P s b ∈ blueDirectionsThrough P s := by
      simp only [blueDirectionsThrough, Finset.mem_image]
      exact ⟨b, Finset.mem_erase.mpr ⟨hbs, hbB⟩, rfl⟩
    rw [hdirs] at hbdir
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbdir
    rcases hbdir with hbdir | hbdir | hbdir
    · have hbpair : b ∈ ({s, s₂} : Finset Point) := by
        rw [← hblue₂]
        exact Finset.mem_inter.mpr
          ⟨hbdir ▸ right_mem_lineFiber (nonordinaryPoints_subset P hbB), hbB⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbpair
      exact hbpair.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
    · have hbpair : b ∈ ({s, s₃} : Finset Point) := by
        rw [← hblue₃]
        exact Finset.mem_inter.mpr
          ⟨hbdir ▸ right_mem_lineFiber (nonordinaryPoints_subset P hbB), hbB⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbpair
      exact hbpair.elim Or.inl (fun h ↦ Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr
        (hbdir ▸ right_mem_lineFiber (nonordinaryPoints_subset P hbB))))
  have no_two_on_L {x y : Point}
      (hxL : x ∈ lineFiber P s a₁) (hyL : y ∈ lineFiber P s a₁)
      (hxy : x ≠ y) (hxline : x ∈ lineFiber P s₂ y) : False := by
    have hyP : y ∈ P := (Finset.mem_filter.mp hyL).1
    have hs₂y : s₂ ≠ y := by
      intro h
      exact hs₂notL (h ▸ hyL)
    have hxyL : lineFiber P x y = lineFiber P s a₁ :=
      lineFiber_eq_of_mem_lineFiber hxy hsa₁ hxL hyL
    have hxy₂ : lineFiber P x y = lineFiber P s₂ y :=
      lineFiber_eq_of_mem_lineFiber hxy hs₂y hxline
        (right_mem_lineFiber hyP)
    apply hs₂notL
    rw [← hxyL, hxy₂]
    exact left_mem_lineFiber hs₂P
  let T : Finset (Finset Point) :=
    {lineFiber P s₂ s, lineFiber P s₂ s₃, lineFiber P s₂ a₂}
  have target_mem : ∀ y : ↑(lineFiber P s a₁),
      lineFiber P s₂ y.1 ∈ T := by
    intro y
    have hyP : y.1 ∈ P := (Finset.mem_filter.mp y.2).1
    have hs₂y : s₂ ≠ y.1 := by
      intro h
      exact hs₂notL (h ▸ y.2)
    have hs₂notA : s₂ ∉ ordinaryPoints P := by
      intro hs₂A
      exact (Finset.disjoint_left.mp
        (disjoint_ordinaryPoints_nonordinaryPoints P)) hs₂A hs₂B
    have hnotPair : lineFiber P s₂ y.1 ≠ {s₂, y.1} := by
      intro heq
      exact hs₂notA ((hred.2.2.2.2.2 s₂ hs₂P y.1 hyP hs₂y).mp heq).1
    have hstrict : ({s₂, y.1} : Finset Point) ⊂ lineFiber P s₂ y.1 :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨pair_subset_lineFiber hs₂P hyP, fun h ↦ hnotPair h.symm⟩
    obtain ⟨x, hxline, hxnot⟩ := Finset.exists_of_ssubset hstrict
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
    have heq_of_mem {u : Point} (hs₂u : s₂ ≠ u)
        (hu : u ∈ lineFiber P s₂ y.1) :
        lineFiber P s₂ y.1 = lineFiber P s₂ u := by
      symm
      exact lineFiber_eq_of_mem_lineFiber hs₂u hs₂y
        (left_mem_lineFiber hs₂P) hu
    by_cases hxA : x ∈ ordinaryPoints P
    · rw [hA] at hxA
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxA
      rcases hxA with hx | hx | hx
      · subst x
        have hs₂a₀ : s₂ ≠ a₀ := by
          intro h
          exact (Finset.disjoint_left.mp
            (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₀A (h ▸ hs₂B)
        have hline₀ : lineFiber P s₂ a₀ = lineFiber P s₂ s := by
          have hs₂s : s₂ ≠ s := hss₂.symm
          exact lineFiber_eq_of_mem_lineFiber hs₂a₀ hs₂s
            (left_mem_lineFiber hs₂P) (by
              rw [lineFiber_swap]
              exact ha₀line)
        simp only [T, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl ((heq_of_mem hs₂a₀ hxline).trans hline₀)
      · subst x
        exact (no_two_on_L
          (right_mem_lineFiber ha₁P) y.2 hxnot.2 hxline).elim
      · subst x
        have hs₂a₂ : s₂ ≠ a₂ := by
          intro h
          exact (Finset.disjoint_left.mp
            (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₂A (h ▸ hs₂B)
        simp only [T, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inr (heq_of_mem hs₂a₂ hxline))
    · have hxB : x ∈ nonordinaryPoints P :=
        Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hxline).1, hxA⟩
      rcases blue_classify hxB with hx | hx | hx | hxL
      · subst x
        simp only [T, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (heq_of_mem hss₂.symm hxline)
      · subst x
        exact (hxnot.1 rfl).elim
      · subst x
        simp only [T, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl (heq_of_mem (by
          intro h
          exact hxnot.1 h.symm) hxline))
      · exact (no_two_on_L hxL y.2 hxnot.2 hxline).elim
  let g : ↑(lineFiber P s a₁) → ↑T :=
    fun y ↦ ⟨lineFiber P s₂ y.1, target_mem y⟩
  have hg : Function.Injective g := by
    intro y y' hyy'
    apply Subtype.ext
    by_contra hyne
    have hy'P : y'.1 ∈ P := (Finset.mem_filter.mp y'.2).1
    have hy'line : y'.1 ∈ lineFiber P s₂ y.1 := by
      have heq : lineFiber P s₂ y.1 = lineFiber P s₂ y'.1 :=
        congrArg (fun z : ↑T ↦ z.1) hyy'
      rw [heq]
      exact right_mem_lineFiber hy'P
    exact no_two_on_L y'.2 y.2 (fun h ↦ hyne h.symm) hy'line
  have hcardT : T.card ≤ 3 := by
    simp only [T]
    exact Finset.card_le_three
  calc
    (lineFiber P s a₁).card ≤ T.card := by
      simpa using Fintype.card_le_of_injective g hg
    _ ≤ 3 := hcardT

/-- Exact primal output of ABKPR Lemma 1 before the final finite
failed-Fano lookup: three directions on `s`, with two distinct double-blue
directions, force a three-red/four-blue complete quadrangle in blue general
position. -/
theorem exists_completeQuadrangle_of_threeDirections_two_double
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    {s s₂ s₃ : Point}
    (hbad₂ : IsDoubleBlueDirection P s s₂)
    (hbad₃ : IsDoubleBlueDirection P s s₃)
    (hdirne : lineFiber P s s₂ ≠ lineFiber P s s₃)
    (hthree : (blueDirectionsThrough P s).card = 3) :
    ∃ a₀ a₁ a₂ s₄,
      ordinaryPoints P = {a₀, a₁, a₂} ∧
      nonordinaryPoints P = {s, s₂, s₃, s₄} ∧
      (nonordinaryPoints P).card = 4 ∧
      BlueGeneralPosition P ∧
      a₀ ∈ lineFiber P s s₂ ∧
      a₁ ∈ lineFiber P s s₄ ∧
      a₂ ∈ lineFiber P s s₃ := by
  classical
  rcases hbad₂ with ⟨hsB, hs₂B, hss₂, hbad₂card⟩
  rcases hbad₃ with ⟨_, hs₃B, hss₃, hbad₃card⟩
  have hAcardEq : (ordinaryPoints P).card = 3 :=
    card_ordinaryPoints_eq_three_of_blueDirections hred hAcard hsB hthree
  obtain ⟨a₀, ha₀, _⟩ := existsUnique_ordinaryPoint_on_doubleBlue hred
    ⟨hsB, hs₂B, hss₂, hbad₂card⟩
  obtain ⟨a₂, ha₂, _⟩ := existsUnique_ordinaryPoint_on_doubleBlue hred
    ⟨hsB, hs₃B, hss₃, hbad₃card⟩
  have hsP := nonordinaryPoints_subset P hsB
  have hsa₀ : s ≠ a₀ := by
    intro h
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₀.1 (h ▸ hsB)
  have ha₀a₂ : a₀ ≠ a₂ := by
    intro h
    subst a₂
    have h₂ : lineFiber P s a₀ = lineFiber P s s₂ :=
      lineFiber_eq_of_mem_lineFiber hsa₀ hss₂
        (left_mem_lineFiber hsP) ha₀.2
    have h₃ : lineFiber P s a₀ = lineFiber P s s₃ :=
      lineFiber_eq_of_mem_lineFiber hsa₀ hss₃
        (left_mem_lineFiber hsP) ha₂.2
    exact hdirne (h₂.symm.trans h₃)
  have ha₂erase : a₂ ∈ (ordinaryPoints P).erase a₀ :=
    Finset.mem_erase.mpr ⟨ha₀a₂.symm, ha₂.1⟩
  have heraseCard : ((ordinaryPoints P).erase a₀).card = 2 := by
    rw [Finset.card_erase_of_mem ha₀.1, hAcardEq]
  obtain ⟨a₁, ha₁erase, ha₁a₂⟩ :=
    Finset.exists_mem_ne (s := (ordinaryPoints P).erase a₀)
      (by rw [heraseCard]; norm_num) a₂
  have ha₁A := (Finset.mem_erase.mp ha₁erase).2
  have ha₀a₁ : a₀ ≠ a₁ := (Finset.mem_erase.mp ha₁erase).1.symm
  have hA : ordinaryPoints P = {a₀, a₁, a₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ha₀.1
      · exact ha₁A
      · exact ha₂.1
    · rw [hAcardEq]
      simp [ha₀a₁, ha₀a₂, ha₁a₂]
  obtain ⟨s₄, hs₄B, hs₄s, ha₁ss₄⟩ :=
    exists_second_nonordinary_on_red_blue_line hred ha₁A hsB
  have hs₄P := nonordinaryPoints_subset P hs₄B
  have hs₄line : s₄ ∈ lineFiber P s a₁ := by
    exact Finset.mem_filter.mpr ⟨hs₄P,
      (collinear3_swap_left a₁ s s₄).mpr ha₁ss₄⟩
  have hsa₁ : s ≠ a₁ := by
    intro h
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A (h ▸ hsB)
  have hss₄ : s ≠ s₄ := hs₄s.symm
  have hs₄dir : lineFiber P s s₄ = lineFiber P s a₁ :=
    lineFiber_eq_of_mem_lineFiber hss₄ hsa₁
      (left_mem_lineFiber hsP) hs₄line
  have hmem₂ : lineFiber P s s₂ ∈ blueDirectionsThrough P s := by
    simp only [blueDirectionsThrough, Finset.mem_image]
    exact ⟨s₂, Finset.mem_erase.mpr ⟨hss₂.symm, hs₂B⟩, rfl⟩
  have hmem₃ : lineFiber P s s₃ ∈ blueDirectionsThrough P s := by
    simp only [blueDirectionsThrough, Finset.mem_image]
    exact ⟨s₃, Finset.mem_erase.mpr ⟨hss₃.symm, hs₃B⟩, rfl⟩
  have hmem₄ : lineFiber P s a₁ ∈ blueDirectionsThrough P s := by
    simp only [blueDirectionsThrough, Finset.mem_image]
    exact ⟨s₄, Finset.mem_erase.mpr ⟨hs₄s, hs₄B⟩, hs₄dir⟩
  have h₂L : lineFiber P s s₂ ≠ lineFiber P s a₁ := by
    intro heq
    have ha₁bad : a₁ ∈ lineFiber P s s₂ := by
      rw [heq]
      exact right_mem_lineFiber (ordinaryPoints_subset P ha₁A)
    have hu := existsUnique_ordinaryPoint_on_doubleBlue hred
      ⟨hsB, hs₂B, hss₂, hbad₂card⟩
    exact ha₀a₁ (hu.unique ha₀ ⟨ha₁A, ha₁bad⟩)
  have h₃L : lineFiber P s s₃ ≠ lineFiber P s a₁ := by
    intro heq
    have ha₁bad : a₁ ∈ lineFiber P s s₃ := by
      rw [heq]
      exact right_mem_lineFiber (ordinaryPoints_subset P ha₁A)
    have hu := existsUnique_ordinaryPoint_on_doubleBlue hred
      ⟨hsB, hs₃B, hss₃, hbad₃card⟩
    exact ha₁a₂ (hu.unique ⟨ha₁A, ha₁bad⟩ ha₂)
  have hdirs : blueDirectionsThrough P s =
      {lineFiber P s s₂, lineFiber P s s₃, lineFiber P s a₁} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hmem₂
      · exact hmem₃
      · exact hmem₄
    · rw [hthree]
      simp [hdirne, h₂L, h₃L]
  have hLcardLe := third_direction_card_le_three hred
    ⟨hsB, hs₂B, hss₂, hbad₂card⟩
    ⟨hsB, hs₃B, hss₃, hbad₃card⟩
    ha₀.1 ha₁A ha₂.1 ha₀a₁ ha₀a₂ ha₁a₂
    hA ha₀.2 ha₂.2 hdirs
  /-
  have hL : lineFiber P s a₁ = {a₁, s, s₄} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have hxP := (Finset.mem_filter.mp hx).1
      by_cases hxA : x ∈ ordinaryPoints P
      · rw [hA] at hxA
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxA ⊢
        rcases hxA with rfl | rfl | rfl
        · have : a₀ = a₁ := by
            apply (existsUnique_ordinaryPoint_on_doubleBlue hred
              ⟨hsB, hs₂B, hss₂, hbad₂card⟩).unique ha₀
            exact ⟨ha₁A, h₂L ▸ hx⟩
          exact (ha₀a₁ this).elim
        · exact Or.inl rfl
        · have : a₂ = a₁ := by
            apply (existsUnique_ordinaryPoint_on_doubleBlue hred
              ⟨hsB, hs₃B, hss₃, hbad₃card⟩).unique ha₂
            exact ⟨ha₁A, h₃L ▸ hx⟩
          exact (ha₁a₂ this.symm).elim
      · have hxB : x ∈ nonordinaryPoints P := Finset.mem_sdiff.mpr ⟨hxP, hxA⟩
        by_cases hxs : x = s
        · exact Or.inr (Or.inl hxs)
        have hxdir : lineFiber P s x ∈ blueDirectionsThrough P s := by
          simp only [blueDirectionsThrough, Finset.mem_image]
          exact ⟨x, Finset.mem_erase.mpr ⟨hxs, hxB⟩, rfl⟩
        rw [hdirs] at hxdir
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxdir
        rcases hxdir with hxdir | hxdir | hxdir
        · have hxpair : x ∈ ({s, s₂} : Finset Point) := by
            rw [← blue_part_eq_pair_of_doubleBlue
              ⟨hsB, hs₂B, hss₂, hbad₂card⟩]
            exact Finset.mem_inter.mpr ⟨hxdir ▸ right_mem_lineFiber hxP, hxB⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
          exact hxpair.elim (fun h ↦ Or.inr (Or.inl h))
            (fun h ↦ (h₂L (hxdir.symm.trans (by
              subst x
              exact lineFiber_eq_of_mem_lineFiber hss₂ hsa₁
                (left_mem_lineFiber hsP) hx))).elim)
        · have hxpair : x ∈ ({s, s₃} : Finset Point) := by
            rw [← blue_part_eq_pair_of_doubleBlue
              ⟨hsB, hs₃B, hss₃, hbad₃card⟩]
            exact Finset.mem_inter.mpr ⟨hxdir ▸ right_mem_lineFiber hxP, hxB⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
          exact hxpair.elim (fun h ↦ Or.inr (Or.inl h))
            (fun h ↦ (h₃L (hxdir.symm.trans (by
              subst x
              exact lineFiber_eq_of_mem_lineFiber hss₃ hsa₁
                (left_mem_lineFiber hsP) hx))).elim)
        · have hxs₄ : x = s₄ := by
            have heq : lineFiber P s x = lineFiber P s s₄ := hxdir.trans hs₄dir.symm
            have hxi : x ∈ lineFiber P s s₄ := by
              rw [← heq]
              exact right_mem_lineFiber hxP
            have hblue := blue_part_eq_pair_of_doubleBlue
              (isDoubleBlueDirection_of_blueGeneralPosition
                (by
                  intro
                  contradiction) hsB hs₄B hss₄)
            -- This branch is on the same direction; its uniqueness follows
            -- from the just established cardinal upper bound below.
            have htri : ({a₁, s, s₄} : Finset Point) ⊆ lineFiber P s a₁ := by
              intro z hz
              simp only [Finset.mem_insert, Finset.mem_singleton] at hz
              rcases hz with rfl | rfl | rfl
              · exact right_mem_lineFiber (ordinaryPoints_subset P ha₁A)
              · exact left_mem_lineFiber hsP
              · exact hs₄line
            have hcardEq : (lineFiber P s a₁).card = 3 := by
              have hge := Finset.card_le_card htri
              have htriCard : ({a₁, s, s₄} : Finset Point).card = 3 := by
                simp [hsa₁.symm, hs₄s, fun h ↦
                  (Finset.disjoint_left.mp
                    (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A (h ▸ hs₄B)]
              rw [htriCard] at hge
              omega
            have hEq := Finset.eq_of_subset_of_card_le htri (by rw [hcardEq]; simp)
            have hxtri : x ∈ ({a₁, s, s₄} : Finset Point) := hEq ▸ hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hxtri
            rcases hxtri with h | h | h
            · exact (Finset.disjoint_left.mp
                (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A (h.symm ▸ hxB) |>.elim
            · exact (hxs h).elim
            · exact h
          exact Or.inr (Or.inr hxs₄)
    · exact hLcardLe
  -/
  have hL : lineFiber P s a₁ = {a₁, s, s₄} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact right_mem_lineFiber (ordinaryPoints_subset P ha₁A)
      · exact left_mem_lineFiber hsP
      · exact hs₄line
    · have ha₁s₄ : a₁ ≠ s₄ := by
        intro h
        exact (Finset.disjoint_left.mp
          (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A (h ▸ hs₄B)
      have htriCard : ({a₁, s, s₄} : Finset Point).card = 3 := by
        simp [hsa₁.symm, hss₄, ha₁s₄]
      rw [htriCard]
      exact hLcardLe
  have hblue₂ : lineFiber P s s₂ ∩ nonordinaryPoints P = {s, s₂} :=
    blue_part_eq_pair_of_doubleBlue
      ⟨hsB, hs₂B, hss₂, hbad₂card⟩
  have hblue₃ : lineFiber P s s₃ ∩ nonordinaryPoints P = {s, s₃} :=
    blue_part_eq_pair_of_doubleBlue
      ⟨hsB, hs₃B, hss₃, hbad₃card⟩
  have hB : nonordinaryPoints P = {s, s₂, s₃, s₄} := by
    apply Finset.Subset.antisymm
    · intro b hbB
      by_cases hbs : b = s
      · simp [hbs]
      have hbP := nonordinaryPoints_subset P hbB
      have hbdir : lineFiber P s b ∈ blueDirectionsThrough P s := by
        simp only [blueDirectionsThrough, Finset.mem_image]
        exact ⟨b, Finset.mem_erase.mpr ⟨hbs, hbB⟩, rfl⟩
      rw [hdirs] at hbdir
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbdir ⊢
      rcases hbdir with hbdir | hbdir | hbdir
      · have hbpair : b ∈ ({s, s₂} : Finset Point) := by
          rw [← hblue₂]
          exact Finset.mem_inter.mpr
            ⟨hbdir ▸ right_mem_lineFiber hbP, hbB⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbpair
        exact hbpair.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
      · have hbpair : b ∈ ({s, s₃} : Finset Point) := by
          rw [← hblue₃]
          exact Finset.mem_inter.mpr
            ⟨hbdir ▸ right_mem_lineFiber hbP, hbB⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbpair
        exact hbpair.elim Or.inl (fun h ↦ Or.inr (Or.inr (Or.inl h)))
      · have hbL : b ∈ lineFiber P s a₁ :=
          hbdir ▸ right_mem_lineFiber hbP
        rw [hL] at hbL
        simp only [Finset.mem_insert, Finset.mem_singleton] at hbL
        rcases hbL with hba₁ | hbs | hbs₄
        · exact ((Finset.disjoint_left.mp
            (disjoint_ordinaryPoints_nonordinaryPoints P)) ha₁A
              (hba₁.symm ▸ hbB)).elim
        · exact Or.inl hbs
        · exact Or.inr (Or.inr (Or.inr hbs₄))
    · intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl
      · exact hsB
      · exact hs₂B
      · exact hs₃B
      · exact hs₄B
  have hs₂s₃ : s₂ ≠ s₃ := by
    intro h
    subst s₃
    exact hdirne rfl
  have hs₂s₄ : s₂ ≠ s₄ := by
    intro h
    subst s₄
    exact h₂L hs₄dir
  have hs₃s₄ : s₃ ≠ s₄ := by
    intro h
    subst s₄
    exact h₃L hs₄dir
  have hn₂₃ : ¬ Collinear3 s s₂ s₃ := by
    intro hcol
    have hs₃line : s₃ ∈ lineFiber P s s₂ :=
      Finset.mem_filter.mpr ⟨nonordinaryPoints_subset P hs₃B, hcol⟩
    have hp : s₃ ∈ ({s, s₂} : Finset Point) := by
      rw [← hblue₂]
      exact Finset.mem_inter.mpr ⟨hs₃line, hs₃B⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact hp.elim (fun h ↦ hss₃ h.symm) (fun h ↦ hs₂s₃ h.symm)
  have hn₂₄ : ¬ Collinear3 s s₂ s₄ := by
    intro hcol
    have hs₄on : s₄ ∈ lineFiber P s s₂ :=
      Finset.mem_filter.mpr ⟨hs₄P, hcol⟩
    have hp : s₄ ∈ ({s, s₂} : Finset Point) := by
      rw [← hblue₂]
      exact Finset.mem_inter.mpr ⟨hs₄on, hs₄B⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact hp.elim (fun h ↦ hss₄ h.symm) (fun h ↦ hs₂s₄ h.symm)
  have hn₃₄ : ¬ Collinear3 s s₃ s₄ := by
    intro hcol
    have hs₄on : s₄ ∈ lineFiber P s s₃ :=
      Finset.mem_filter.mpr ⟨hs₄P, hcol⟩
    have hp : s₄ ∈ ({s, s₃} : Finset Point) := by
      rw [← hblue₃]
      exact Finset.mem_inter.mpr ⟨hs₄on, hs₄B⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact hp.elim (fun h ↦ hss₄ h.symm) (fun h ↦ hs₃s₄ h.symm)
  have hn₂₃₄ : ¬ Collinear3 s₂ s₃ s₄ := by
    intro hcol
    have hsubset : blueDirectionsThrough P s₄ ⊆
        {lineFiber P s₄ s, lineFiber P s₄ s₂} := by
      intro d hd
      simp only [blueDirectionsThrough, Finset.mem_image] at hd
      obtain ⟨b, hbErase, rfl⟩ := hd
      have hb := (Finset.mem_erase.mp hbErase).2
      rw [hB] at hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb ⊢
      rcases hb with hb | hb | hb | hb
      · subst b
        exact Or.inl rfl
      · subst b
        exact Or.inr rfl
      · subst b
        right
        have hs₃on : s₃ ∈ lineFiber P s₄ s₂ := by
          apply Finset.mem_filter.mpr
          refine ⟨nonordinaryPoints_subset P hs₃B, ?_⟩
          unfold Collinear3 orientationDet at hcol ⊢
          nlinarith
        exact lineFiber_eq_of_mem_lineFiber hs₃s₄.symm hs₂s₄.symm
          (left_mem_lineFiber hs₄P) hs₃on
      · subst b
        exact ((Finset.mem_erase.mp hbErase).1 rfl).elim
    have hdirCard : (blueDirectionsThrough P s₄).card ≤ 2 := by
      calc
        (blueDirectionsThrough P s₄).card ≤
            ({lineFiber P s₄ s, lineFiber P s₄ s₂} :
              Finset (Finset Point)).card := Finset.card_le_card hsubset
        _ ≤ 2 := Finset.card_le_two
    have hredCard := card_ordinaryPoints_le_blueDirectionsThrough hred hs₄B
    rw [hAcardEq] at hredCard
    omega
  have hblue₄ : lineFiber P s s₄ ∩ nonordinaryPoints P = {s, s₄} := by
    rw [hs₄dir, hL, hB]
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, hxB⟩
      rcases hx with hx | hx | hx
      · subst x
        have hd := Finset.disjoint_left.mp
          (disjoint_ordinaryPoints_nonordinaryPoints P)
        rcases hxB with h | h | h | h
        · exact (hd ha₁A (h ▸ hsB)).elim
        · exact (hd ha₁A (h ▸ hs₂B)).elim
        · exact (hd ha₁A (h ▸ hs₃B)).elim
        · exact (hd ha₁A (h ▸ hs₄B)).elim
      · exact Or.inl hx
      · exact Or.inr hx
    · intro hx
      rcases hx with hx | hx
      · subst x
        exact ⟨Or.inr (Or.inl rfl), Or.inl rfl⟩
      · subst x
        exact ⟨Or.inr (Or.inr rfl), Or.inr (Or.inr (Or.inr rfl))⟩
  have blue_ne_s {b : Point} (hb : b ∈ nonordinaryPoints P) (hbs : b ≠ s) :
      b = s₂ ∨ b = s₃ ∨ b = s₄ := by
    rw [hB] at hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    exact hb.resolve_left hbs
  have blue_pair {b : Point} (hb : b ∈ nonordinaryPoints P) (hsb : s ≠ b) :
      lineFiber P s b ∩ nonordinaryPoints P = {s, b} := by
    rcases blue_ne_s hb hsb.symm with hb | hb | hb
    · subst b
      exact hblue₂
    · subst b
      exact hblue₃
    · subst b
      exact hblue₄
  have col_swap_right {p q r : Point} (h : Collinear3 p q r) :
      Collinear3 p r q := by
    unfold Collinear3 orientationDet at h ⊢
    nlinarith
  have hgp : BlueGeneralPosition P := by
    intro x hx y hy z hz hxy hxz hyz hcol
    by_cases hxs : x = s
    · subst x
      have hzline : z ∈ lineFiber P s y :=
        Finset.mem_filter.mpr ⟨nonordinaryPoints_subset P hz, hcol⟩
      have hzp : z ∈ ({s, y} : Finset Point) := by
        rw [← blue_pair hy hxy]
        exact Finset.mem_inter.mpr ⟨hzline, hz⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzp
      exact hzp.elim (fun h ↦ hxz h.symm) (fun h ↦ hyz h.symm)
    by_cases hys : y = s
    · subst y
      have hzline : z ∈ lineFiber P s x :=
        Finset.mem_filter.mpr ⟨nonordinaryPoints_subset P hz,
          (collinear3_swap_left x s z).mpr hcol⟩
      have hzp : z ∈ ({s, x} : Finset Point) := by
        rw [← blue_pair hx (fun h ↦ hxs h.symm)]
        exact Finset.mem_inter.mpr ⟨hzline, hz⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzp
      exact hzp.elim (fun h ↦ hyz h.symm) (fun h ↦ hxz h.symm)
    by_cases hzs : z = s
    · subst z
      have hyline : y ∈ lineFiber P s x :=
        Finset.mem_filter.mpr ⟨nonordinaryPoints_subset P hy,
          collinear3_cycle.mp (collinear3_cycle.mp hcol)⟩
      have hyp : y ∈ ({s, x} : Finset Point) := by
        rw [← blue_pair hx (fun h ↦ hxs h.symm)]
        exact Finset.mem_inter.mpr ⟨hyline, hy⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hyp
      exact hyp.elim (fun h ↦ hys h) (fun h ↦ hxy h.symm)
    rcases blue_ne_s hx hxs with hx | hx | hx <;> subst x <;>
      rcases blue_ne_s hy hys with hy | hy | hy <;> subst y <;>
      rcases blue_ne_s hz hzs with hz | hz | hz <;> subst z
    all_goals try contradiction
    all_goals
      apply hn₂₃₄
      first
      | exact hcol
      | exact col_swap_right hcol
      | exact collinear3_cycle.mp hcol
      | exact col_swap_right (collinear3_cycle.mp hcol)
      | exact collinear3_cycle.mp (collinear3_cycle.mp hcol)
      | exact col_swap_right (collinear3_cycle.mp (collinear3_cycle.mp hcol))
  have hBcardEq : (nonordinaryPoints P).card = 4 := by
    rw [hB]
    simp [hss₂, hss₃, hss₄, hs₂s₃, hs₂s₄, hs₃s₄]
  have ha₁line : a₁ ∈ lineFiber P s s₄ := by
    rw [hs₄dir]
    exact right_mem_lineFiber (ordinaryPoints_subset P ha₁A)
  exact ⟨a₀, a₁, a₂, s₄, hA, hB, hBcardEq, hgp, ha₀.2,
    ha₁line, ha₂.2⟩

@[simp] private lemma map_fin7_filter_or_two (e : FailedFanoLabel ↪ Point)
    (i j : FailedFanoLabel) :
    (Finset.univ.filter (fun x ↦ x = i ∨ x = j)).map e = {e i, e j} := by
  classical
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk.elim (fun h ↦ Or.inl (congrArg e h))
      (fun h ↦ Or.inr (congrArg e h))
  · intro hx
    rcases hx with hx | hx
    · exact ⟨i, Or.inl rfl, hx.symm⟩
    · exact ⟨j, Or.inr rfl, hx.symm⟩

@[simp] private lemma map_fin7_filter_or_three (e : FailedFanoLabel ↪ Point)
    (i j k : FailedFanoLabel) :
    (Finset.univ.filter (fun x ↦ x = i ∨ x = j ∨ x = k)).map e =
      {e i, e j, e k} := by
  classical
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rcases hl with hl | hl | hl
    · exact Or.inl (congrArg e hl)
    · exact Or.inr (Or.inl (congrArg e hl))
    · exact Or.inr (Or.inr (congrArg e hl))
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨i, Or.inl rfl, hx.symm⟩
    · exact ⟨j, Or.inr (Or.inl rfl), hx.symm⟩
    · exact ⟨k, Or.inr (Or.inr rfl), hx.symm⟩

/-- The six nonordinary fibers of a complete quadrangle, together with the
reduced red/blue hypotheses, determine all twenty-one fibers of the failed
Fano configuration.  This is the finite incidence-recognition step at the
end of ABKPR Lemma 1, separated from its preceding arrangement count. -/
theorem isFailedFano_of_completeQuadrangle
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (e : FailedFanoLabel ↪ Point)
    (hP : P = Finset.univ.map e)
    (hdiag : ∀ i : FailedFanoLabel, i.1 < 3 → e i ∈ ordinaryPoints P)
    (h34 : lineFiber P (e 3) (e 4) = {e 0, e 3, e 4})
    (h56 : lineFiber P (e 5) (e 6) = {e 0, e 5, e 6})
    (h35 : lineFiber P (e 3) (e 5) = {e 1, e 3, e 5})
    (h46 : lineFiber P (e 4) (e 6) = {e 1, e 4, e 6})
    (h36 : lineFiber P (e 3) (e 6) = {e 2, e 3, e 6})
    (h45 : lineFiber P (e 4) (e 5) = {e 2, e 4, e 5}) :
    IsFailedFano P := by
  classical
  refine ⟨e, hP, ?_⟩
  intro i j hij
  rcases hred with ⟨_, _, _, _, hAA, _⟩
  have hdiagPair (i j : FailedFanoLabel) (hi : i.1 < 3) (hj : j.1 < 3)
      (hij : i ≠ j) : lineFiber P (e i) (e j) = {e i, e j} := by
    exact hAA (e i) (hdiag i hi) (e j) (hdiag j hj) (e.injective.ne hij)
  have htransfer {i j r s : FailedFanoLabel} (hij : i ≠ j) (hrs : r ≠ s)
      (hi : e i ∈ lineFiber P (e r) (e s))
      (hj : e j ∈ lineFiber P (e r) (e s)) :
      lineFiber P (e i) (e j) = lineFiber P (e r) (e s) :=
    lineFiber_eq_of_mem_lineFiber (e.injective.ne hij) (e.injective.ne hrs) hi hj
  fin_cases i <;> fin_cases j
  all_goals try contradiction
  · simpa [failedFanoLine, failedFanoBlocks] using hdiagPair 0 1 (by decide) (by decide) (by decide)
  · simpa [failedFanoLine, failedFanoBlocks] using hdiagPair 0 2 (by decide) (by decide) (by decide)
  · have ht := htransfer (i := (0 : FailedFanoLabel)) (j := 3)
        (r := 3) (s := 4) (by decide) (by decide)
        (by rw [h34]; simp) (by rw [h34]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h34
  · have ht := htransfer (i := (0 : FailedFanoLabel)) (j := 4)
        (r := 3) (s := 4) (by decide) (by decide)
        (by rw [h34]; simp) (by rw [h34]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h34
  · have ht := htransfer (i := (0 : FailedFanoLabel)) (j := 5)
        (r := 5) (s := 6) (by decide) (by decide)
        (by rw [h56]; simp) (by rw [h56]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h56
  · have ht := htransfer (i := (0 : FailedFanoLabel)) (j := 6)
        (r := 5) (s := 6) (by decide) (by decide)
        (by rw [h56]; simp) (by rw [h56]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h56
  · simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using
      hdiagPair 1 0 (by decide) (by decide) (by decide)
  · simpa [failedFanoLine, failedFanoBlocks] using hdiagPair 1 2 (by decide) (by decide) (by decide)
  · have ht := htransfer (i := (1 : FailedFanoLabel)) (j := 3)
        (r := 3) (s := 5) (by decide) (by decide)
        (by rw [h35]; simp) (by rw [h35]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h35
  · have ht := htransfer (i := (1 : FailedFanoLabel)) (j := 4)
        (r := 4) (s := 6) (by decide) (by decide)
        (by rw [h46]; simp) (by rw [h46]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h46
  · have ht := htransfer (i := (1 : FailedFanoLabel)) (j := 5)
        (r := 3) (s := 5) (by decide) (by decide)
        (by rw [h35]; simp) (by rw [h35]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h35
  · have ht := htransfer (i := (1 : FailedFanoLabel)) (j := 6)
        (r := 4) (s := 6) (by decide) (by decide)
        (by rw [h46]; simp) (by rw [h46]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h46
  · simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using
      hdiagPair 2 0 (by decide) (by decide) (by decide)
  · simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using
      hdiagPair 2 1 (by decide) (by decide) (by decide)
  · have ht := htransfer (i := (2 : FailedFanoLabel)) (j := 3)
        (r := 3) (s := 6) (by decide) (by decide)
        (by rw [h36]; simp) (by rw [h36]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h36
  · have ht := htransfer (i := (2 : FailedFanoLabel)) (j := 4)
        (r := 4) (s := 5) (by decide) (by decide)
        (by rw [h45]; simp) (by rw [h45]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h45
  · have ht := htransfer (i := (2 : FailedFanoLabel)) (j := 5)
        (r := 4) (s := 5) (by decide) (by decide)
        (by rw [h45]; simp) (by rw [h45]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h45
  · have ht := htransfer (i := (2 : FailedFanoLabel)) (j := 6)
        (r := 3) (s := 6) (by decide) (by decide)
        (by rw [h36]; simp) (by rw [h36]; simp)
    simpa [failedFanoLine, failedFanoBlocks] using ht.trans h36
  · have ht := htransfer (i := (3 : FailedFanoLabel)) (j := 0)
        (r := 3) (s := 4) (by decide) (by decide)
        (by rw [h34]; simp) (by rw [h34]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h34
  · have ht := htransfer (i := (3 : FailedFanoLabel)) (j := 1)
        (r := 3) (s := 5) (by decide) (by decide)
        (by rw [h35]; simp) (by rw [h35]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h35
  · have ht := htransfer (i := (3 : FailedFanoLabel)) (j := 2)
        (r := 3) (s := 6) (by decide) (by decide)
        (by rw [h36]; simp) (by rw [h36]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h36
  · simpa [failedFanoLine, failedFanoBlocks] using h34
  · simpa [failedFanoLine, failedFanoBlocks] using h35
  · simpa [failedFanoLine, failedFanoBlocks] using h36
  · have ht := htransfer (i := (4 : FailedFanoLabel)) (j := 0)
        (r := 3) (s := 4) (by decide) (by decide)
        (by rw [h34]; simp) (by rw [h34]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h34
  · have ht := htransfer (i := (4 : FailedFanoLabel)) (j := 1)
        (r := 4) (s := 6) (by decide) (by decide)
        (by rw [h46]; simp) (by rw [h46]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h46
  · have ht := htransfer (i := (4 : FailedFanoLabel)) (j := 2)
        (r := 4) (s := 5) (by decide) (by decide)
        (by rw [h45]; simp) (by rw [h45]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h45
  · rw [lineFiber_swap]
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using h34
  · simpa [failedFanoLine, failedFanoBlocks] using h45
  · simpa [failedFanoLine, failedFanoBlocks] using h46
  · have ht := htransfer (i := (5 : FailedFanoLabel)) (j := 0)
        (r := 5) (s := 6) (by decide) (by decide)
        (by rw [h56]; simp) (by rw [h56]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h56
  · have ht := htransfer (i := (5 : FailedFanoLabel)) (j := 1)
        (r := 3) (s := 5) (by decide) (by decide)
        (by rw [h35]; simp) (by rw [h35]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h35
  · have ht := htransfer (i := (5 : FailedFanoLabel)) (j := 2)
        (r := 4) (s := 5) (by decide) (by decide)
        (by rw [h45]; simp) (by rw [h45]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h45
  · rw [lineFiber_swap]
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using h35
  · rw [lineFiber_swap]
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using h45
  · simpa [failedFanoLine, failedFanoBlocks] using h56
  · have ht := htransfer (i := (6 : FailedFanoLabel)) (j := 0)
        (r := 5) (s := 6) (by decide) (by decide)
        (by rw [h56]; simp) (by rw [h56]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h56
  · have ht := htransfer (i := (6 : FailedFanoLabel)) (j := 1)
        (r := 4) (s := 6) (by decide) (by decide)
        (by rw [h46]; simp) (by rw [h46]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h46
  · have ht := htransfer (i := (6 : FailedFanoLabel)) (j := 2)
        (r := 3) (s := 6) (by decide) (by decide)
        (by rw [h36]; simp) (by rw [h36]; simp)
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using ht.trans h36
  · rw [lineFiber_swap]
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using h36
  · rw [lineFiber_swap]
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using h46
  · rw [lineFiber_swap]
    simpa [failedFanoLine, failedFanoBlocks, Finset.pair_comm] using h56

/-- Certificate-oriented form of ABKPR's local recognition exit.  It asks
only for the seven labels, the six double-blue crossings of the resulting
complete quadrangle, and the red incidence at each crossing; the exact
twenty-one failed-Fano fibers are then a theorem. -/
theorem isFailedFano_of_doubleBlue_completeQuadrangle
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (e : FailedFanoLabel ↪ Point)
    (hP : P = Finset.univ.map e)
    (hdiag : ∀ i : FailedFanoLabel, i.1 < 3 → e i ∈ ordinaryPoints P)
    (hbad34 : IsDoubleBlueDirection P (e 3) (e 4))
    (hbad56 : IsDoubleBlueDirection P (e 5) (e 6))
    (hbad35 : IsDoubleBlueDirection P (e 3) (e 5))
    (hbad46 : IsDoubleBlueDirection P (e 4) (e 6))
    (hbad36 : IsDoubleBlueDirection P (e 3) (e 6))
    (hbad45 : IsDoubleBlueDirection P (e 4) (e 5))
    (h0₃₄ : e 0 ∈ lineFiber P (e 3) (e 4))
    (h0₅₆ : e 0 ∈ lineFiber P (e 5) (e 6))
    (h1₃₅ : e 1 ∈ lineFiber P (e 3) (e 5))
    (h1₄₆ : e 1 ∈ lineFiber P (e 4) (e 6))
    (h2₃₆ : e 2 ∈ lineFiber P (e 3) (e 6))
    (h2₄₅ : e 2 ∈ lineFiber P (e 4) (e 5)) :
    IsFailedFano P := by
  apply isFailedFano_of_completeQuadrangle hred e hP hdiag
  · exact lineFiber_eq_triple_of_doubleBlue hred hbad34 (hdiag 0 (by decide)) h0₃₄
  · exact lineFiber_eq_triple_of_doubleBlue hred hbad56 (hdiag 0 (by decide)) h0₅₆
  · exact lineFiber_eq_triple_of_doubleBlue hred hbad35 (hdiag 1 (by decide)) h1₃₅
  · exact lineFiber_eq_triple_of_doubleBlue hred hbad46 (hdiag 1 (by decide)) h1₄₆
  · exact lineFiber_eq_triple_of_doubleBlue hred hbad36 (hdiag 2 (by decide)) h2₃₆
  · exact lineFiber_eq_triple_of_doubleBlue hred hbad45 (hdiag 2 (by decide)) h2₄₅

/-- Four blue points in general position, together with the three red
crossings seen from one blue line, force the complete quadrangle and hence
the failed Fano configuration.  The three opposite red incidences are
derived rather than assumed. -/
theorem isFailedFano_of_four_blue_generalPosition
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (e : FailedFanoLabel ↪ Point)
    (hP : P = Finset.univ.map e)
    (hdiag : ∀ i : FailedFanoLabel, i.1 < 3 → e i ∈ ordinaryPoints P)
    (hbase : ∀ i : FailedFanoLabel, 3 ≤ i.1 → e i ∈ nonordinaryPoints P)
    (hgp : BlueGeneralPosition P)
    (h0₃₄ : e 0 ∈ lineFiber P (e 3) (e 4))
    (h1₃₅ : e 1 ∈ lineFiber P (e 3) (e 5))
    (h2₃₆ : e 2 ∈ lineFiber P (e 3) (e 6)) :
    IsFailedFano P := by
  have hb3 := hbase 3 (by decide)
  have hb4 := hbase 4 (by decide)
  have hb5 := hbase 5 (by decide)
  have hb6 := hbase 6 (by decide)
  have hbad34 := isDoubleBlueDirection_of_blueGeneralPosition hgp hb3 hb4
    (e.injective.ne (by decide))
  have hbad56 := isDoubleBlueDirection_of_blueGeneralPosition hgp hb5 hb6
    (e.injective.ne (by decide))
  have hbad35 := isDoubleBlueDirection_of_blueGeneralPosition hgp hb3 hb5
    (e.injective.ne (by decide))
  have hbad46 := isDoubleBlueDirection_of_blueGeneralPosition hgp hb4 hb6
    (e.injective.ne (by decide))
  have hbad36 := isDoubleBlueDirection_of_blueGeneralPosition hgp hb3 hb6
    (e.injective.ne (by decide))
  have hbad45 := isDoubleBlueDirection_of_blueGeneralPosition hgp hb4 hb5
    (e.injective.ne (by decide))
  have h0₅₆ : e 0 ∈ lineFiber P (e 5) (e 6) := by
    obtain ⟨a, ha, _⟩ := existsUnique_ordinaryPoint_on_doubleBlue hred hbad56
    rcases ordinaryPoint_eq_diagonalLabel e hP hbase ha.1 with rfl | rfl | rfl
    · exact ha.2
    · exfalso
      have h1' : e 1 ∈ lineFiber P (e 5) (e 3) := by
        rw [lineFiber_swap]
        exact h1₃₅
      exact ordinaryPoint_not_on_adjacent_blue_lines hgp (hdiag 1 (by decide))
        hb5 hb3 hb6 (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide)) h1' ha.2
    · exfalso
      have h2' : e 2 ∈ lineFiber P (e 6) (e 3) := by
        rw [lineFiber_swap]
        exact h2₃₆
      have ha' : e 2 ∈ lineFiber P (e 6) (e 5) := by
        rw [lineFiber_swap]
        exact ha.2
      exact ordinaryPoint_not_on_adjacent_blue_lines hgp (hdiag 2 (by decide))
        hb6 hb3 hb5 (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide)) h2' ha'
  have h1₄₆ : e 1 ∈ lineFiber P (e 4) (e 6) := by
    obtain ⟨a, ha, _⟩ := existsUnique_ordinaryPoint_on_doubleBlue hred hbad46
    rcases ordinaryPoint_eq_diagonalLabel e hP hbase ha.1 with rfl | rfl | rfl
    · exfalso
      have h0' : e 0 ∈ lineFiber P (e 4) (e 3) := by
        rw [lineFiber_swap]
        exact h0₃₄
      exact ordinaryPoint_not_on_adjacent_blue_lines hgp (hdiag 0 (by decide))
        hb4 hb3 hb6 (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide)) h0' ha.2
    · exact ha.2
    · exfalso
      have h2' : e 2 ∈ lineFiber P (e 6) (e 3) := by
        rw [lineFiber_swap]
        exact h2₃₆
      have ha' : e 2 ∈ lineFiber P (e 6) (e 4) := by
        rw [lineFiber_swap]
        exact ha.2
      exact ordinaryPoint_not_on_adjacent_blue_lines hgp (hdiag 2 (by decide))
        hb6 hb3 hb4 (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide)) h2' ha'
  have h2₄₅ : e 2 ∈ lineFiber P (e 4) (e 5) := by
    obtain ⟨a, ha, _⟩ := existsUnique_ordinaryPoint_on_doubleBlue hred hbad45
    rcases ordinaryPoint_eq_diagonalLabel e hP hbase ha.1 with rfl | rfl | rfl
    · exfalso
      have h0' : e 0 ∈ lineFiber P (e 4) (e 3) := by
        rw [lineFiber_swap]
        exact h0₃₄
      exact ordinaryPoint_not_on_adjacent_blue_lines hgp (hdiag 0 (by decide))
        hb4 hb3 hb5 (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide)) h0' ha.2
    · exfalso
      have h1' : e 1 ∈ lineFiber P (e 5) (e 3) := by
        rw [lineFiber_swap]
        exact h1₃₅
      have ha' : e 1 ∈ lineFiber P (e 5) (e 4) := by
        rw [lineFiber_swap]
        exact ha.2
      exact ordinaryPoint_not_on_adjacent_blue_lines hgp (hdiag 1 (by decide))
        hb5 hb3 hb4 (e.injective.ne (by decide)) (e.injective.ne (by decide))
        (e.injective.ne (by decide)) h1' ha'
    · exact ha.2
  exact isFailedFano_of_doubleBlue_completeQuadrangle hred e hP hdiag
    hbad34 hbad56 hbad35 hbad46 hbad36 hbad45
    h0₃₄ h0₅₆ h1₃₅ h1₄₆ h2₃₆ h2₄₅

/-- ABKPR Lemma 1, in the concrete projective-incidence interface used by
the discharging argument.  The witnesses `s₂,s₃` name two distinct
double-blue vertices among the exactly three vertices on the blue dual line
of `s`. -/
theorem isFailedFano_of_threeDirections_two_double
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    {s s₂ s₃ : Point}
    (hbad₂ : IsDoubleBlueDirection P s s₂)
    (hbad₃ : IsDoubleBlueDirection P s s₃)
    (hdirne : lineFiber P s s₂ ≠ lineFiber P s s₃)
    (hthree : (blueDirectionsThrough P s).card = 3) :
    IsFailedFano P := by
  classical
  obtain ⟨a₀, a₁, a₂, s₄, hA, hB, hBcard, hgp,
      ha₀, ha₁, ha₂⟩ :=
    exists_completeQuadrangle_of_threeDirections_two_double
      hred hAcard hbad₂ hbad₃ hdirne hthree
  have hAcardEq : (ordinaryPoints P).card = 3 := by
    rw [hA] at hAcard ⊢
    exact Nat.le_antisymm Finset.card_le_three hAcard
  have ha₀a₁ : a₀ ≠ a₁ := by
    intro h
    subst a₁
    have hle : (ordinaryPoints P).card ≤ 2 := by
      rw [hA]
      simpa using (Finset.card_le_two (a := a₀) (b := a₂))
    omega
  have ha₀a₂ : a₀ ≠ a₂ := by
    intro h
    subst a₂
    have hle : (ordinaryPoints P).card ≤ 2 := by
      rw [hA]
      simpa using (Finset.card_le_two (a := a₁) (b := a₀))
    omega
  have ha₁a₂ : a₁ ≠ a₂ := by
    intro h
    subst a₂
    have hle : (ordinaryPoints P).card ≤ 2 := by
      rw [hA]
      simpa using (Finset.card_le_two (a := a₀) (b := a₁))
    omega
  have hsB : s ∈ nonordinaryPoints P := by rw [hB]; simp
  have hs₂B : s₂ ∈ nonordinaryPoints P := by rw [hB]; simp
  have hs₃B : s₃ ∈ nonordinaryPoints P := by rw [hB]; simp
  have hs₄B : s₄ ∈ nonordinaryPoints P := by rw [hB]; simp
  have hss₂ : s ≠ s₂ := hbad₂.2.2.1
  have hss₃ : s ≠ s₃ := hbad₃.2.2.1
  have hs₂s₃ : s₂ ≠ s₃ := by
    intro h
    subst s₃
    exact hdirne rfl
  have hss₄ : s ≠ s₄ := by
    intro h
    subst s₄
    have hle : (nonordinaryPoints P).card ≤ 3 := by
      rw [hB]
      simpa using (Finset.card_le_three (a := s₂) (b := s₃) (c := s))
    omega
  have hs₂s₄ : s₂ ≠ s₄ := by
    intro h
    subst s₄
    have hle : (nonordinaryPoints P).card ≤ 3 := by
      rw [hB]
      simpa using
        (Finset.card_le_three (a := s) (b := s₃) (c := s₂))
    omega
  have hs₃s₄ : s₃ ≠ s₄ := by
    intro h
    subst s₄
    have hle : (nonordinaryPoints P).card ≤ 3 := by
      rw [hB]
      simpa using (Finset.card_le_three (a := s) (b := s₂) (c := s₃))
    omega
  have hdisj := Finset.disjoint_left.mp
    (disjoint_ordinaryPoints_nonordinaryPoints P)
  have ha₀A : a₀ ∈ ordinaryPoints P := by rw [hA]; simp
  have ha₁A : a₁ ∈ ordinaryPoints P := by rw [hA]; simp
  have ha₂A : a₂ ∈ ordinaryPoints P := by rw [hA]; simp
  have hcrosses :
      a₀ ≠ s ∧ a₀ ≠ s₂ ∧ a₀ ≠ s₃ ∧ a₀ ≠ s₄ ∧
      a₁ ≠ s ∧ a₁ ≠ s₂ ∧ a₁ ≠ s₃ ∧ a₁ ≠ s₄ ∧
      a₂ ≠ s ∧ a₂ ≠ s₂ ∧ a₂ ≠ s₃ ∧ a₂ ≠ s₄ := by
    repeat' apply And.intro
    all_goals
      intro h
      first
      | exact hdisj ha₀A (h ▸ hsB)
      | exact hdisj ha₀A (h ▸ hs₂B)
      | exact hdisj ha₀A (h ▸ hs₃B)
      | exact hdisj ha₀A (h ▸ hs₄B)
      | exact hdisj ha₁A (h ▸ hsB)
      | exact hdisj ha₁A (h ▸ hs₂B)
      | exact hdisj ha₁A (h ▸ hs₃B)
      | exact hdisj ha₁A (h ▸ hs₄B)
      | exact hdisj ha₂A (h ▸ hsB)
      | exact hdisj ha₂A (h ▸ hs₂B)
      | exact hdisj ha₂A (h ▸ hs₃B)
      | exact hdisj ha₂A (h ▸ hs₄B)
  let eFun : FailedFanoLabel → Point := ![a₀, a₂, a₁, s, s₂, s₃, s₄]
  have eFunInj : Function.Injective eFun := by
    intro i j hij
    rcases hcrosses with ⟨ha₀s, ha₀s₂, ha₀s₃, ha₀s₄,
      ha₁s, ha₁s₂, ha₁s₃, ha₁s₄,
      ha₂s, ha₂s₂, ha₂s₃, ha₂s₄⟩
    fin_cases i <;> fin_cases j <;> simp_all [eFun]
  let e : FailedFanoLabel ↪ Point := ⟨eFun, eFunInj⟩
  have e0 : e 0 = a₀ := rfl
  have e1 : e 1 = a₂ := rfl
  have e2 : e 2 = a₁ := rfl
  have e3 : e 3 = s := rfl
  have e4 : e 4 = s₂ := rfl
  have e5 : e 5 = s₃ := rfl
  have e6 : e 6 = s₄ := rfl
  have hP : P = Finset.univ.map e := by
    rw [← ordinaryPoints_union_nonordinaryPoints P, hA, hB]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rcases hx with hx | hx
      · rcases hx with hx | hx | hx
        · refine ⟨0, ?_⟩; change a₀ = x; exact hx.symm
        · refine ⟨2, ?_⟩; change a₁ = x; exact hx.symm
        · refine ⟨1, ?_⟩; change a₂ = x; exact hx.symm
      · rcases hx with hx | hx | hx | hx
        · refine ⟨3, ?_⟩; change s = x; exact hx.symm
        · refine ⟨4, ?_⟩; change s₂ = x; exact hx.symm
        · refine ⟨5, ?_⟩; change s₃ = x; exact hx.symm
        · refine ⟨6, ?_⟩; change s₄ = x; exact hx.symm
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [e, eFun]
  have hdiag : ∀ i : FailedFanoLabel, i.1 < 3 →
      e i ∈ ordinaryPoints P := by
    intro i hi
    fin_cases i
    · change a₀ ∈ ordinaryPoints P; exact ha₀A
    · change a₂ ∈ ordinaryPoints P; exact ha₂A
    · change a₁ ∈ ordinaryPoints P; exact ha₁A
    all_goals norm_num at hi
  have hbase : ∀ i : FailedFanoLabel, 3 ≤ i.1 →
      e i ∈ nonordinaryPoints P := by
    intro i hi
    fin_cases i
    all_goals try norm_num at hi
    · change s ∈ nonordinaryPoints P; exact hsB
    · change s₂ ∈ nonordinaryPoints P; exact hs₂B
    · change s₃ ∈ nonordinaryPoints P; exact hs₃B
    · change s₄ ∈ nonordinaryPoints P; exact hs₄B
  apply isFailedFano_of_four_blue_generalPosition hred e hP hdiag hbase hgp
  · simpa only [e0, e3, e4] using ha₀
  · simpa only [e1, e3, e5] using ha₂
  · simpa only [e2, e3, e6] using ha₁

end

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

/-- The four configurations listed in the resolution all have positive equal
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

/-- A configuration with fewer than two points is in general position. -/
theorem inGeneralPosition_of_card_lt_two {P : Finset Point}
    (hcard : P.card < 2) : InGeneralPosition P := by
  intro p hp q hq hpq
  exfalso
  have hle : P.card ≤ 1 := by omega
  exact hpq ((Finset.card_le_one.mp hle) p hp q hq)

/-- The constructive classification direction, including the vacuous empty
and singleton configurations. -/
theorem isMagic_of_classified_all {P : Finset Point}
    (h : IsCollinearConfig P ∨ InGeneralPosition P ∨
      IsNearPencil P ∨ IsFailedFano P) : IsMagic P := by
  by_cases hcard : 2 ≤ P.card
  · exact isMagic_of_classified hcard h
  · exact isMagic_of_inGeneralPosition
      (inGeneralPosition_of_card_lt_two (by omega))

/-- Once the reduced red--blue core is proved, the forward classification
holds for every finite configuration, including cardinalities zero and one. -/
theorem classified_of_magic_of_reduced_core_all
    (reducedCore : ∀ {P : Finset Point} {w : Point → ℝ} {c : ℝ},
      3 ≤ (ordinaryPoints P).card → (nonordinaryPoints P).Nonempty →
        IsReducedMagic P w c → IsFailedFano P)
    {P : Finset Point} (hmagic : IsMagic P) :
    IsCollinearConfig P ∨ InGeneralPosition P ∨
      IsNearPencil P ∨ IsFailedFano P := by
  by_cases hcard : 2 ≤ P.card
  · exact classified_of_magic_of_reduced_core reducedCore hcard hmagic
  · exact Or.inr (Or.inl (inGeneralPosition_of_card_lt_two (by omega)))

end

end Erdos735
