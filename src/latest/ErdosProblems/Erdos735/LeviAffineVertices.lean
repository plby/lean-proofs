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

import ErdosProblems.Erdos735.LeviAffineChart
import ErdosProblems.Erdos735.LeviConvexCore
import ErdosProblems.Erdos957.HullEdge

/-!
# Finite affine vertices after selecting a projective line at infinity

This file gives an explicit finite set of the crossings of the affine lines

`1 + (q-p) · u = 0`

obtained after the dual line of `p` is sent to infinity.  Parallel pairs are
discarded.  The intersection formula and its incidence equations are proved
directly, so later convex-hull arguments do not depend on a topological line
arrangement API.
-/

open scoped Matrix

namespace Erdos735.LeviAffineVertices

noncomputable section

open LeviAffineChart

abbrev Point := ProjectiveArrangement.Point

/-- The determinant of two affine direction covectors. -/
def det2 (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

theorem det2_swap (u v : Point) : det2 v u = -det2 u v := by
  simp [det2]
  ring

/-- The coefficient covector of the affine dual line of `q` after selecting
the dual line of `p` as infinity. -/
def coeff (p q : Point) : Point := q - p

@[simp] theorem coeff_apply (p q : Point) (i : Fin 2) :
    coeff p q i = q i - p i := by
  rfl

theorem coeff_ne_zero {p q : Point} (hpq : p ≠ q) : coeff p q ≠ 0 := by
  intro hzero
  apply hpq
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z : Point ↦ z i) hzero
  simp [coeff] at hi
  linarith

theorem coeff_injective (p : Point) : Function.Injective (coeff p) := by
  intro q r hqr
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z : Point ↦ z i) hqr
  simp [coeff] at hi
  linarith

/-- Affine nonparallelity of the two lines obtained from `q` and `r`. -/
def Nonparallel (p q r : Point) : Prop := det2 (coeff p q) (coeff p r) ≠ 0

theorem nonparallel_iff_not_collinear (p q r : Point) :
    Nonparallel p q r ↔
      ¬ ProjectiveDuality.Collinear3 p q r := by
  simp only [Nonparallel, ProjectiveDuality.Collinear3]
  have hdet : det2 (coeff p q) (coeff p r) =
      ProjectiveDuality.orientationDet p q r := by
    simp [det2, coeff, ProjectiveDuality.orientationDet]
  rw [hdet]

/-- The crossing of two nonparallel affine dual lines. -/
def crossing (p q r : Point) (hqr : Nonparallel p q r) : Point :=
  let d := coeff p q
  let e := coeff p r
  let D := det2 d e
  WithLp.toLp 2 ![((d 1 - e 1) / D), ((e 0 - d 0) / D)]

@[simp] theorem crossing_apply_zero (p q r : Point) (hqr : Nonparallel p q r) :
    crossing p q r hqr 0 =
      ((coeff p q) 1 - (coeff p r) 1) /
        det2 (coeff p q) (coeff p r) := by
  simp [crossing]

@[simp] theorem crossing_apply_one (p q r : Point) (hqr : Nonparallel p q r) :
    crossing p q r hqr 1 =
      ((coeff p r) 0 - (coeff p q) 0) /
        det2 (coeff p q) (coeff p r) := by
  simp [crossing]

theorem lineEval_crossing_left (p q r : Point) (hqr : Nonparallel p q r) :
    lineEval p q (crossing p q r hqr) = 0 := by
  have hD : det2 (coeff p q) (coeff p r) ≠ 0 := hqr
  simp [lineEval, crossing_apply_zero, crossing_apply_one, coeff_apply]
  field_simp [hD]
  simp [det2, coeff]
  ring

theorem lineEval_crossing_right (p q r : Point) (hqr : Nonparallel p q r) :
    lineEval p r (crossing p q r hqr) = 0 := by
  have hD : det2 (coeff p q) (coeff p r) ≠ 0 := hqr
  simp [lineEval, crossing_apply_zero, crossing_apply_one, coeff_apply]
  field_simp [hD]
  simp [det2, coeff]
  ring

theorem crossing_swap (p q r : Point) (hqr : Nonparallel p q r)
    (hrq : Nonparallel p r q) :
    crossing p r q hrq = crossing p q r hqr := by
  apply PiLp.ext
  intro i
  fin_cases i
  · change crossing p r q hrq (0 : Fin 2) = crossing p q r hqr 0
    rw [crossing_apply_zero, crossing_apply_zero, det2_swap]
    field_simp [hqr]
    ring
  · change crossing p r q hrq (1 : Fin 2) = crossing p q r hqr 1
    rw [crossing_apply_one, crossing_apply_one, det2_swap]
    field_simp [hqr]
    ring

/-- Two nonparallel affine line equations have at most one common zero. -/
theorem eq_of_lineEval_eq_zero_of_nonparallel
    {p q r x y : Point} (hqr : Nonparallel p q r)
    (hxq : lineEval p q x = 0) (hxr : lineEval p r x = 0)
    (hyq : lineEval p q y = 0) (hyr : lineEval p r y = 0) :
    x = y := by
  have hq :
      coeff p q 0 * (x 0 - y 0) + coeff p q 1 * (x 1 - y 1) = 0 := by
    simp [lineEval, coeff] at hxq hyq ⊢
    linarith
  have hr :
      coeff p r 0 * (x 0 - y 0) + coeff p r 1 * (x 1 - y 1) = 0 := by
    simp [lineEval, coeff] at hxr hyr ⊢
    linarith
  have hdet : det2 (coeff p q) (coeff p r) ≠ 0 := hqr
  have hx₀ : x 0 - y 0 = 0 := by
    have hprod :
        det2 (coeff p q) (coeff p r) * (x 0 - y 0) = 0 := by
      dsimp [det2]
      linear_combination coeff p r 1 * hq - coeff p q 1 * hr
    exact (mul_eq_zero.mp hprod).resolve_left hdet
  have hx₁ : x 1 - y 1 = 0 := by
    have hprod :
        det2 (coeff p q) (coeff p r) * (x 1 - y 1) = 0 := by
      dsimp [det2]
      linear_combination -(coeff p r 0) * hq + coeff p q 0 * hr
    exact (mul_eq_zero.mp hprod).resolve_left hdet
  apply PiLp.ext
  intro i
  fin_cases i
  · exact sub_eq_zero.mp hx₀
  · exact sub_eq_zero.mp hx₁

theorem crossing_eq_of_lineEval_eq_zero
    {p q r x : Point} (hqr : Nonparallel p q r)
    (hxq : lineEval p q x = 0) (hxr : lineEval p r x = 0) :
    crossing p q r hqr = x := by
  exact eq_of_lineEval_eq_zero_of_nonparallel hqr
    (lineEval_crossing_left p q r hqr)
    (lineEval_crossing_right p q r hqr) hxq hxr

section FiniteConfiguration

variable (B : Finset Point)

/-- The affine lines other than the selected projective line. -/
abbrev OtherPoint (p : B) := {q : B // q ≠ p}

/-- Ordered nonparallel pairs of affine lines. -/
abbrev CrossingPair (p : B) :=
  {qr : OtherPoint B p × OtherPoint B p //
    Nonparallel p.1 qr.1.1 qr.2.1}

/-- The crossing represented by an ordered nonparallel pair. -/
def indexedCrossing (p : B) (qr : CrossingPair B p) : Point :=
  crossing p.1 qr.1.1.1 qr.1.2.1 qr.2

/-- The finite set of distinct affine crossings after the line of `p` is
sent to infinity.  Multiple concurrent pairs are identified. -/
def vertexFinset (p : B) : Finset Point := by
  classical
  exact Finset.univ.image (indexedCrossing B p)

@[simp] theorem mem_vertexFinset (p : B) (v : Point) :
    v ∈ vertexFinset B p ↔ ∃ qr : CrossingPair B p,
      indexedCrossing B p qr = v := by
  classical
  constructor
  · intro hv
    obtain ⟨qr, -, hqr⟩ := Finset.mem_image.mp hv
    exact ⟨qr, hqr⟩
  · rintro ⟨qr, rfl⟩
    exact Finset.mem_image.mpr ⟨qr, Finset.mem_univ _, rfl⟩

theorem indexedCrossing_mem (p : B) (qr : CrossingPair B p) :
    indexedCrossing B p qr ∈ vertexFinset B p := by
  simp

theorem indexedCrossing_on_left (p : B) (qr : CrossingPair B p) :
    lineEval p.1 qr.1.1.1 (indexedCrossing B p qr) = 0 := by
  exact lineEval_crossing_left _ _ _ _

theorem indexedCrossing_on_right (p : B) (qr : CrossingPair B p) :
    lineEval p.1 qr.1.2.1 (indexedCrossing B p qr) = 0 := by
  exact lineEval_crossing_right _ _ _ _

/-- A concrete noncollinear triple through `p` produces an affine crossing. -/
theorem vertexFinset_nonempty_of_noncollinear
    (p q r : B) (hpq : p ≠ q) (hpr : p ≠ r)
    (hncol : ¬ ProjectiveDuality.Collinear3 p.1 q.1 r.1) :
    (vertexFinset B p).Nonempty := by
  let oq : OtherPoint B p := ⟨q, hpq.symm⟩
  let or : OtherPoint B p := ⟨r, hpr.symm⟩
  have hpar : Nonparallel p.1 q.1 r.1 :=
    (nonparallel_iff_not_collinear _ _ _).2 hncol
  let qr : CrossingPair B p := ⟨(oq, or), hpar⟩
  exact ⟨indexedCrossing B p qr, indexedCrossing_mem B p qr⟩

/-- A genuinely two-dimensional affine crossing set has at least three
vertices on its convex hull. -/
theorem three_le_hullVertexCount_of_affineSpan_eq_top (p : B)
    (hspan : affineSpan ℝ (vertexFinset B p : Set Point) = ⊤) :
    3 ≤ Erdos957.hullVertexCount (vertexFinset B p) := by
  have h := LeviConvexCore.finrank_add_one_le_card_extremePoints
    (vertexFinset B p).finite_toSet hspan
  have hfinrank : Module.finrank ℝ Point = 2 := by simp
  rw [hfinrank] at h
  norm_num at h
  let X : Set Point :=
    (convexHull ℝ (vertexFinset B p : Set Point)).extremePoints ℝ
  have hXfin : X.Finite := (vertexFinset B p).finite_toSet.subset (by
    dsimp [X]
    exact extremePoints_convexHull_subset)
  letI : Fintype X := hXfin.fintype
  change 3 ≤ X.ncard at h
  have hXcard : X.ncard = Erdos957.hullVertexCount (vertexFinset B p) := by
    rw [Set.ncard_eq_toFinset_card']
    apply congrArg Finset.card
    ext x
    simp only [Set.mem_toFinset, Erdos957.mem_hullVertices, X]
  rwa [hXcard] at h

/-- The checked gift-wrapping cycle of the affine crossing hull in the
noncollinear case. -/
noncomputable def vertexHullOrder (p : B)
    (hspan : affineSpan ℝ (vertexFinset B p : Set Point) = ⊤) :
    Erdos957.CyclicHullOrder (vertexFinset B p) :=
  Erdos957.cyclicHullOrderOfThree _
    (three_le_hullVertexCount_of_affineSpan_eq_top B p hspan)

end FiniteConfiguration

end

end Erdos735.LeviAffineVertices
