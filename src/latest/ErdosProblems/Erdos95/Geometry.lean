/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.ElekesSharir

/-!
# Elementary geometry for the Elekes--Sharir line family

This file proves the plane non-clustering estimate in coordinates: a proper
affine plane contains at most one line `L(p,q)` for each fixed first endpoint
`p`, and hence at most `|P|` lines indexed by `P × P`.
-/

namespace Erdos95.ES

/-! ## The ruling vector fields -/

/-- Direction of the normalized line `L(p,q)`. -/
noncomputable def lineDirection (p q : PlanePoint) : Space3 :=
  ![(q 1 - p 1) / 2, (p 0 - q 0) / 2, 1]

/-- Guth's polynomial vector field for the two-parameter family
`{L(p,q) | q ∈ ℝ²}`.  At every point it is a nonzero multiple of the
direction of the unique member of this family through that point. -/
noncomputable def rulingVectorField (p : PlanePoint) (x : Space3) : Space3 :=
  ![x 2 * x 0 + x 1 - x 2 * p 0 - p 1,
    p 0 - x 0 - x 2 * p 1 + x 2 * x 1,
    1 + (x 2) ^ 2]

/-- On `L(p,q)`, the ruling vector field is `(1+t²)` times the normalized
line direction. -/
theorem rulingVectorField_linePoint (p q : PlanePoint) (t : ℝ) :
    rulingVectorField p (linePoint p q t) =
      (1 + t ^ 2) • lineDirection p q := by
  funext i
  fin_cases i <;> simp [rulingVectorField, linePoint, lineDirection] <;> ring

/-- The ruling field never vanishes; its third coordinate is strictly
positive. -/
theorem rulingVectorField_ne_zero (p : PlanePoint) (x : Space3) :
    rulingVectorField p x ≠ 0 := by
  intro h
  have hthird := congrFun h (2 : Fin 3)
  simp [rulingVectorField] at hthird
  nlinarith [sq_nonneg (x 2)]

/-- The unique second endpoint `q` such that the ruling line `L(p,q)` passes
through `x`.  The denominator is `1+x₂²`, hence is never zero. -/
noncomputable def secondIndexThrough (p : PlanePoint) (x : Space3) : PlanePoint :=
  let d := 1 + (x 2) ^ 2
  WithLp.toLp 2 ![((2 * x 0 - p 0 + x 2 * p 1) -
      x 2 * (2 * x 1 - p 1 - x 2 * p 0)) / d,
    (x 2 * (2 * x 0 - p 0 + x 2 * p 1) +
      (2 * x 1 - p 1 - x 2 * p 0)) / d]

private theorem one_add_sq_ne_zero (z : ℝ) : 1 + z ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg z]

/-- Every point of three-space lies on the ruling line indexed by
`(p, secondIndexThrough p x)`. -/
theorem linePoint_secondIndexThrough (p : PlanePoint) (x : Space3) :
    linePoint p (secondIndexThrough p x) (x 2) = x := by
  funext i
  fin_cases i
  · simp [linePoint, secondIndexThrough]
    field_simp [one_add_sq_ne_zero (x 2)]
    ring
  · simp [linePoint, secondIndexThrough]
    field_simp [one_add_sq_ne_zero (x 2)]
    ring
  · simp [linePoint]

theorem onLine_secondIndexThrough (p : PlanePoint) (x : Space3) :
    OnLine p (secondIndexThrough p x) x := by
  exact ⟨x 2, (linePoint_secondIndexThrough p x).symm⟩

/-- For a fixed first endpoint, the member of the ruling through a point is
unique. -/
theorem eq_secondIndexThrough_of_onLine {p q : PlanePoint} {x : Space3}
    (hx : OnLine p q x) : q = secondIndexThrough p x := by
  have hint : Intersects p q p (secondIndexThrough p x) :=
    ⟨x, hx, onLine_secondIndexThrough p x⟩
  have hdist := sqDist_eq_of_intersects hint
  simp only [sqDist, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0),
    zero_add] at hdist
  have h0 : q 0 - secondIndexThrough p x 0 = 0 := by
    nlinarith [sq_nonneg (q 0 - secondIndexThrough p x 0),
      sq_nonneg (q 1 - secondIndexThrough p x 1)]
  have h1 : q 1 - secondIndexThrough p x 1 = 0 := by
    nlinarith [sq_nonneg (q 0 - secondIndexThrough p x 0),
      sq_nonneg (q 1 - secondIndexThrough p x 1)]
  apply PiLp.ext
  intro i
  fin_cases i
  · exact sub_eq_zero.mp h0
  · exact sub_eq_zero.mp h1

/-- The affine-linear functional with the given normal vector. -/
noncomputable def planeValue (normal x : Space3) : ℝ :=
  normal 0 * x 0 + normal 1 * x 1 + normal 2 * x 2

/-- The whole Elekes--Sharir line `L(p,q)` lies in the affine plane with
equation `normal ⋅ x = offset`. -/
def LineInAffinePlane (normal : Space3) (offset : ℝ)
    (p q : PlanePoint) : Prop :=
  ∀ t : ℝ, planeValue normal (linePoint p q t) = offset

/-- For a proper affine plane and a fixed first endpoint `p`, at most one
member of the ruling-like family `q ↦ L(p,q)` lies in the plane. -/
theorem eq_of_same_first_of_lines_in_affinePlane
    {normal : Space3} {offset : ℝ} (hnormal : normal ≠ 0)
    {p q r : PlanePoint}
    (hq : LineInAffinePlane normal offset p q)
    (hr : LineInAffinePlane normal offset p r) : q = r := by
  have hq0 := hq 0
  have hq1 := hq 1
  have hr0 := hr 0
  have hr1 := hr 1
  simp [planeValue, linePoint] at hq0 hq1 hr0 hr1
  have hbase :
      normal 0 * (q 0 - r 0) + normal 1 * (q 1 - r 1) = 0 := by
    linarith
  have hdir :
      normal 0 * (q 1 - r 1) - normal 1 * (q 0 - r 0) = 0 := by
    linarith
  have hslope :
      normal 0 * (q 1 - p 1) + normal 1 * (p 0 - q 0) + 2 * normal 2 = 0 := by
    linarith
  have hnorm : 0 < normal 0 ^ 2 + normal 1 ^ 2 := by
    by_contra h
    have hz : normal 0 ^ 2 + normal 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (normal 0), sq_nonneg (normal 1)]
    have hn0 : normal 0 = 0 := by nlinarith [sq_nonneg (normal 1)]
    have hn1 : normal 1 = 0 := by nlinarith [sq_nonneg (normal 0)]
    have hn2 : normal 2 = 0 := by
      rw [hn0, hn1] at hslope
      linarith
    apply hnormal
    funext i
    fin_cases i
    · exact hn0
    · exact hn1
    · exact hn2
  have hxprod :
      (normal 0 ^ 2 + normal 1 ^ 2) * (q 0 - r 0) = 0 := by
    linear_combination normal 0 * hbase - normal 1 * hdir
  have hyprod :
      (normal 0 ^ 2 + normal 1 ^ 2) * (q 1 - r 1) = 0 := by
    linear_combination normal 1 * hbase + normal 0 * hdir
  have hx : q 0 = r 0 := by
    have hne : normal 0 ^ 2 + normal 1 ^ 2 ≠ 0 := hnorm.ne'
    exact sub_eq_zero.mp (mul_eq_zero.mp hxprod |>.resolve_left hne)
  have hy : q 1 = r 1 := by
    have hne : normal 0 ^ 2 + normal 1 ^ 2 ≠ 0 := hnorm.ne'
    exact sub_eq_zero.mp (mul_eq_zero.mp hyprod |>.resolve_left hne)
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hx
  · exact hy

/-- The indexed lines from `P × P` which lie in a specified affine plane. -/
noncomputable def lineIndicesInAffinePlane (P : Finset PlanePoint)
    (normal : Space3) (offset : ℝ) : Finset (PlanePoint × PlanePoint) := by
  classical
  exact (P.product P).filter fun pq => LineInAffinePlane normal offset pq.1 pq.2

/-- The Elekes--Sharir family has at most `|P|` lines in every proper affine
plane. -/
theorem card_lineIndicesInAffinePlane_le (P : Finset PlanePoint)
    {normal : Space3} {offset : ℝ} (hnormal : normal ≠ 0) :
    (lineIndicesInAffinePlane P normal offset).card ≤ P.card := by
  classical
  let S := lineIndicesInAffinePlane P normal offset
  have hinj : Set.InjOn Prod.fst (S : Set (PlanePoint × PlanePoint)) := by
    intro a ha b hb hab
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    apply Prod.ext hab
    exact eq_of_same_first_of_lines_in_affinePlane hnormal ha'.2 (hab ▸ hb'.2)
  have hcard : (S.image Prod.fst).card = S.card := Finset.card_image_iff.mpr hinj
  have hsub : S.image Prod.fst ⊆ P := by
    intro p hp
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hpq).1).1
  calc
    S.card = (S.image Prod.fst).card := hcard.symm
    _ ≤ P.card := Finset.card_le_card hsub

end Erdos95.ES
