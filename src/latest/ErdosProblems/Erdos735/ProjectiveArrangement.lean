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

import ErdosProblems.Erdos735.ProjectiveDuality
import ErdosProblems.Erdos735.ChartOrder
import ErdosProblems.Erdos735.SignVectorArrangement

/-!
# Concrete normals for the dual arrangement in Problem 735

This file connects the affine point model used in the main theorem with the
`Fin 3 → ℝ` normals used by the sign-vector, great-circle, and rotation-system
developments.  In particular, a noncollinear affine triple gives three
linearly independent normalized normals, and hence any finite configuration
containing that triple has full homogeneous span.
-/

open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.ProjectiveArrangement

noncomputable section

/-- The concrete affine plane used by the main Problem 735 development. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The three-dimensional normal to the projective line dual to `p`. -/
def normalVec (p : Point) : SignVector.Vec3 := ![p 0, p 1, 1]

lemma normalVec_eq_toCoordinates_embed (p : Point) :
    normalVec p = ProjectiveDuality.toCoordinates (ProjectiveDuality.embed p) := by
  funext i
  fin_cases i <;> simp [normalVec, ProjectiveDuality.toCoordinates,
    ProjectiveDuality.embed]

lemma normalVec_ne_zero (p : Point) : normalVec p ≠ 0 := by
  intro hzero
  have h := congrFun hzero (2 : Fin 3)
  change (1 : ℝ) = 0 at h
  norm_num at h

lemma normalVec_injective : Function.Injective normalVec := by
  intro p q hpq
  apply PiLp.ext
  intro i
  fin_cases i
  · exact congrFun hpq 0
  · exact congrFun hpq 1

lemma distinct_point_iff_distinct_normalVec (p q : Point) :
    p ≠ q ↔ normalVec p ≠ normalVec q := by
  constructor
  · intro hpq heq
    exact hpq (normalVec_injective heq)
  · intro hpq heq
    exact hpq (congrArg normalVec heq)

/-- Distinct affine points give projectively distinct dual-line normals. -/
lemma normalVec_cross_ne_zero {p q : Point} (hpq : p ≠ q) :
    normalVec p ⨯₃ normalVec q ≠ 0 := by
  rw [normalVec_eq_toCoordinates_embed, normalVec_eq_toCoordinates_embed,
    ← ProjectiveDuality.toCoordinates_cross]
  exact (ProjectiveDuality.toCoordinates_ne_zero_iff _).2
    (ProjectiveDuality.pairIntersection_ne_zero hpq)

/-- Homogeneous incidence in `ProjectiveDuality` is exactly dot-product
incidence for the sign-vector normal. -/
lemma dotProduct_normalVec_toCoordinates_iff (p : Point)
    (h : ProjectiveDuality.Homogeneous) :
    normalVec p ⬝ᵥ ProjectiveDuality.toCoordinates h = 0 ↔
      h ∈ ProjectiveDuality.dualLine p := by
  rw [normalVec_eq_toCoordinates_embed,
    ProjectiveDuality.dotProduct_toCoordinates]
  rfl

/-- Matrix whose rows are the three normalized normals belonging to an
ordered affine triple. -/
def normalMatrix (p q r : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![normalVec p, normalVec q, normalVec r]

/-- The determinant of the normal matrix is the affine orientation
determinant. -/
lemma det_normalMatrix (p q r : Point) :
    (normalMatrix p q r).det = ProjectiveDuality.orientationDet p q r := by
  rw [Matrix.det_fin_three]
  simp [normalMatrix, normalVec, ProjectiveDuality.orientationDet]
  ring

/-- A noncollinear affine triple gives three linearly independent homogeneous
normals. -/
lemma linearIndependent_normalMatrix_rows {p q r : Point}
    (hncol : ¬ ProjectiveDuality.Collinear3 p q r) :
    LinearIndependent ℝ (normalMatrix p q r).row := by
  apply Matrix.linearIndependent_rows_of_det_ne_zero
    (A := normalMatrix p q r)
  rw [det_normalMatrix]
  simpa [ProjectiveDuality.Collinear3] using hncol

/-- The three normals of a noncollinear affine triple span homogeneous
three-space. -/
lemma span_normalMatrix_rows_eq_top {p q r : Point}
    (hncol : ¬ ProjectiveDuality.Collinear3 p q r) :
    Submodule.span ℝ (Set.range (normalMatrix p q r).row) = ⊤ := by
  apply (linearIndependent_normalMatrix_rows hncol).span_eq_top_of_card_eq_finrank'
  simp

/-- Exact rank-three bridge for a finite noncollinear configuration.  It is
enough to exhibit one noncollinear triple in `B`; the normals of all points of
`B` then span the full homogeneous space used by `BoundaryExtraction`. -/
theorem span_normalVec_range_eq_top_of_noncollinear_triple
    (B : Finset Point) {p q r : Point}
    (hp : p ∈ B) (hq : q ∈ B) (hr : r ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 p q r) :
    Submodule.span ℝ
      (Set.range (fun b : {x // x ∈ B} ↦ normalVec b.1)) = ⊤ := by
  have hthree := span_normalMatrix_rows_eq_top hncol
  apply top_unique
  rw [← hthree]
  apply Submodule.span_mono (R := ℝ)
  rintro v ⟨i, rfl⟩
  fin_cases i
  · exact ⟨⟨p, hp⟩, rfl⟩
  · exact ⟨⟨q, hq⟩, rfl⟩
  · exact ⟨⟨r, hr⟩, rfl⟩

/-! ## Projective intersection and chart-incidence bridges -/

/-- Dot product with a normal, as a linear functional. -/
def normalFunctional (v : SignVector.Vec3) : Module.Dual ℝ SignVector.Vec3 where
  toFun x := v ⬝ᵥ x
  map_add' x y := by simp [dotProduct_add]
  map_smul' a x := by simp [dotProduct_smul]

/-- Incidence of a projective point with a line represented by normal `v`. -/
def OnProjectiveLine (v : SignVector.Vec3) (x : ℙ ℝ SignVector.Vec3) : Prop :=
  normalFunctional v x.rep = 0

/-- Projective incidence can be checked on the vector used to construct the
projective point, independently of Mathlib's chosen representative. -/
lemma onProjectiveLine_mk_iff (v x : SignVector.Vec3) (hx : x ≠ 0) :
    OnProjectiveLine v (Projectivization.mk ℝ x hx) ↔ v ⬝ᵥ x = 0 := by
  exact ChartOrder.apply_rep_mk_eq_zero_iff (normalFunctional v) x hx

/-- The projective intersection of the dual lines belonging to two distinct
affine points. -/
def intersectionPoint (p q : Point) (hpq : p ≠ q) : ℙ ℝ SignVector.Vec3 :=
  Projectivization.mk ℝ (normalVec p ⨯₃ normalVec q)
    (normalVec_cross_ne_zero hpq)

lemma intersectionPoint_on_left (p q : Point) (hpq : p ≠ q) :
    OnProjectiveLine (normalVec p) (intersectionPoint p q hpq) := by
  rw [intersectionPoint, onProjectiveLine_mk_iff]
  exact dot_self_cross _ _

lemma intersectionPoint_on_right (p q : Point) (hpq : p ≠ q) :
    OnProjectiveLine (normalVec q) (intersectionPoint p q hpq) := by
  rw [intersectionPoint, onProjectiveLine_mk_iff]
  exact dot_cross_self _ _

lemma normalVec_dot_cross_eq_neg_orientation (p q r : Point) :
    normalVec q ⬝ᵥ (normalVec p ⨯₃ normalVec r) =
      -ProjectiveDuality.orientationDet p q r := by
  rw [vec3_dotProduct, cross_apply]
  simp [normalVec, ProjectiveDuality.orientationDet]
  ring

/-- On a noncollinear triple, the two projective vertices cut out on the
first dual line by the other two dual lines are distinct. -/
lemma intersectionPoint_ne_of_not_collinear {p q r : Point}
    (hncol : ¬ ProjectiveDuality.Collinear3 p q r) :
    intersectionPoint p q (by
      intro hpq
      apply hncol
      simp [hpq, ProjectiveDuality.Collinear3,
        ProjectiveDuality.orientationDet]) ≠
      intersectionPoint p r (by
        intro hpr
        apply hncol
        simp [hpr, ProjectiveDuality.Collinear3,
          ProjectiveDuality.orientationDet]) := by
  let hpq : p ≠ q := by
    intro h
    apply hncol
    simp [h, ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]
  let hpr : p ≠ r := by
    intro h
    apply hncol
    simp [h, ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]
  change intersectionPoint p q hpq ≠ intersectionPoint p r hpr
  intro heq
  have hinc : OnProjectiveLine (normalVec q) (intersectionPoint p r hpr) := by
    rw [← heq]
    exact intersectionPoint_on_right p q hpq
  have hdot : normalVec q ⬝ᵥ (normalVec p ⨯₃ normalVec r) = 0 :=
    (onProjectiveLine_mk_iff _ _ (normalVec_cross_ne_zero hpr)).mp hinc
  rw [normalVec_dot_cross_eq_neg_orientation] at hdot
  apply hncol
  simp only [ProjectiveDuality.Collinear3]
  linarith

/-- Ordered pairs of distinct members of a finite affine configuration. -/
abbrev DistinctPointPair (B : Finset Point) := {pq : B × B // pq.1 ≠ pq.2}

/-- The projective intersection vertex belonging to an ordered pair from
`B`. -/
def indexedIntersection (B : Finset Point) (pq : DistinctPointPair B) :
    ℙ ℝ SignVector.Vec3 :=
  intersectionPoint pq.1.1.1 pq.1.2.1 (by
    intro h
    apply pq.2
    exact Subtype.ext h)

/-- The finite projective vertex set of the dual-line arrangement.  Multiple
pairs meeting at the same projective point are automatically identified by
`Finset.image`. -/
def projectiveVertices (B : Finset Point) : Finset (ℙ ℝ SignVector.Vec3) := by
  classical
  exact Finset.univ.image (indexedIntersection B)

/-- Incidence relation in the argument order expected by `ChartOrder`. -/
def Incident (v : ℙ ℝ SignVector.Vec3) (p : Point) : Prop :=
  OnProjectiveLine (normalVec p) v

noncomputable instance incidentDecidableRel : DecidableRel Incident :=
  fun _ _ ↦ Classical.propDecidable _

lemma indexedIntersection_mem_projectiveVertices (B : Finset Point)
    (pq : DistinctPointPair B) : indexedIntersection B pq ∈ projectiveVertices B := by
  classical
  exact Finset.mem_image.mpr ⟨pq, Finset.mem_univ _, rfl⟩

lemma indexedIntersection_incident_left (B : Finset Point)
    (pq : DistinctPointPair B) :
    Incident (indexedIntersection B pq) pq.1.1.1 := by
  apply intersectionPoint_on_left

lemma indexedIntersection_incident_right (B : Finset Point)
    (pq : DistinctPointPair B) :
    Incident (indexedIntersection B pq) pq.1.2.1 := by
  apply intersectionPoint_on_right

/-- A noncollinear triple in `B` supplies two distinct arrangement vertices
on the dual line belonging to its first point.  This is the exact cardinality
hypothesis consumed by `CyclicArrangementGraph`. -/
lemma two_le_verticesOn_card_of_noncollinear_triple
    (B : Finset Point) {p q r : Point}
    (hp : p ∈ B) (hq : q ∈ B) (hr : r ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 p q r) :
    2 ≤ (ChartOrder.verticesOn (projectiveVertices B) Incident p).card := by
  classical
  have hpq : p ≠ q := by
    intro h
    apply hncol
    simp [h, ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]
  have hpr : p ≠ r := by
    intro h
    apply hncol
    simp [h, ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]
  let pq : DistinctPointPair B :=
    ⟨(⟨p, hp⟩, ⟨q, hq⟩), by
      intro h
      apply hpq
      exact congrArg Subtype.val h⟩
  let pr : DistinctPointPair B :=
    ⟨(⟨p, hp⟩, ⟨r, hr⟩), by
      intro h
      apply hpr
      exact congrArg Subtype.val h⟩
  apply Finset.one_lt_card.mpr
  refine ⟨indexedIntersection B pq, ?_, indexedIntersection B pr, ?_, ?_⟩
  · exact (ChartOrder.mem_verticesOn (projectiveVertices B) Incident).mpr
      ⟨indexedIntersection_mem_projectiveVertices B pq,
        indexedIntersection_incident_left B pq⟩
  · exact (ChartOrder.mem_verticesOn (projectiveVertices B) Incident).mpr
      ⟨indexedIntersection_mem_projectiveVertices B pr,
        indexedIntersection_incident_left B pr⟩
  · simpa [pq, pr, indexedIntersection] using
      (intersectionPoint_ne_of_not_collinear hncol)

lemma orientationDet_decompose (x a b c : Point) :
    ProjectiveDuality.orientationDet a b c =
      ProjectiveDuality.orientationDet x b c -
        ProjectiveDuality.orientationDet x a c +
          ProjectiveDuality.orientationDet x a b := by
  simp [ProjectiveDuality.orientationDet]
  ring

/-- Every point can be completed to a noncollinear triple using the vertices
of any fixed noncollinear triple. -/
lemma exists_noncollinear_pair_through_point {a b c : Point}
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) (x : Point) :
    (¬ ProjectiveDuality.Collinear3 x a b) ∨
      (¬ ProjectiveDuality.Collinear3 x a c) ∨
        (¬ ProjectiveDuality.Collinear3 x b c) := by
  by_contra h
  push Not at h
  apply hncol
  simp only [ProjectiveDuality.Collinear3] at h ⊢
  rw [orientationDet_decompose x a b c]
  rw [h.2.2, h.2.1, h.1]
  ring

/-- A finite configuration containing one noncollinear triple has at least
two distinct projective intersection vertices on every represented dual
line.  This discharges the line-cardinality input of the cyclic arrangement
graph uniformly. -/
theorem two_le_verticesOn_card_of_noncollinear_config
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    ∀ p ∈ B, 2 ≤
      (ChartOrder.verticesOn (projectiveVertices B) Incident p).card := by
  intro p hp
  rcases exists_noncollinear_pair_through_point hncol p with hab | hac | hbc
  · exact two_le_verticesOn_card_of_noncollinear_triple B hp ha hb hab
  · exact two_le_verticesOn_card_of_noncollinear_triple B hp ha hc hac
  · exact two_le_verticesOn_card_of_noncollinear_triple B hp hb hc hbc

/-- The finite projective vertex set admits an avoiding affine chart and a
coordinate separating all normalized vertices. -/
theorem exists_chart_and_separating_coordinate (B : Finset Point) :
    ∃ f g : Module.Dual ℝ SignVector.Vec3,
      (∀ v ∈ projectiveVertices B, f v.rep ≠ 0) ∧
      Set.InjOn (ChartOrder.chartCoord f g)
        (projectiveVertices B : Set (ℙ ℝ SignVector.Vec3)) :=
  ChartOrder.exists_chart_and_separating_coordinate (projectiveVertices B)

/-- Chart normalization preserves concrete normal incidence. -/
lemma normalFunctional_chartRep_eq_zero_iff
    (f : Module.Dual ℝ SignVector.Vec3) (v : SignVector.Vec3)
    (x : ℙ ℝ SignVector.Vec3) (hx : f x.rep ≠ 0) :
    normalFunctional v (ChartOrder.chartRep f x) = 0 ↔
      OnProjectiveLine v x := by
  exact ChartOrder.apply_chartRep_eq_zero_iff f (normalFunctional v) x hx

/-- Two distinct dual projective lines have at most one common projective
point.  This representative-free form is used to exclude a red chord whose
two endpoints are consecutive on one blue boundary line. -/
theorem eq_of_two_common_lines {a b : Point} (hab : a ≠ b)
    {x y : ℙ ℝ SignVector.Vec3}
    (hxa : Incident x a) (hxb : Incident x b)
    (hya : Incident y a) (hyb : Incident y b) : x = y := by
  have hxaH : ProjectiveDuality.dot (ProjectiveDuality.embed a)
      (ProjectiveDuality.fromCoordinates x.rep) = 0 := by
    rw [← ProjectiveDuality.dotProduct_toCoordinates]
    simpa [normalVec_eq_toCoordinates_embed, Incident, OnProjectiveLine,
      normalFunctional] using hxa
  have hxbH : ProjectiveDuality.dot (ProjectiveDuality.embed b)
      (ProjectiveDuality.fromCoordinates x.rep) = 0 := by
    rw [← ProjectiveDuality.dotProduct_toCoordinates]
    simpa [normalVec_eq_toCoordinates_embed, Incident, OnProjectiveLine,
      normalFunctional] using hxb
  have hyaH : ProjectiveDuality.dot (ProjectiveDuality.embed a)
      (ProjectiveDuality.fromCoordinates y.rep) = 0 := by
    rw [← ProjectiveDuality.dotProduct_toCoordinates]
    simpa [normalVec_eq_toCoordinates_embed, Incident, OnProjectiveLine,
      normalFunctional] using hya
  have hybH : ProjectiveDuality.dot (ProjectiveDuality.embed b)
      (ProjectiveDuality.fromCoordinates y.rep) = 0 := by
    rw [← ProjectiveDuality.dotProduct_toCoordinates]
    simpa [normalVec_eq_toCoordinates_embed, Incident, OnProjectiveLine,
      normalFunctional] using hyb
  obtain ⟨cx, hcx⟩ := ProjectiveDuality.common_point_eq_scale_cross
    (ProjectiveDuality.pairIntersection_ne_zero hab) hxaH hxbH
  obtain ⟨cy, hcy⟩ := ProjectiveDuality.common_point_eq_scale_cross
    (ProjectiveDuality.pairIntersection_ne_zero hab) hyaH hybH
  have hcx0 : cx ≠ 0 := by
    intro hc
    apply Projectivization.rep_nonzero x
    have hz : ProjectiveDuality.scale cx
        (ProjectiveDuality.cross (ProjectiveDuality.embed a)
          (ProjectiveDuality.embed b)) = ProjectiveDuality.homZero := by
      rw [hc]
      ext <;> simp [ProjectiveDuality.scale, ProjectiveDuality.homZero]
    rw [hz] at hcx
    have h := congrArg ProjectiveDuality.toCoordinates hcx
    simpa only [ProjectiveDuality.toCoordinates_fromCoordinates,
      ProjectiveDuality.toCoordinates_homZero] using h
  have hcy0 : cy ≠ 0 := by
    intro hc
    apply Projectivization.rep_nonzero y
    have hz : ProjectiveDuality.scale cy
        (ProjectiveDuality.cross (ProjectiveDuality.embed a)
          (ProjectiveDuality.embed b)) = ProjectiveDuality.homZero := by
      rw [hc]
      ext <;> simp [ProjectiveDuality.scale, ProjectiveDuality.homZero]
    rw [hz] at hcy
    have h := congrArg ProjectiveDuality.toCoordinates hcy
    simpa only [ProjectiveDuality.toCoordinates_fromCoordinates,
      ProjectiveDuality.toCoordinates_homZero] using h
  rw [← Projectivization.mk_rep x, ← Projectivization.mk_rep y]
  apply (Projectivization.mk_eq_mk_iff' ℝ x.rep y.rep
    (Projectivization.rep_nonzero x) (Projectivization.rep_nonzero y)).2
  refine ⟨cx / cy, ?_⟩
  have hx := congrArg ProjectiveDuality.toCoordinates hcx
  have hy := congrArg ProjectiveDuality.toCoordinates hcy
  simp only [ProjectiveDuality.toCoordinates_fromCoordinates] at hx hy
  rw [hx, hy]
  funext i
  fin_cases i <;>
    simp [ProjectiveDuality.scale, ProjectiveDuality.toCoordinates] <;>
    field_simp

end

end Erdos735.ProjectiveArrangement
