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

import ErdosProblems.Erdos735.RedBlueDualIncidence

/-!
# Concrete incidence constraints for red chords

A red line cuts a blue strict face precisely when the face sign pattern is
realizable after restriction to the red normal's kernel.  This file records
that definition and proves the two incidence facts needed after the two
sector endpoints have been extracted geometrically:

* endpoints belonging to distinct red lines are disjoint, because the
  crossing of two red lines is ordinary and therefore contains no blue line;
* two distinct endpoints on one red line cannot lie on a common blue line,
  and hence cannot be the endpoints of one blue boundary edge.

These statements use the actual projective vertices of the concrete blue
arrangement, independently of any cardinality-chosen edge equivalence.
-/

open Classical
open scoped LinearAlgebra.Projectivization

namespace Erdos735.RedChordIncidence

open ProjectiveArrangement ProjectiveBoundaryExtraction
open RedBlueDualIncidence SignVector

noncomputable section

/-- A red normal cuts the interior of the blue strict face `f`. -/
def IsRedChord {I : Type*} (blueNormals : I → Vec3)
    (f : StrictFace blueNormals) (redNormal : Vec3) : Prop :=
  RestrictedRealizable blueNormals redNormal f.1

/-- Concrete specialization to the dual line of an affine red point. -/
def IsConcreteRedChord (B : Finset Point) (f : StrictFace (normals B))
    (a : Point) : Prop :=
  IsRedChord (normals B) f (normalVec a)

/-- The blue arrangement vertices lying on the dual line of `a`.  A sector
endpoint produced by the red chord construction belongs to this finset. -/
def redBlueVertices (P : Finset Point) (a : Point) :
    Finset (ℙ ℝ Vec3) := by
  classical
  exact (projectiveVertices (nonordinaryPoints P)).filter fun v ↦ Incident v a

@[simp] theorem mem_redBlueVertices {P : Finset Point} {a : Point}
    {v : ℙ ℝ Vec3} :
    v ∈ redBlueVertices P a ↔
      v ∈ projectiveVertices (nonordinaryPoints P) ∧ Incident v a := by
  simp [redBlueVertices]

/-- Concrete projective incidence can be read on the homogeneous
representative used in the reduced-magic development, for any affine point
(not only a member of the blue indexing finset). -/
lemma incident_iff_vertexHomogeneous {B : Finset Point} (v : Vertex B)
    (p : Point) :
    Incident v.1 p ↔
      vertexHomogeneous v ∈ ProjectiveDuality.dualLine p := by
  change normalVec p ⬝ᵥ v.1.rep = 0 ↔ _
  simpa [vertexHomogeneous] using
    (dotProduct_normalVec_toCoordinates_iff p (vertexHomogeneous v))

/-- Every concrete projective blue vertex is incident with at least one
blue line (in fact with both lines of any pair producing it). -/
lemma exists_incident_line_of_projectiveVertex (B : Finset Point)
    (v : Vertex B) : ∃ b ∈ B, Incident v.1 b := by
  have hv := v.2
  unfold projectiveVertices at hv
  obtain ⟨pq, -, hpqv⟩ := Finset.mem_image.mp hv
  refine ⟨pq.1.1.1, pq.1.1.2, ?_⟩
  rw [← hpqv]
  exact indexedIntersection_incident_left B pq

/-- Two distinct red lines cannot share a projective blue vertex.  Such a
vertex also contains a blue line, whereas the reduced-magic ordinary-fiber
theorem says that a crossing of two red lines contains exactly those two red
lines. -/
theorem no_common_blueVertex_of_distinct_red
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    {a a' : Point} (ha : a ∈ ordinaryPoints P)
    (ha' : a' ∈ ordinaryPoints P) (haa' : a ≠ a')
    (v : Vertex (nonordinaryPoints P))
    (hva : Incident v.1 a) (hva' : Incident v.1 a') : False := by
  obtain ⟨b, hb, hvb⟩ :=
    exists_incident_line_of_projectiveVertex (nonordinaryPoints P) v
  have hab := ordinary_incident_unique_at_blue_crossing hred
    (isDualCrossing_vertex_nonordinary P v) hb
    ((incident_iff_vertexHomogeneous v b).mp hvb)
    ha ha'
    ((incident_iff_vertexHomogeneous v a).mp hva)
    ((incident_iff_vertexHomogeneous v a').mp hva')
  exact haa' hab

/-- Endpoint finsets of distinct red lines are disjoint. -/
theorem redBlueVertices_disjoint_of_distinct
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    {a a' : Point} (ha : a ∈ ordinaryPoints P)
    (ha' : a' ∈ ordinaryPoints P) (haa' : a ≠ a') :
    Disjoint (redBlueVertices P a) (redBlueVertices P a') := by
  rw [Finset.disjoint_left]
  intro v hva hva'
  have hvaData := mem_redBlueVertices.mp hva
  have hva'Data := mem_redBlueVertices.mp hva'
  exact no_common_blueVertex_of_distinct_red hred ha ha' haa'
    ⟨v, hvaData.1⟩ hvaData.2 hva'Data.2

/-- A red point and a blue point are distinct. -/
lemma red_ne_blue {P : Finset Point} {a b : Point}
    (ha : a ∈ ordinaryPoints P) (hb : b ∈ nonordinaryPoints P) : a ≠ b := by
  intro hab
  subst b
  exact (Finset.disjoint_left.mp (disjoint_ordinaryPoints_nonordinaryPoints P)) ha hb

/-- Every red--blue crossing is already a vertex of the blue-only
arrangement.  Indeed the primal line through a red and a blue point is not
ordinary, so it contains a third point; that third point must be blue because
a line through two distinct red points is ordinary. -/
theorem red_blue_intersection_mem_projectiveVertices
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    {a b : Point} (ha : a ∈ ordinaryPoints P)
    (hb : b ∈ nonordinaryPoints P) :
    intersectionPoint a b (red_ne_blue ha hb) ∈
      projectiveVertices (nonordinaryPoints P) := by
  classical
  let hab : a ≠ b := red_ne_blue ha hb
  have haP : a ∈ P := ordinaryPoints_subset P ha
  have hbP : b ∈ P := nonordinaryPoints_subset P hb
  have hfiberNe : lineFiber P a b ≠ {a, b} := by
    intro hpair
    have hcolors := (hred.2.2.2.2.2 a haP b hbP hab).mp hpair
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) hcolors.2 hb
  have hstrict : {a, b} ⊂ lineFiber P a b :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨pair_subset_lineFiber haP hbP, Ne.symm hfiberNe⟩
  obtain ⟨d, hdFiber, hdPair⟩ := Finset.exists_of_ssubset hstrict
  have hdData := Finset.mem_filter.mp hdFiber
  have hda : d ≠ a := by
    intro hda
    subst d
    exact hdPair (Finset.mem_insert_self _ _)
  have hdb : d ≠ b := by
    intro hdb
    subst d
    exact hdPair (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hadb : Collinear3 a d b :=
    (collinear3_swap_left a d b).mp
      (collinear3_cycle.mp (collinear3_cycle.mp hdData.2))
  have hdNotRed : d ∉ ordinaryPoints P := by
    intro hdRed
    have hadFiber := hred.2.2.2.2.1 a ha d hdRed hda.symm
    have hbFiber : b ∈ lineFiber P a d := by
      exact Finset.mem_filter.mpr ⟨hbP, hadb⟩
    rw [hadFiber] at hbFiber
    rcases Finset.mem_insert.mp hbFiber with hba | hbd
    · exact hab hba.symm
    · exact hdb (Finset.mem_singleton.mp hbd).symm
  have hdBlue : d ∈ nonordinaryPoints P :=
    Finset.mem_sdiff.mpr ⟨hdData.1, hdNotRed⟩
  have hvd : Incident (intersectionPoint a b hab) d := by
    change OnProjectiveLine (normalVec d) (intersectionPoint a b hab)
    rw [intersectionPoint, onProjectiveLine_mk_iff,
      normalVec_dot_cross_eq_neg_orientation a d b]
    dsimp [Erdos735.Collinear3, Erdos735.orientationDet] at hadb
    dsimp [ProjectiveDuality.orientationDet]
    linarith
  have hbd : b ≠ d := Ne.symm hdb
  have heq : intersectionPoint a b hab = intersectionPoint b d hbd :=
    ProjectiveArrangement.eq_of_two_common_lines hbd
      (intersectionPoint_on_right a b hab) hvd
      (intersectionPoint_on_left b d hbd)
      (intersectionPoint_on_right b d hbd)
  let bb : {x // x ∈ nonordinaryPoints P} := ⟨b, hb⟩
  let dd : {x // x ∈ nonordinaryPoints P} := ⟨d, hdBlue⟩
  let bd : DistinctPointPair (nonordinaryPoints P) :=
    ⟨(bb, dd), fun h ↦ hbd (congrArg Subtype.val h)⟩
  rw [heq]
  simpa [indexedIntersection, bd, bb, dd] using
    (indexedIntersection_mem_projectiveVertices (nonordinaryPoints P) bd)

/-- Two projective points incident with the same red and blue lines are
equal.  Thus a red line cannot enter and leave a blue face through the two
ends of one blue boundary edge. -/
theorem eq_of_common_red_and_blue_lines
    {P : Finset Point} {a b : Point}
    (ha : a ∈ ordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
    {v z : ℙ ℝ Vec3}
    (hva : Incident v a) (hvb : Incident v b)
    (hza : Incident z a) (hzb : Incident z b) : v = z := by
  exact ProjectiveArrangement.eq_of_two_common_lines
    (red_ne_blue ha hb) hva hvb hza hzb

/-- Nonadjacency in the incidence form consumed by a concrete boundary
realization: distinct endpoints of one red chord cannot both lie on its
supporting blue boundary line. -/
theorem distinct_red_endpoints_not_common_blue_line
    {P : Finset Point} {a b : Point}
    (ha : a ∈ ordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
    {v z : ℙ ℝ Vec3} (hvz : v ≠ z)
    (hva : Incident v a) (hza : Incident z a) :
    ¬ (Incident v b ∧ Incident z b) := by
  rintro ⟨hvb, hzb⟩
  exact hvz (eq_of_common_red_and_blue_lines ha hb hva hvb hza hzb)

end

end Erdos735.RedChordIncidence
