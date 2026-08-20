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

import ErdosProblems.Erdos735.ConcretePolarEdgeVertices
import ErdosProblems.Erdos735.ProjectiveConcreteExtraction

open Classical
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization BigOperators
open Matrix

namespace Erdos735.ConcretePolarVertexDegree

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.RedChordSector
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B
abbrev BaseVertex (B : Finset Point) := ProjectiveBoundaryExtraction.Vertex B
abbrev Vertex (B : Finset Point) := ConcretePolarOrientedVertex.OrientedVertex B

private lemma dot_comm_homogeneous (a b : ProjectiveDuality.Homogeneous) :
    ProjectiveDuality.dot a b = ProjectiveDuality.dot b a := by
  simp [ProjectiveDuality.dot]
  ring

private lemma dot_cross_cross (u v y z : ProjectiveDuality.Homogeneous) :
    ProjectiveDuality.dot (ProjectiveDuality.cross u v) (ProjectiveDuality.cross y z) =
      ProjectiveDuality.dot u y * ProjectiveDuality.dot v z -
        ProjectiveDuality.dot u z * ProjectiveDuality.dot v y := by
  simp [ProjectiveDuality.dot, ProjectiveDuality.cross]
  ring

private lemma dot_scale_scale (a b : ℝ)
    (x y : ProjectiveDuality.Homogeneous) :
    ProjectiveDuality.dot (ProjectiveDuality.scale a x) (ProjectiveDuality.scale b y) =
      a * b * ProjectiveDuality.dot x y := by
  simp [ProjectiveDuality.dot, ProjectiveDuality.scale]
  ring

/-- Determinantal relation for three hyperplanes through a nonzero point. -/
private theorem incident_dot_crossRatio
    {u v r x y z : ProjectiveDuality.Homogeneous}
    (hxne : x ≠ ProjectiveDuality.homZero)
    (hrne : r ≠ ProjectiveDuality.homZero)
    (hux : ProjectiveDuality.dot u x = 0)
    (hvx : ProjectiveDuality.dot v x = 0)
    (hrx : ProjectiveDuality.dot r x = 0)
    (hry : ProjectiveDuality.dot r y = 0)
    (hrz : ProjectiveDuality.dot r z = 0) :
    ProjectiveDuality.dot u y * ProjectiveDuality.dot v z =
      ProjectiveDuality.dot v y * ProjectiveDuality.dot u z := by
  by_cases huv : ProjectiveDuality.cross u v = ProjectiveDuality.homZero
  · have hdet := dot_cross_cross u v y z
    rw [huv] at hdet
    have hz : ProjectiveDuality.dot ProjectiveDuality.homZero
        (ProjectiveDuality.cross y z) = 0 := by
      simp [ProjectiveDuality.dot, ProjectiveDuality.homZero]
    rw [hz] at hdet
    linarith
  by_cases hyz : ProjectiveDuality.cross y z = ProjectiveDuality.homZero
  · have hdet := dot_cross_cross u v y z
    rw [hyz] at hdet
    have hz : ProjectiveDuality.dot (ProjectiveDuality.cross u v)
        ProjectiveDuality.homZero = 0 := by
      simp [ProjectiveDuality.dot, ProjectiveDuality.homZero]
    rw [hz] at hdet
    linarith
  obtain ⟨a, hxa⟩ := ProjectiveDuality.common_point_eq_scale_cross huv hux hvx
  obtain ⟨b, hrb⟩ := ProjectiveDuality.common_point_eq_scale_cross hyz
    ((dot_comm_homogeneous y r).trans hry)
    ((dot_comm_homogeneous z r).trans hrz)
  have ha : a ≠ 0 := by
    intro ha
    apply hxne
    rw [hxa, ha]
    ext <;> simp [ProjectiveDuality.scale, ProjectiveDuality.homZero]
  have hb : b ≠ 0 := by
    intro hb
    apply hrne
    rw [hrb, hb]
    ext <;> simp [ProjectiveDuality.scale, ProjectiveDuality.homZero]
  have hcrossdot : ProjectiveDuality.dot
      (ProjectiveDuality.cross u v) (ProjectiveDuality.cross y z) = 0 := by
    have hxr : ProjectiveDuality.dot x r = 0 :=
      (dot_comm_homogeneous x r).trans hrx
    rw [hxa, hrb, dot_scale_scale] at hxr
    rcases mul_eq_zero.mp hxr with hab | hd
    · rcases mul_eq_zero.mp hab with ha0 | hb0
      · exact (ha ha0).elim
      · exact (hb hb0).elim
    · exact hd
  rw [dot_cross_cross] at hcrossdot
  linarith

private lemma dot_fromCoordinates_fromCoordinates (a b : Vec3) :
    ProjectiveDuality.dot (ProjectiveDuality.fromCoordinates a)
      (ProjectiveDuality.fromCoordinates b) = a ⬝ᵥ b := by
  simp [ProjectiveDuality.dot, ProjectiveDuality.fromCoordinates, vec3_dotProduct]

/-- At a fixed oriented projective vertex and on a fixed incident line,
the sign on one other incident line determines the entire open edge sector. -/
theorem restrictedSigns_eq_of_weaklyRealizes
    {B : Finset Point} [Nonempty (Line B)]
    (v : Vertex B) (i q : Line B) (hqi : q ≠ i)
    (hi : OnLine B v.1 i) (hq : OnLine B v.1 q)
    (s t : {j : Line B // j ≠ i} → Bool)
    (hs : RestrictedRealizable (otherNormals (normals B) i) (normals B i) s)
    (ht : RestrictedRealizable (otherNormals (normals B) i) (normals B i) t)
    (hws : WeaklyRealizes (otherNormals (normals B) i) s (orientedRep v))
    (hwt : WeaklyRealizes (otherNormals (normals B) i) t (orientedRep v))
    (hqt : s ⟨q, hqi⟩ = t ⟨q, hqi⟩) : s = t := by
  funext j
  by_cases hjq : j.1 = q
  · subst q
    simpa using hqt
  by_cases hjzero : otherNormals (normals B) i j ⬝ᵥ orientedRep v = 0
  · by_contra hst
    have hflip : t j = !(s j) := by
      cases hsval : s j <;> cases htval : t j <;> simp_all
    obtain ⟨y, hsy, hyi⟩ := hs
    obtain ⟨z, htz, hzi⟩ := ht
    have hratio := incident_dot_crossRatio
      (u := ProjectiveDuality.fromCoordinates (otherNormals (normals B) i ⟨q, hqi⟩))
      (v := ProjectiveDuality.fromCoordinates (otherNormals (normals B) i j))
      (r := ProjectiveDuality.fromCoordinates (normals B i))
      (x := ProjectiveDuality.fromCoordinates (orientedRep v))
      (y := ProjectiveDuality.fromCoordinates y)
      (z := ProjectiveDuality.fromCoordinates z)
      (by
        rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
        simpa using orientedRep_ne_zero v)
      (by
        rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
        simpa using normals_ne_zero B i)
      (by
        rw [dot_fromCoordinates_fromCoordinates]
        change normals B q ⬝ᵥ orientedRep v = 0
        apply (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).mp
        rw [orientedRep_projectivization]
        exact hq)
      (by simpa [dot_fromCoordinates_fromCoordinates] using hjzero)
      (by
        rw [dot_fromCoordinates_fromCoordinates]
        apply (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).mp
        rw [orientedRep_projectivization]
        exact hi)
      (by simpa [dot_fromCoordinates_fromCoordinates] using hyi)
      (by simpa [dot_fromCoordinates_fromCoordinates] using hzi)
    have hqy := hsy ⟨q, hqi⟩
    have hjy := hsy j
    have hqz := htz ⟨q, hqi⟩
    have hjz := htz j
    rw [← hqt] at hqz
    rw [hflip] at hjz
    rw [dot_fromCoordinates_fromCoordinates, dot_fromCoordinates_fromCoordinates,
      dot_fromCoordinates_fromCoordinates, dot_fromCoordinates_fromCoordinates] at hratio
    cases hsq : s ⟨q, hqi⟩ <;> cases hsj : s j <;>
      simp [signed, hsq, hsj] at hqy hjy hqz hjz <;> nlinarith
  · have hsweak := hws j
    have htweak := hwt j
    by_contra hst
    have hflip : t j = !(s j) := by
      cases hsval : s j <;> cases htval : t j <;> simp_all
    cases hsval : s j
    · have hsle : otherNormals (normals B) i j ⬝ᵥ orientedRep v ≤ 0 := by
        simpa [signed, hsval] using hsweak
      have htge : 0 ≤ otherNormals (normals B) i j ⬝ᵥ orientedRep v := by
        simpa [signed, hflip, hsval] using htweak
      exact hjzero (le_antisymm hsle htge)
    · have hsge : 0 ≤ otherNormals (normals B) i j ⬝ᵥ orientedRep v := by
        simpa [signed, hsval] using hsweak
      have htle : otherNormals (normals B) i j ⬝ᵥ orientedRep v ≤ 0 := by
        simpa [signed, hflip, hsval] using htweak
      exact hjzero (le_antisymm htle hsge)

/-- A deterministic second arrangement line through a projective vertex. -/
noncomputable def otherIncidentLine
    (B : Finset Point) (v : BaseVertex B) (i : Line B) : Line B :=
  Classical.choose (exists_other_incident_line B v i)

theorem otherIncidentLine_ne
    (B : Finset Point) (v : BaseVertex B) (i : Line B) :
    otherIncidentLine B v i ≠ i :=
  (Classical.choose_spec (exists_other_incident_line B v i)).1

theorem otherIncidentLine_onLine
    (B : Finset Point) (v : BaseVertex B) (i : Line B) :
    OnLine B v (otherIncidentLine B v i) :=
  (Classical.choose_spec (exists_other_incident_line B v i)).2

/-- An actual oriented endpoint edge is encoded by its incident supporting
line and the one local direction bit measured on a second line through the
same projective vertex. -/
noncomputable def incidentEdgeCode
    {B : Finset Point} [Nonempty (Line B)]
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤) (v : Vertex B) :
    {e : StrictEdge (normals B) // e ∈ concreteVertexEdges hspan v} →
      {i : Line B // OnLine B v.1 i} × Bool :=
  fun e ↦
    let i := e.1.1.1
    let hi : OnLine B v.1 i := concreteEdgeVertex_on_support hspan e.1 v
      ((mem_concreteVertexEdges_iff hspan v e.1).mp e.2)
    let q := otherIncidentLine B v.1 i
    (⟨i, hi⟩, e.1.1.2 ⟨q, otherIncidentLine_ne B v.1 i⟩)

theorem incidentEdgeCode_injective
    {B : Finset Point} [Nonempty (Line B)]
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤) (v : Vertex B) :
    Function.Injective (incidentEdgeCode hspan v) := by
  rintro ⟨⟨⟨i, s⟩, hs⟩, he⟩ ⟨⟨⟨k, t⟩, ht⟩, hd⟩ hcode
  have hik : i = k := by
    have := congrArg (fun z : {i : Line B // OnLine B v.1 i} × Bool ↦ z.1.1) hcode
    simpa [incidentEdgeCode] using this
  subst k
  let q := otherIncidentLine B v.1 i
  let hqi : q ≠ i := otherIncidentLine_ne B v.1 i
  have hqt : s ⟨q, hqi⟩ = t ⟨q, hqi⟩ := by
    have := congrArg Prod.snd hcode
    simpa [incidentEdgeCode, q, hqi] using this
  have hws : WeaklyRealizes (otherNormals (normals B) i) s (orientedRep v) :=
    concreteEdgeVertex_weaklyRealizes_restriction hspan
      ⟨⟨i, s⟩, hs⟩ v ((mem_concreteVertexEdges_iff hspan v _).mp he)
  have hwt : WeaklyRealizes (otherNormals (normals B) i) t (orientedRep v) :=
    concreteEdgeVertex_weaklyRealizes_restriction hspan
      ⟨⟨i, t⟩, ht⟩ v ((mem_concreteVertexEdges_iff hspan v _).mp hd)
  have hst : s = t := restrictedSigns_eq_of_weaklyRealizes v i q hqi
    (concreteEdgeVertex_on_support hspan ⟨⟨i, s⟩, hs⟩ v
      ((mem_concreteVertexEdges_iff hspan v _).mp he))
    (otherIncidentLine_onLine B v.1 i) s t hs ht hws hwt hqt
  apply Subtype.ext
  apply Subtype.ext
  exact Sigma.ext rfl (hst ▸ HEq.rfl)

theorem card_incidentLine_prod_bool
    {B : Finset Point} (v : BaseVertex B) :
    Fintype.card ({i : Line B // OnLine B v i} × Bool) =
      2 * lineMultiplicity (OnLine B) v := by
  rw [Fintype.card_prod, Fintype.card_bool, mul_comm]
  congr 1
  rw [Fintype.card_subtype]
  rfl

/-- The literal polar degree is at most the expected two local directions
for every blue line through the projective vertex. -/
theorem concreteVertexEdges_card_le
    {B : Finset Point} [Nonempty (Line B)]
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤) (v : Vertex B) :
    (concreteVertexEdges hspan v).card ≤
      2 * lineMultiplicity (OnLine B) v.1 := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card {e // e ∈ concreteVertexEdges hspan v} ≤
        Fintype.card ({i : Line B // OnLine B v.1 i} × Bool) :=
      Fintype.card_le_of_injective (incidentEdgeCode hspan v)
        (incidentEdgeCode_injective hspan v)
    _ = 2 * lineMultiplicity (OnLine B) v.1 := card_incidentLine_prod_bool v.1

/-- Double-counting the literal endpoint relation uses only that every
concrete strict edge has exactly two endpoints. -/
theorem sum_concreteVertexEdges_card
    {B : Finset Point} [Nonempty (Line B)]
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤) :
    (∑ v : Vertex B, (concreteVertexEdges hspan v).card) =
      2 * Fintype.card (StrictEdge (normals B)) := by
  calc
    (∑ v : Vertex B, (concreteVertexEdges hspan v).card) =
        ∑ v : Vertex B, ∑ e : StrictEdge (normals B),
          if e ∈ concreteVertexEdges hspan v then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [concreteVertexEdges]
    _ = ∑ e : StrictEdge (normals B), ∑ v : Vertex B,
          if e ∈ concreteVertexEdges hspan v then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e : StrictEdge (normals B), (concreteEdgeVertices hspan e).card := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [mem_concreteVertexEdges_iff]
      simp
    _ = 2 * Fintype.card (StrictEdge (normals B)) := by
      simp [concreteEdgeVertices_card, mul_comm]

/-- The already checked deletion--restriction count gives the same total
for the expected degrees, independently of how its auxiliary cyclic-edge
equivalence chose endpoints. -/
theorem sum_expected_vertexDegrees
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    (∑ v : Vertex B, 2 * lineMultiplicity (OnLine B) v.1) =
      2 * Fintype.card (StrictEdge (normals B)) := by
  have hedge : Fintype.card (StrictEdge (normals B)) =
      2 * ∑ v : BaseVertex B, lineMultiplicity (OnLine B) v := by
    rw [card_strictEdge]
    calc
      (∑ i : Line B,
          restrictedFaceCount (otherNormals (normals B) i) (normals B i)) =
          ∑ i : Line B,
            2 * (verticesOn (Finset.univ : Finset (BaseVertex B))
              (OnLine B) i).card := by
        apply Finset.sum_congr rfl
        intro i hi
        exact concreteRestrictedFaceCount B ha hb hc hncol i
      _ = 2 * ∑ i : Line B,
          (verticesOn (Finset.univ : Finset (BaseVertex B)) (OnLine B) i).card := by
        rw [Finset.mul_sum]
      _ = 2 * ∑ v : BaseVertex B, lineMultiplicity (OnLine B) v := by
        congr 1
        simp only [verticesOn, lineMultiplicity, Finset.card_filter]
        rw [Finset.sum_comm]
  rw [hedge, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  calc
    (∑ x : BaseVertex B,
        (2 * lineMultiplicity (OnLine B) x +
          2 * lineMultiplicity (OnLine B) x)) =
        ∑ x : BaseVertex B, 4 * lineMultiplicity (OnLine B) x := by
      apply Finset.sum_congr rfl
      intro x hx
      omega
    _ = 4 * ∑ x : BaseVertex B, lineMultiplicity (OnLine B) x := by
      rw [Finset.mul_sum]
    _ = 2 * (2 * ∑ x : BaseVertex B,
        lineMultiplicity (OnLine B) x) := by ring

/-- Exact local degree of the literal oriented polar one-skeleton.  The
pointwise upper bound and equality of the two finite total degree sums force
equality at every vertex. -/
theorem concreteVertexEdges_card_eq
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    letI : Nonempty (Line B) := ⟨⟨a, ha⟩⟩
    let hspan := span_normalVec_range_eq_top_of_noncollinear_triple
      B ha hb hc hncol
    ∀ v : Vertex B,
      (concreteVertexEdges hspan v).card =
        2 * lineMultiplicity (OnLine B) v.1 := by
  letI : Nonempty (Line B) := ⟨⟨a, ha⟩⟩
  dsimp only
  intro v
  let hspan := span_normalVec_range_eq_top_of_noncollinear_triple B ha hb hc hncol
  have hle (v : Vertex B) :
      (concreteVertexEdges hspan v).card ≤
        2 * lineMultiplicity (OnLine B) v.1 :=
    concreteVertexEdges_card_le hspan v
  have hsum :
      (∑ v : Vertex B, (concreteVertexEdges hspan v).card) =
        ∑ v : Vertex B, 2 * lineMultiplicity (OnLine B) v.1 := by
    rw [sum_concreteVertexEdges_card hspan,
      sum_expected_vertexDegrees B ha hb hc hncol]
  have hall : ∀ w ∈ (Finset.univ : Finset (Vertex B)),
      (concreteVertexEdges hspan w).card =
        2 * lineMultiplicity (OnLine B) w.1 :=
    (Finset.sum_eq_sum_iff_of_le
      (s := (Finset.univ : Finset (Vertex B)))
      (f := fun w ↦ (concreteVertexEdges hspan w).card)
      (g := fun w ↦ 2 * lineMultiplicity (OnLine B) w.1)
      (fun w hw ↦ hle w)).mp (by simpa using hsum)
  exact hall v (Finset.mem_univ v)

end Erdos735.ConcretePolarVertexDegree
