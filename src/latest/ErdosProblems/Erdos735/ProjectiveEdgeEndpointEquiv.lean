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

import ErdosProblems.Erdos735.ProjectiveBoundaryExtraction
import ErdosProblems.Erdos735.ProjectiveConcreteExtraction
import ErdosProblems.Erdos735.ProjectiveLineChart
import ErdosProblems.Erdos735.RedChordSector

/-!
# Concrete endpoints of projective strict edges

This file starts the label-preserving replacement for the cardinality-chosen
equivalence between projective strict sign edges and the cyclic projective
skeleton.  A restricted sign pattern on one dual line is equipped with its
two literal adjacent arrangement intersections.
-/

open Classical
open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.SignVector.ProjectiveEdgeEndpointEquiv

noncomputable section

open ChartOrder ProjectiveArrangement ProjectiveBoundaryExtraction
open PolarFace RedChordSector

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The restriction-sector direction is nonzero without any rank hypothesis:
otherwise the positive oriented sum would be parallel to the cutting normal,
contradicting its positive value on the strict witness. -/
lemma direction_ne_zero_of_restricted
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hh : h ≠ 0) (hx : Realizes n s x) (hhx : h ⬝ᵥ x = 0) :
    direction n s h ≠ 0 := by
  intro hz
  have hdep : ¬ LinearIndependent ℝ ![h, orientedSum n s] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]
    exact not_ne_iff.mpr hz
  have hpair := (LinearIndependent.pair_iff' hh).not.mp hdep
  push Not at hpair
  obtain ⟨a, ha⟩ := hpair
  have hsumpos : 0 < orientedSum n s ⬝ᵥ x := by
    rw [orientedSum, sum_dotProduct]
    exact Finset.sum_pos (fun i _ ↦ by
      simpa [orientedNormal_dot] using hx i) Finset.univ_nonempty
  have hzero : orientedSum n s ⬝ᵥ x = 0 := by
    rw [← ha]
    simp [smul_dotProduct, hhx]
  linarith

/-- If the cutting normal together with all restricted normals spans the
ambient three-space, some restricted normal has nonzero slope. -/
lemma exists_slope_ne_zero_of_span_insert_eq_top
    {n : I → Vec3} {s : I → Bool} {h : Vec3}
    (hspan : Submodule.span ℝ (Set.insert h (Set.range n)) = ⊤)
    (hz : direction n s h ≠ 0) :
    ∃ i, slope n s h i ≠ 0 := by
  by_contra hall
  push Not at hall
  let z := direction n s h
  let L : Vec3 →ₗ[ℝ] ℝ :=
    { toFun := fun v ↦ v ⬝ᵥ z
      map_add' := by intro u v; simp [add_dotProduct]
      map_smul' := by intro c v; simp [smul_dotProduct] }
  have hnker : Set.range n ⊆ L.ker := by
    rintro v ⟨i, rfl⟩
    change n i ⬝ᵥ z = 0
    have hi : orientedNormal n s i ⬝ᵥ z = 0 := hall i
    rw [← signScalar_smul_orientedNormal n s i]
    simp [hi]
  have hhker : h ∈ L.ker := by
    change h ⬝ᵥ direction n s h = 0
    exact dot_self_cross _ _
  have hins : Set.insert h (Set.range n) ⊆ L.ker := by
    intro v hv
    rcases hv with rfl | hv
    · exact hhker
    · exact hnker hv
  have hle : Submodule.span ℝ (Set.insert h (Set.range n)) ≤ L.ker :=
    (Submodule.span_le).2 hins
  rw [hspan] at hle
  have hzz : z ⬝ᵥ z = 0 := hle (by simp)
  exact hz (dotProduct_self_eq_zero.mp hzz)

/-- Endpoint data under the natural rank hypothesis for a restricted
arrangement: the cutting normal is included in the spanning family. -/
def endpointDataOfRestrictedInsertSpan
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hh : h ≠ 0) (hx : Realizes n s x) (hhx : h ⬝ᵥ x = 0)
    (hspan : Submodule.span ℝ (Set.insert h (Set.range n)) = ⊤) :
    EndpointData n s h x hx := by
  let hz := direction_ne_zero_of_restricted hh hx hhx
  obtain ⟨hl, hu, hlu, hreal, hboundary⟩ :=
    chart_sector_has_exactly_two_endpoints hx
      (exists_slope_ne_zero_of_span_insert_eq_top hspan hz)
  exact
    { lower_nonempty := hl
      upper_nonempty := hu
      direction_ne_zero := hz
      lower_lt_upper := hlu
      realizes_iff := hreal
      boundary_iff := hboundary
      lower_active := lowerEndpoint_active hl
      upper_active := upperEndpoint_active hu
      projective_card := projectiveEndpoints_card hx hz hl hu hlu }

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B

/-- Removing one normal but retaining it as the cutting normal leaves the
same spanning family as the full configuration. -/
theorem span_insert_otherNormals_eq_top
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) (i : Line B) :
    Submodule.span ℝ
        (Set.insert (normals B i) (Set.range (otherNormals (normals B) i))) = ⊤ := by
  apply top_unique
  rw [← span_normalVec_range_eq_top_of_noncollinear_triple B ha hb hc hncol]
  apply Submodule.span_mono
  rintro v ⟨j, rfl⟩
  by_cases hji : j = i
  · subst j
    exact Set.mem_insert _ _
  · apply Set.mem_insert_of_mem
    exact ⟨⟨j, hji⟩, rfl⟩

/-- A noncollinear configuration has another line besides any specified
line, providing the nonempty restricted index type. -/
theorem exists_line_ne
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) (i : Line B) :
    ∃ j : Line B, j ≠ i := by
  by_cases hai : (⟨a, ha⟩ : Line B) ≠ i
  · exact ⟨⟨a, ha⟩, hai⟩
  · by_cases hbi : (⟨b, hb⟩ : Line B) ≠ i
    · exact ⟨⟨b, hb⟩, hbi⟩
    · exfalso
      apply hncol
      have hab : a = b := by
        exact congrArg Subtype.val <|
          (not_ne_iff.mp hai).trans (not_ne_iff.mp hbi).symm
      subst b
      simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]

section ConcreteEdge

variable (B : Finset Point) {a b c : Point}
variable (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
variable (pick : OtherLineChoice (Line B))

private def restrictedIndexNonempty (i : Line B) :
    Nonempty {j : Line B // j ≠ i} :=
  ⟨⟨Classical.choose (exists_line_ne B ha hb hc hncol i),
    Classical.choose_spec (exists_line_ne B ha hb hc hncol i)⟩⟩

/-- A chosen strict witness for a projective sign edge. -/
def edgeWitness (e : ProjectiveStrictEdge pick (normals B)) : Vec3 :=
  Classical.choose e.1.2

theorem edgeWitness_realizes (e : ProjectiveStrictEdge pick (normals B)) :
    Realizes (otherNormals (normals B) e.1.1.1) e.1.1.2
      (edgeWitness B pick e) :=
  (Classical.choose_spec e.1.2).1

theorem edgeWitness_on_owner (e : ProjectiveStrictEdge pick (normals B)) :
    normals B e.1.1.1 ⬝ᵥ edgeWitness B pick e = 0 :=
  (Classical.choose_spec e.1.2).2

/-- The literal two-endpoint certificate attached to a projective strict
edge. -/
def edgeEndpointData (e : ProjectiveStrictEdge pick (normals B)) :
    letI := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
    EndpointData (otherNormals (normals B) e.1.1.1) e.1.1.2
      (normals B e.1.1.1) (edgeWitness B pick e)
      (edgeWitness_realizes B pick e) := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  exact endpointDataOfRestrictedInsertSpan
    (normals_ne_zero B e.1.1.1) (edgeWitness_realizes B pick e)
    (edgeWitness_on_owner B pick e)
    (span_insert_otherNormals_eq_top B ha hb hc hncol e.1.1.1)

/-- Lower literal projective endpoint of a projective strict edge. -/
def lowerEdgeProjectiveEndpoint
    (e : ProjectiveStrictEdge pick (normals B)) : ℙ ℝ Vec3 := by
  letI := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  exact lowerProjectiveEndpoint
    (otherNormals (normals B) e.1.1.1) e.1.1.2
    (normals B e.1.1.1) (edgeWitness B pick e)
    D.lower_nonempty (edgeWitness_realizes B pick e)

/-- Upper literal projective endpoint of a projective strict edge. -/
def upperEdgeProjectiveEndpoint
    (e : ProjectiveStrictEdge pick (normals B)) : ℙ ℝ Vec3 := by
  letI := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  exact upperProjectiveEndpoint
    (otherNormals (normals B) e.1.1.1) e.1.1.2
    (normals B e.1.1.1) (edgeWitness B pick e)
    D.upper_nonempty (edgeWitness_realizes B pick e)

theorem lowerEdgeProjectiveEndpoint_on_owner
    (e : ProjectiveStrictEdge pick (normals B)) :
    Incident (lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e) e.1.1.1.1 := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  apply (onProjectiveLine_mk_iff _ _
    (chartPoint_ne_zero (edgeWitness_realizes B pick e) _)).2
  exact D.lower_on_red (edgeWitness_on_owner B pick e)

theorem upperEdgeProjectiveEndpoint_on_owner
    (e : ProjectiveStrictEdge pick (normals B)) :
    Incident (upperEdgeProjectiveEndpoint B ha hb hc hncol pick e) e.1.1.1.1 := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  apply (onProjectiveLine_mk_iff _ _
    (chartPoint_ne_zero (edgeWitness_realizes B pick e) _)).2
  exact D.upper_on_red (edgeWitness_on_owner B pick e)

/-- The lower sector endpoint is an actual projective intersection of the
owner with an active second configuration line. -/
theorem lowerEdgeProjectiveEndpoint_mem_projectiveVertices
    (e : ProjectiveStrictEdge pick (normals B)) :
    lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e ∈ projectiveVertices B := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  obtain ⟨j, hj⟩ := D.exists_lower_owner_incident
  let pair : DistinctPointPair B :=
    ⟨(e.1.1.1, j.1), fun h ↦ j.2 h.symm⟩
  have heq : lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e =
      indexedIntersection B pair := by
    apply eq_of_two_common_lines (show e.1.1.1.1 ≠ j.1.1 by
      intro h
      exact j.2 (Subtype.ext h).symm)
    · exact lowerEdgeProjectiveEndpoint_on_owner B ha hb hc hncol pick e
    · exact hj
    · exact indexedIntersection_incident_left B pair
    · exact indexedIntersection_incident_right B pair
  rw [heq]
  exact indexedIntersection_mem_projectiveVertices B pair

/-- The upper sector endpoint is an actual projective intersection of the
owner with an active second configuration line. -/
theorem upperEdgeProjectiveEndpoint_mem_projectiveVertices
    (e : ProjectiveStrictEdge pick (normals B)) :
    upperEdgeProjectiveEndpoint B ha hb hc hncol pick e ∈ projectiveVertices B := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  obtain ⟨j, hj⟩ := D.exists_upper_owner_incident
  let pair : DistinctPointPair B :=
    ⟨(e.1.1.1, j.1), fun h ↦ j.2 h.symm⟩
  have heq : upperEdgeProjectiveEndpoint B ha hb hc hncol pick e =
      indexedIntersection B pair := by
    apply eq_of_two_common_lines (show e.1.1.1.1 ≠ j.1.1 by
      intro h
      exact j.2 (Subtype.ext h).symm)
    · exact upperEdgeProjectiveEndpoint_on_owner B ha hb hc hncol pick e
    · exact hj
    · exact indexedIntersection_incident_left B pair
    · exact indexedIntersection_incident_right B pair
  rw [heq]
  exact indexedIntersection_mem_projectiveVertices B pair

/-- The lower endpoint as a vertex of the concrete projective arrangement. -/
def lowerEdgeVertex (e : ProjectiveStrictEdge pick (normals B)) : Vertex B :=
  ⟨lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e,
    lowerEdgeProjectiveEndpoint_mem_projectiveVertices B ha hb hc hncol pick e⟩

/-- The upper endpoint as a vertex of the concrete projective arrangement. -/
def upperEdgeVertex (e : ProjectiveStrictEdge pick (normals B)) : Vertex B :=
  ⟨upperEdgeProjectiveEndpoint B ha hb hc hncol pick e,
    upperEdgeProjectiveEndpoint_mem_projectiveVertices B ha hb hc hncol pick e⟩

theorem lowerEdgeVertex_mem_verticesOn
    (e : ProjectiveStrictEdge pick (normals B)) :
    lowerEdgeVertex B ha hb hc hncol pick e ∈
      verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1 := by
  apply (mem_verticesOn _ _).2
  exact ⟨Finset.mem_univ _, lowerEdgeProjectiveEndpoint_on_owner B ha hb hc hncol pick e⟩

theorem upperEdgeVertex_mem_verticesOn
    (e : ProjectiveStrictEdge pick (normals B)) :
    upperEdgeVertex B ha hb hc hncol pick e ∈
      verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1 := by
  apply (mem_verticesOn _ _).2
  exact ⟨Finset.mem_univ _, upperEdgeProjectiveEndpoint_on_owner B ha hb hc hncol pick e⟩

theorem lowerEdgeVertex_ne_upperEdgeVertex
    (e : ProjectiveStrictEdge pick (normals B)) :
    lowerEdgeVertex B ha hb hc hncol pick e ≠
      upperEdgeVertex B ha hb hc hncol pick e := by
  intro h
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  have hp : lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e ≠
      upperEdgeProjectiveEndpoint B ha hb hc hncol pick e := by
    change lowerProjectiveEndpoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e)
        D.lower_nonempty (edgeWitness_realizes B pick e) ≠
      upperProjectiveEndpoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e)
        D.upper_nonempty (edgeWitness_realizes B pick e)
    intro hp
    have hcard := D.projective_card
    have hcard' :
        ({lowerProjectiveEndpoint
            (otherNormals (normals B) e.1.1.1) e.1.1.2
            (normals B e.1.1.1) (edgeWitness B pick e)
            D.lower_nonempty (edgeWitness_realizes B pick e),
          upperProjectiveEndpoint
            (otherNormals (normals B) e.1.1.1) e.1.1.2
            (normals B e.1.1.1) (edgeWitness B pick e)
            D.upper_nonempty (edgeWitness_realizes B pick e)} :
          Finset (ℙ ℝ Vec3)).card = 2 := by
      simpa only [projectiveEndpoints] using hcard
    rw [hp] at hcard'
    simp at hcard'
  exact hp (congrArg Subtype.val h)

/-- No projective arrangement vertex lies in the open restriction sector
between the two literal endpoints.  Any such vertex would lie on a second
configuration line, contradicting strict realization of its sign. -/
theorem no_vertex_in_open_edgeSector
    (e : ProjectiveStrictEdge pick (normals B))
    (v : Vertex B) (hvowner : OnLine B v e.1.1.1) :
    ¬ ∃ t : ℝ,
      letI := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
      let D := edgeEndpointData B ha hb hc hncol pick e
      lowerEndpoint
          (otherNormals (normals B) e.1.1.1) e.1.1.2
          (normals B e.1.1.1) (edgeWitness B pick e) D.lower_nonempty < t ∧
        t < upperEndpoint
          (otherNormals (normals B) e.1.1.1) e.1.1.2
          (normals B e.1.1.1) (edgeWitness B pick e) D.upper_nonempty ∧
        Projectivization.mk ℝ
            (chartPoint
              (otherNormals (normals B) e.1.1.1) e.1.1.2
              (normals B e.1.1.1) (edgeWitness B pick e) t)
            (chartPoint_ne_zero (edgeWitness_realizes B pick e) t) = v.1 := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  rintro ⟨t, hlt, htu, hproj⟩
  have hreal : Realizes (otherNormals (normals B) e.1.1.1) e.1.1.2
      (chartPoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e) t) :=
    (D.realizes_iff t).2 ⟨hlt, htu⟩
  obtain ⟨j, hjne, hvj⟩ :=
    exists_other_incident_line B v e.1.1.1
  let jj : {j : Line B // j ≠ e.1.1.1} := ⟨j, hjne⟩
  have hz : otherNormals (normals B) e.1.1.1 jj ⬝ᵥ
      chartPoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e) t = 0 := by
    change normalVec j.1 ⬝ᵥ
      chartPoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e) t = 0
    apply (onProjectiveLine_mk_iff _ _
      (chartPoint_ne_zero (edgeWitness_realizes B pick e) t)).mp
    rw [hproj]
    exact hvj
  have hpos := hreal jj
  rw [hz] at hpos
  cases hs : e.1.1.2 jj <;> simp [signed, hs] at hpos

def lowerEdgeParameter (e : ProjectiveStrictEdge pick (normals B)) : ℝ := by
  letI := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  exact lowerEndpoint
    (otherNormals (normals B) e.1.1.1) e.1.1.2
    (normals B e.1.1.1) (edgeWitness B pick e) D.lower_nonempty

def upperEdgeParameter (e : ProjectiveStrictEdge pick (normals B)) : ℝ := by
  letI := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  exact upperEndpoint
    (otherNormals (normals B) e.1.1.1) e.1.1.2
    (normals B e.1.1.1) (edgeWitness B pick e) D.upper_nonempty

def lowerEdgeRaw (e : ProjectiveStrictEdge pick (normals B)) : Vec3 :=
  chartPoint (otherNormals (normals B) e.1.1.1) e.1.1.2
    (normals B e.1.1.1) (edgeWitness B pick e)
    (lowerEdgeParameter B ha hb hc hncol pick e)

def upperEdgeRaw (e : ProjectiveStrictEdge pick (normals B)) : Vec3 :=
  chartPoint (otherNormals (normals B) e.1.1.1) e.1.1.2
    (normals B e.1.1.1) (edgeWitness B pick e)
    (upperEdgeParameter B ha hb hc hncol pick e)

/-- If the two literal sector endpoints have chart values of the same sign,
then no arrangement vertex lies strictly between their global chart
coordinates.  This is the central chart-invariance bridge: affine
interpolation in the global chart pulls back to an interior parameter of the
literal restriction sector. -/
theorem no_vertex_between_edgeEndpoints_of_sameSign
    (e : ProjectiveStrictEdge pick (normals B))
    (v : Vertex B) (hvowner : OnLine B v e.1.1.1)
    (hbetween :
      (vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e) < vertexCoord B v ∧
        vertexCoord B v < vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e)) ∨
      (vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e) < vertexCoord B v ∧
        vertexCoord B v < vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e))) :
    0 < chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
        chartF B (upperEdgeRaw B ha hb hc hncol pick e) → False := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  let l := lowerEdgeParameter B ha hb hc hncol pick e
  let u := upperEdgeParameter B ha hb hc hncol pick e
  let yl := lowerEdgeRaw B ha hb hc hncol pick e
  let yu := upperEdgeRaw B ha hb hc hncol pick e
  intro hsame
  let p := lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e
  let q := upperEdgeProjectiveEndpoint B ha hb hc hncol pick e
  let f := chartF B
  let g := chartG B
  have hyl : yl ≠ 0 := by
    exact chartPoint_ne_zero (edgeWitness_realizes B pick e) l
  have hyu : yu ≠ 0 := by
    exact chartPoint_ne_zero (edgeWitness_realizes B pick e) u
  have hp_mk : p = Projectivization.mk ℝ yl hyl := by
    rfl
  have hq_mk : q = Projectivization.mk ℝ yu hyu := by
    rfl
  have hfp : f p.rep ≠ 0 :=
    (chart_spec B).1 p (lowerEdgeProjectiveEndpoint_mem_projectiveVertices
      B ha hb hc hncol pick e)
  have hfq : f q.rep ≠ 0 :=
    (chart_spec B).1 q (upperEdgeProjectiveEndpoint_mem_projectiveVertices
      B ha hb hc hncol pick e)
  have hfv : f v.1.rep ≠ 0 := (chart_spec B).1 v.1 v.2
  have hfyl : f yl ≠ 0 := by
    intro hz
    apply hfp
    apply (apply_rep_mk_eq_zero_iff f yl hyl).2
    simpa [hp_mk] using hz
  have hfyu : f yu ≠ 0 := by
    intro hz
    apply hfq
    apply (apply_rep_mk_eq_zero_iff f yu hyu).2
    simpa [hq_mk] using hz
  let cp := chartCoord f g p
  let cq := chartCoord f g q
  let cv := chartCoord f g v.1
  have hbetween' : (cp < cv ∧ cv < cq) ∨ (cq < cv ∧ cv < cp) := hbetween
  have hpq : cp ≠ cq := by
    rcases hbetween' with h | h
    · exact ne_of_lt (h.1.trans h.2)
    · exact ne_of_gt (h.1.trans h.2)
  let r := (cv - cp) / (cq - cp)
  have hden : cq - cp ≠ 0 := sub_ne_zero.mpr hpq.symm
  have hrpos : 0 < r := by
    rcases hbetween' with h | h
    · exact div_pos (sub_pos.mpr h.1) (sub_pos.mpr (h.1.trans h.2))
    · exact div_pos_of_neg_of_neg (sub_neg.mpr h.2)
        (sub_neg.mpr (h.1.trans h.2))
  have hrlt : r < 1 := by
    rcases hbetween' with h | h
    · apply (div_lt_one (sub_pos.mpr (h.1.trans h.2))).2
      linarith
    · apply (div_lt_iff_of_neg (sub_neg.mpr (h.1.trans h.2))).2
      linarith
  have hcoord : cv = (1 - r) * cp + r * cq := by
    dsimp [r]
    field_simp [hden]
    ring
  have hpowner : OnProjectiveLine (normals B e.1.1.1) p :=
    lowerEdgeProjectiveEndpoint_on_owner B ha hb hc hncol pick e
  have hqowner : OnProjectiveLine (normals B e.1.1.1) q :=
    upperEdgeProjectiveEndpoint_on_owner B ha hb hc hncol pick e
  obtain ⟨hz, hvz⟩ := eq_mk_chartRep_interpolation
    (normals_ne_zero B e.1.1.1) f g hfp hfq hfv hpowner hqowner hvowner
    hpq r (by simpa [cp, cq, cv] using hcoord)
  let A := (1 - r) * (f yl)⁻¹
  let C := r * (f yu)⁻¹
  have hchartp : chartRep f p = (f yl)⁻¹ • yl := by
    rw [hp_mk]
    exact chartRep_mk_eq_inv_smul f hyl hfyl
  have hchartq : chartRep f q = (f yu)⁻¹ • yu := by
    rw [hq_mk]
    exact chartRep_mk_eq_inv_smul f hyu hfyu
  have hzform :
      (1 - r) • chartRep f p + r • chartRep f q = A • yl + C • yu := by
    rw [hchartp, hchartq]
    simp only [smul_smul]
    rfl
  have hinvprod : 0 < (f yl)⁻¹ * (f yu)⁻¹ := by
    rw [← mul_inv]
    exact inv_pos.mpr hsame
  have hAC : 0 < A * C := by
    calc
      A * C = ((1 - r) * r) * ((f yl)⁻¹ * (f yu)⁻¹) := by
        simp only [A, C]
        ring
      _ > 0 := mul_pos (mul_pos (sub_pos.mpr hrlt) hrpos) hinvprod
  have hsum : A + C ≠ 0 := by
    intro hzero
    have : C = -A := by linarith
    rw [this] at hAC
    nlinarith [sq_nonneg A]
  let t := (A * l + C * u) / (A + C)
  have hltu : l < u := D.lower_lt_upper
  have ht := sameSign_weightedParameter_between hltu hAC
  change l < t ∧ t < u at ht
  have hraw : A • yl + C • yu = (A + C) •
      chartPoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e) t := by
    exact weighted_chartPoint_identity
      (edgeWitness B pick e)
      (direction (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1)) l u A C hsum
  have hproj : Projectivization.mk ℝ
      ((1 - r) • chartRep f p + r • chartRep f q) hz =
      Projectivization.mk ℝ
        (chartPoint
          (otherNormals (normals B) e.1.1.1) e.1.1.2
          (normals B e.1.1.1) (edgeWitness B pick e) t)
        (chartPoint_ne_zero (edgeWitness_realizes B pick e) t) := by
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hz
      (chartPoint_ne_zero (edgeWitness_realizes B pick e) t)).2
    exact ⟨A + C, by rw [hzform, hraw]⟩
  apply no_vertex_in_open_edgeSector B ha hb hc hncol pick e v hvowner
  exact ⟨t, ht.1, ht.2, hproj.symm.trans hvz.symm⟩

/-- When the global affine chart has no pole in the literal restriction
sector, its two endpoints are an ordinary consecutive pair (in whichever
coordinate orientation they occur). -/
theorem edgeEndpoints_cyclicConsecutive_of_sameSign
    (e : ProjectiveStrictEdge pick (normals B))
    (hsame : 0 < chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
      chartF B (upperEdgeRaw B ha hb hc hncol pick e)) :
    CyclicConsecutive (vertexCoord B)
        (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
        (lowerEdgeVertex B ha hb hc hncol pick e)
        (upperEdgeVertex B ha hb hc hncol pick e) ∨
      CyclicConsecutive (vertexCoord B)
        (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
        (upperEdgeVertex B ha hb hc hncol pick e)
        (lowerEdgeVertex B ha hb hc hncol pick e) := by
  let S := verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1
  let vl := lowerEdgeVertex B ha hb hc hncol pick e
  let vu := upperEdgeVertex B ha hb hc hncol pick e
  have hvl : vl ∈ S := lowerEdgeVertex_mem_verticesOn B ha hb hc hncol pick e
  have hvu : vu ∈ S := upperEdgeVertex_mem_verticesOn B ha hb hc hncol pick e
  have hcoordne : vertexCoord B vl ≠ vertexCoord B vu := by
    intro h
    exact lowerEdgeVertex_ne_upperEdgeVertex B ha hb hc hncol pick e <|
      vertexCoord_injective B (Finset.mem_univ vl) (Finset.mem_univ vu) h
  rcases lt_or_gt_of_ne hcoordne with hlu | hul
  · left
    left
    refine ⟨hvl, hvu, hlu, ?_⟩
    intro v hv hvbetween
    have hvowner : OnLine B v e.1.1.1 := (mem_verticesOn _ _).mp hv |>.2
    exact no_vertex_between_edgeEndpoints_of_sameSign
      B ha hb hc hncol pick e v hvowner (Or.inl hvbetween) hsame
  · right
    left
    refine ⟨hvu, hvl, hul, ?_⟩
    intro v hv hvbetween
    have hvowner : OnLine B v e.1.1.1 := (mem_verticesOn _ _).mp hv |>.2
    exact no_vertex_between_edgeEndpoints_of_sameSign
      B ha hb hc hncol pick e v hvowner (Or.inr hvbetween) hsame

/-- The reusable interpolation core.  Whenever the two normalized endpoint
coefficients have the same sign, the interpolated projective point lies in
the literal open restriction sector and hence cannot be an arrangement
vertex. -/
theorem no_vertex_of_positive_edgeInterpolation
    (e : ProjectiveStrictEdge pick (normals B))
    (v : Vertex B) (hvowner : OnLine B v e.1.1.1)
    (r : ℝ)
    (hpq : vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e) ≠
      vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e))
    (hcoord : vertexCoord B v =
      (1 - r) * vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e) +
        r * vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e))
    (hcoeff : 0 <
      ((1 - r) * (chartF B (lowerEdgeRaw B ha hb hc hncol pick e))⁻¹) *
        (r * (chartF B (upperEdgeRaw B ha hb hc hncol pick e))⁻¹)) : False := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  let l := lowerEdgeParameter B ha hb hc hncol pick e
  let u := upperEdgeParameter B ha hb hc hncol pick e
  let yl := lowerEdgeRaw B ha hb hc hncol pick e
  let yu := upperEdgeRaw B ha hb hc hncol pick e
  let p := lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e
  let q := upperEdgeProjectiveEndpoint B ha hb hc hncol pick e
  let f := chartF B
  let g := chartG B
  have hyl : yl ≠ 0 := chartPoint_ne_zero (edgeWitness_realizes B pick e) l
  have hyu : yu ≠ 0 := chartPoint_ne_zero (edgeWitness_realizes B pick e) u
  have hp_mk : p = Projectivization.mk ℝ yl hyl := by rfl
  have hq_mk : q = Projectivization.mk ℝ yu hyu := by rfl
  have hfp : f p.rep ≠ 0 :=
    (chart_spec B).1 p (lowerEdgeProjectiveEndpoint_mem_projectiveVertices
      B ha hb hc hncol pick e)
  have hfq : f q.rep ≠ 0 :=
    (chart_spec B).1 q (upperEdgeProjectiveEndpoint_mem_projectiveVertices
      B ha hb hc hncol pick e)
  have hfv : f v.1.rep ≠ 0 := (chart_spec B).1 v.1 v.2
  have hfyl : f yl ≠ 0 := by
    intro hz
    apply hfp
    apply (apply_rep_mk_eq_zero_iff f yl hyl).2
    simpa [hp_mk] using hz
  have hfyu : f yu ≠ 0 := by
    intro hz
    apply hfq
    apply (apply_rep_mk_eq_zero_iff f yu hyu).2
    simpa [hq_mk] using hz
  have hpowner : OnProjectiveLine (normals B e.1.1.1) p :=
    lowerEdgeProjectiveEndpoint_on_owner B ha hb hc hncol pick e
  have hqowner : OnProjectiveLine (normals B e.1.1.1) q :=
    upperEdgeProjectiveEndpoint_on_owner B ha hb hc hncol pick e
  obtain ⟨hz, hvz⟩ := eq_mk_chartRep_interpolation
    (normals_ne_zero B e.1.1.1) f g hfp hfq hfv hpowner hqowner hvowner
    hpq r (by
      simpa [p, q, f, g, vertexCoord, lowerEdgeVertex, upperEdgeVertex] using hcoord)
  let A := (1 - r) * (f yl)⁻¹
  let C := r * (f yu)⁻¹
  have hchartp : chartRep f p = (f yl)⁻¹ • yl := by
    rw [hp_mk]
    exact chartRep_mk_eq_inv_smul f hyl hfyl
  have hchartq : chartRep f q = (f yu)⁻¹ • yu := by
    rw [hq_mk]
    exact chartRep_mk_eq_inv_smul f hyu hfyu
  have hzform :
      (1 - r) • chartRep f p + r • chartRep f q = A • yl + C • yu := by
    rw [hchartp, hchartq]
    simp only [smul_smul]
    rfl
  have hAC : 0 < A * C := hcoeff
  have hsum : A + C ≠ 0 := by
    intro hzero
    have : C = -A := by linarith
    rw [this] at hAC
    nlinarith [sq_nonneg A]
  let t := (A * l + C * u) / (A + C)
  have hltu : l < u := D.lower_lt_upper
  have ht := sameSign_weightedParameter_between hltu hAC
  change l < t ∧ t < u at ht
  have hraw : A • yl + C • yu = (A + C) •
      chartPoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e) t := by
    exact weighted_chartPoint_identity
      (edgeWitness B pick e)
      (direction (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1)) l u A C hsum
  have hproj : Projectivization.mk ℝ
      ((1 - r) • chartRep f p + r • chartRep f q) hz =
      Projectivization.mk ℝ
        (chartPoint
          (otherNormals (normals B) e.1.1.1) e.1.1.2
          (normals B e.1.1.1) (edgeWitness B pick e) t)
        (chartPoint_ne_zero (edgeWitness_realizes B pick e) t) := by
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hz
      (chartPoint_ne_zero (edgeWitness_realizes B pick e) t)).2
    exact ⟨A + C, by rw [hzform, hraw]⟩
  apply no_vertex_in_open_edgeSector B ha hb hc hncol pick e v hvowner
  exact ⟨t, ht.1, ht.2, hproj.symm.trans hvz.symm⟩

/-- If the chart pole lies in the literal sector, no vertex can lie outside
the coordinate interval bounded by its two endpoints. -/
theorem no_vertex_outside_edgeEndpoints_of_oppositeSign
    (e : ProjectiveStrictEdge pick (normals B))
    (v : Vertex B) (hvowner : OnLine B v e.1.1.1)
    (houtside :
      (vertexCoord B v < vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e) ∧
        vertexCoord B v < vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e)) ∨
      (vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e) < vertexCoord B v ∧
        vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e) < vertexCoord B v))
    (hopposite : chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
      chartF B (upperEdgeRaw B ha hb hc hncol pick e) < 0) : False := by
  let cp := vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e)
  let cq := vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e)
  let cv := vertexCoord B v
  have houtside' : (cv < cp ∧ cv < cq) ∨ (cp < cv ∧ cq < cv) := houtside
  have hpq : cp ≠ cq := by
    intro h
    exact lowerEdgeVertex_ne_upperEdgeVertex B ha hb hc hncol pick e <|
      vertexCoord_injective B (Finset.mem_univ _) (Finset.mem_univ _) h
  let r := (cv - cp) / (cq - cp)
  have hrouter : r < 0 ∨ 1 < r := by
    rcases lt_or_gt_of_ne hpq with hcpq | hqcp
    · rcases houtside' with hbelow | habove
      · left
        exact div_neg_of_neg_of_pos (sub_neg.mpr hbelow.1) (sub_pos.mpr hcpq)
      · right
        exact (one_lt_div (sub_pos.mpr hcpq)).2 (by linarith)
    · rcases houtside' with hbelow | habove
      · right
        exact (one_lt_div_of_neg (sub_neg.mpr hqcp)).2 (by linarith)
      · left
        exact div_neg_of_pos_of_neg (sub_pos.mpr habove.1) (sub_neg.mpr hqcp)
  have hcoord : cv = (1 - r) * cp + r * cq := by
    have hden : cq - cp ≠ 0 := sub_ne_zero.mpr hpq.symm
    dsimp [r]
    field_simp [hden]
    ring
  have hrprodneg : (1 - r) * r < 0 := by
    rcases hrouter with hr | hr
    · exact mul_neg_of_pos_of_neg (by linarith) hr
    · exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hinvprodneg :
      (chartF B (lowerEdgeRaw B ha hb hc hncol pick e))⁻¹ *
        (chartF B (upperEdgeRaw B ha hb hc hncol pick e))⁻¹ < 0 := by
    rw [← mul_inv]
    exact inv_lt_zero.mpr hopposite
  have hcoeff : 0 <
      ((1 - r) * (chartF B (lowerEdgeRaw B ha hb hc hncol pick e))⁻¹) *
        (r * (chartF B (upperEdgeRaw B ha hb hc hncol pick e))⁻¹) := by
    calc
      _ = ((1 - r) * r) *
          ((chartF B (lowerEdgeRaw B ha hb hc hncol pick e))⁻¹ *
            (chartF B (upperEdgeRaw B ha hb hc hncol pick e))⁻¹) := by ring
      _ > 0 := mul_pos_of_neg_of_neg hrprodneg hinvprodneg
  exact no_vertex_of_positive_edgeInterpolation B ha hb hc hncol pick e v hvowner r
    hpq (by simpa [cp, cq, cv] using hcoord) hcoeff

theorem edgeEndpoints_cyclicConsecutive_of_oppositeSign
    (e : ProjectiveStrictEdge pick (normals B))
    (hopposite : chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
      chartF B (upperEdgeRaw B ha hb hc hncol pick e) < 0) :
    CyclicConsecutive (vertexCoord B)
        (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
        (lowerEdgeVertex B ha hb hc hncol pick e)
        (upperEdgeVertex B ha hb hc hncol pick e) ∨
      CyclicConsecutive (vertexCoord B)
        (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
        (upperEdgeVertex B ha hb hc hncol pick e)
        (lowerEdgeVertex B ha hb hc hncol pick e) := by
  let S := verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1
  let vl := lowerEdgeVertex B ha hb hc hncol pick e
  let vu := upperEdgeVertex B ha hb hc hncol pick e
  have hvl : vl ∈ S := lowerEdgeVertex_mem_verticesOn B ha hb hc hncol pick e
  have hvu : vu ∈ S := upperEdgeVertex_mem_verticesOn B ha hb hc hncol pick e
  have hcoordne : vertexCoord B vl ≠ vertexCoord B vu := by
    intro h
    exact lowerEdgeVertex_ne_upperEdgeVertex B ha hb hc hncol pick e <|
      vertexCoord_injective B (Finset.mem_univ vl) (Finset.mem_univ vu) h
  rcases lt_or_gt_of_ne hcoordne with hlu | hul
  · right
    right
    refine ⟨hvu, hvl, ?_, ?_⟩
    · intro v hv
      apply le_of_not_gt
      intro hvu_lt
      have hvowner : OnLine B v e.1.1.1 := (mem_verticesOn _ _).mp hv |>.2
      exact no_vertex_outside_edgeEndpoints_of_oppositeSign
        B ha hb hc hncol pick e v hvowner
          (Or.inr ⟨hlu.trans hvu_lt, hvu_lt⟩) hopposite
    · intro v hv
      apply le_of_not_gt
      intro hv_lt
      have hvowner : OnLine B v e.1.1.1 := (mem_verticesOn _ _).mp hv |>.2
      exact no_vertex_outside_edgeEndpoints_of_oppositeSign
        B ha hb hc hncol pick e v hvowner
          (Or.inl ⟨hv_lt, hv_lt.trans hlu⟩) hopposite
  · left
    right
    refine ⟨hvl, hvu, ?_, ?_⟩
    · intro v hv
      apply le_of_not_gt
      intro hvl_lt
      have hvowner : OnLine B v e.1.1.1 := (mem_verticesOn _ _).mp hv |>.2
      exact no_vertex_outside_edgeEndpoints_of_oppositeSign
        B ha hb hc hncol pick e v hvowner
          (Or.inr ⟨hvl_lt, hul.trans hvl_lt⟩) hopposite
    · intro v hv
      apply le_of_not_gt
      intro hv_lt
      have hvowner : OnLine B v e.1.1.1 := (mem_verticesOn _ _).mp hv |>.2
      exact no_vertex_outside_edgeEndpoints_of_oppositeSign
        B ha hb hc hncol pick e v hvowner
          (Or.inl ⟨hv_lt.trans hul, hv_lt⟩) hopposite

theorem chartF_lowerEdgeRaw_ne_zero
    (e : ProjectiveStrictEdge pick (normals B)) :
    chartF B (lowerEdgeRaw B ha hb hc hncol pick e) ≠ 0 := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let yl := lowerEdgeRaw B ha hb hc hncol pick e
  have hyl : yl ≠ 0 := chartPoint_ne_zero (edgeWitness_realizes B pick e)
    (lowerEdgeParameter B ha hb hc hncol pick e)
  have hfp := (chart_spec B).1
    (lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e)
    (lowerEdgeProjectiveEndpoint_mem_projectiveVertices B ha hb hc hncol pick e)
  intro hz
  apply hfp
  apply (apply_rep_mk_eq_zero_iff (chartF B) yl hyl).2
  simpa [yl] using hz

theorem chartF_upperEdgeRaw_ne_zero
    (e : ProjectiveStrictEdge pick (normals B)) :
    chartF B (upperEdgeRaw B ha hb hc hncol pick e) ≠ 0 := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let yu := upperEdgeRaw B ha hb hc hncol pick e
  have hyu : yu ≠ 0 := chartPoint_ne_zero (edgeWitness_realizes B pick e)
    (upperEdgeParameter B ha hb hc hncol pick e)
  have hfq := (chart_spec B).1
    (upperEdgeProjectiveEndpoint B ha hb hc hncol pick e)
    (upperEdgeProjectiveEndpoint_mem_projectiveVertices B ha hb hc hncol pick e)
  intro hz
  apply hfq
  apply (apply_rep_mk_eq_zero_iff (chartF B) yu hyu).2
  simpa [yu] using hz

/-- The two genuine endpoints of every projective strict edge form one of
the two orientations of a cyclic-consecutive projective arrangement edge. -/
theorem edgeEndpoints_cyclicConsecutive
    (e : ProjectiveStrictEdge pick (normals B)) :
    CyclicConsecutive (vertexCoord B)
        (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
        (lowerEdgeVertex B ha hb hc hncol pick e)
        (upperEdgeVertex B ha hb hc hncol pick e) ∨
      CyclicConsecutive (vertexCoord B)
        (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
        (upperEdgeVertex B ha hb hc hncol pick e)
        (lowerEdgeVertex B ha hb hc hncol pick e) := by
  let z := chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
    chartF B (upperEdgeRaw B ha hb hc hncol pick e)
  rcases lt_trichotomy 0 z with hz | hz | hz
  · exact edgeEndpoints_cyclicConsecutive_of_sameSign B ha hb hc hncol pick e hz
  · exfalso
    rcases mul_eq_zero.mp hz.symm with h | h
    · exact chartF_lowerEdgeRaw_ne_zero B ha hb hc hncol pick e h
    · exact chartF_upperEdgeRaw_ne_zero B ha hb hc hncol pick e h
  · exact edgeEndpoints_cyclicConsecutive_of_oppositeSign B ha hb hc hncol pick e hz

theorem lower_upper_cyclicConsecutive_of_sameSign_of_lt
    (e : ProjectiveStrictEdge pick (normals B))
    (hsame : 0 < chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
      chartF B (upperEdgeRaw B ha hb hc hncol pick e))
    (hlt : vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e) <
      vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e)) :
    CyclicConsecutive (vertexCoord B)
      (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
      (lowerEdgeVertex B ha hb hc hncol pick e)
      (upperEdgeVertex B ha hb hc hncol pick e) := by
  left
  refine ⟨lowerEdgeVertex_mem_verticesOn B ha hb hc hncol pick e,
    upperEdgeVertex_mem_verticesOn B ha hb hc hncol pick e, hlt, ?_⟩
  intro v hv hvbetween
  exact no_vertex_between_edgeEndpoints_of_sameSign B ha hb hc hncol pick e v
    ((mem_verticesOn _ _).mp hv).2 (Or.inl hvbetween) hsame

theorem upper_lower_cyclicConsecutive_of_sameSign_of_lt
    (e : ProjectiveStrictEdge pick (normals B))
    (hsame : 0 < chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
      chartF B (upperEdgeRaw B ha hb hc hncol pick e))
    (hlt : vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e) <
      vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e)) :
    CyclicConsecutive (vertexCoord B)
      (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
      (upperEdgeVertex B ha hb hc hncol pick e)
      (lowerEdgeVertex B ha hb hc hncol pick e) := by
  left
  refine ⟨upperEdgeVertex_mem_verticesOn B ha hb hc hncol pick e,
    lowerEdgeVertex_mem_verticesOn B ha hb hc hncol pick e, hlt, ?_⟩
  intro v hv hvbetween
  exact no_vertex_between_edgeEndpoints_of_sameSign B ha hb hc hncol pick e v
    ((mem_verticesOn _ _).mp hv).2 (Or.inr hvbetween) hsame

theorem upper_lower_cyclicConsecutive_of_oppositeSign_of_lt
    (e : ProjectiveStrictEdge pick (normals B))
    (hopposite : chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
      chartF B (upperEdgeRaw B ha hb hc hncol pick e) < 0)
    (hlt : vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e) <
      vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e)) :
    CyclicConsecutive (vertexCoord B)
      (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
      (upperEdgeVertex B ha hb hc hncol pick e)
      (lowerEdgeVertex B ha hb hc hncol pick e) := by
  right
  refine ⟨upperEdgeVertex_mem_verticesOn B ha hb hc hncol pick e,
    lowerEdgeVertex_mem_verticesOn B ha hb hc hncol pick e, ?_, ?_⟩
  · intro v hv
    apply le_of_not_gt
    intro hvu
    exact no_vertex_outside_edgeEndpoints_of_oppositeSign B ha hb hc hncol pick e v
      ((mem_verticesOn _ _).mp hv).2 (Or.inr ⟨hlt.trans hvu, hvu⟩) hopposite
  · intro v hv
    apply le_of_not_gt
    intro hvl
    exact no_vertex_outside_edgeEndpoints_of_oppositeSign B ha hb hc hncol pick e v
      ((mem_verticesOn _ _).mp hv).2 (Or.inl ⟨hvl, hvl.trans hlt⟩) hopposite

theorem lower_upper_cyclicConsecutive_of_oppositeSign_of_lt
    (e : ProjectiveStrictEdge pick (normals B))
    (hopposite : chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
      chartF B (upperEdgeRaw B ha hb hc hncol pick e) < 0)
    (hlt : vertexCoord B (upperEdgeVertex B ha hb hc hncol pick e) <
      vertexCoord B (lowerEdgeVertex B ha hb hc hncol pick e)) :
    CyclicConsecutive (vertexCoord B)
      (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
      (lowerEdgeVertex B ha hb hc hncol pick e)
      (upperEdgeVertex B ha hb hc hncol pick e) := by
  right
  refine ⟨lowerEdgeVertex_mem_verticesOn B ha hb hc hncol pick e,
    upperEdgeVertex_mem_verticesOn B ha hb hc hncol pick e, ?_, ?_⟩
  · intro v hv
    apply le_of_not_gt
    intro hvl
    exact no_vertex_outside_edgeEndpoints_of_oppositeSign B ha hb hc hncol pick e v
      ((mem_verticesOn _ _).mp hv).2 (Or.inr ⟨hvl, hlt.trans hvl⟩) hopposite
  · intro v hv
    apply le_of_not_gt
    intro hvu
    exact no_vertex_outside_edgeEndpoints_of_oppositeSign B ha hb hc hncol pick e v
      ((mem_verticesOn _ _).mp hv).2 (Or.inl ⟨hvu.trans hlt, hvu⟩) hopposite

/-- The canonical genuine cyclic edge associated to a projective strict
restriction sector.  Its start is chosen so that its cyclic successor is the
other literal sector endpoint. -/
noncomputable def projectiveStrictEdgeToCyclic
    (e : ProjectiveStrictEdge pick (normals B)) :
    CyclicSkeletonEdge (Finset.univ : Finset (Vertex B)) (OnLine B) := by
  let vl := lowerEdgeVertex B ha hb hc hncol pick e
  let vu := upperEdgeVertex B ha hb hc hncol pick e
  let z := chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
    chartF B (upperEdgeRaw B ha hb hc hncol pick e)
  exact if hpos : 0 < z then
    if hlt : vertexCoord B vl < vertexCoord B vu then
      ⟨e.1.1.1, ⟨vl,
        (lower_upper_cyclicConsecutive_of_sameSign_of_lt
          B ha hb hc hncol pick e hpos hlt).left_mem⟩⟩
    else by
      have hne : vertexCoord B vl ≠ vertexCoord B vu := fun h ↦
        lowerEdgeVertex_ne_upperEdgeVertex B ha hb hc hncol pick e <|
          vertexCoord_injective B (Finset.mem_univ vl) (Finset.mem_univ vu) h
      have hgt : vertexCoord B vu < vertexCoord B vl :=
        lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      exact ⟨e.1.1.1, ⟨vu,
        (upper_lower_cyclicConsecutive_of_sameSign_of_lt
          B ha hb hc hncol pick e hpos hgt).left_mem⟩⟩
  else by
    have hz : z ≠ 0 := mul_ne_zero
      (chartF_lowerEdgeRaw_ne_zero B ha hb hc hncol pick e)
      (chartF_upperEdgeRaw_ne_zero B ha hb hc hncol pick e)
    have hneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hz
    exact if hlt : vertexCoord B vl < vertexCoord B vu then
      ⟨e.1.1.1, ⟨vu,
        (upper_lower_cyclicConsecutive_of_oppositeSign_of_lt
          B ha hb hc hncol pick e hneg hlt).left_mem⟩⟩
    else by
      have hne : vertexCoord B vl ≠ vertexCoord B vu := fun h ↦
        lowerEdgeVertex_ne_upperEdgeVertex B ha hb hc hncol pick e <|
          vertexCoord_injective B (Finset.mem_univ vl) (Finset.mem_univ vu) h
      have hgt : vertexCoord B vu < vertexCoord B vl :=
        lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
      exact ⟨e.1.1.1, ⟨vl,
        (lower_upper_cyclicConsecutive_of_oppositeSign_of_lt
          B ha hb hc hncol pick e hneg hgt).left_mem⟩⟩

@[simp] theorem projectiveStrictEdgeToCyclic_line
    (e : ProjectiveStrictEdge pick (normals B)) :
    (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e).1 = e.1.1.1 := by
  unfold projectiveStrictEdgeToCyclic
  dsimp only
  split <;> split <;> rfl

/-- The canonical cyclic edge has precisely the two genuine geometric
endpoints extracted from the strict restriction sector. -/
theorem projectiveStrictEdgeToCyclic_vertices
    (e : ProjectiveStrictEdge pick (normals B)) :
    cyclicEdgeVertices (Finset.univ : Finset (Vertex B)) (OnLine B)
        (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) =
      {lowerEdgeVertex B ha hb hc hncol pick e,
        upperEdgeVertex B ha hb hc hncol pick e} := by
  let vl := lowerEdgeVertex B ha hb hc hncol pick e
  let vu := upperEdgeVertex B ha hb hc hncol pick e
  let S := verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1
  have hinj : Set.InjOn (vertexCoord B) (S : Set (Vertex B)) :=
    (vertexCoord_injective B).mono (Finset.filter_subset _ _)
  let z := chartF B (lowerEdgeRaw B ha hb hc hncol pick e) *
    chartF B (upperEdgeRaw B ha hb hc hncol pick e)
  have hcoordne : vertexCoord B vl ≠ vertexCoord B vu := fun h ↦
    lowerEdgeVertex_ne_upperEdgeVertex B ha hb hc hncol pick e <|
      vertexCoord_injective B (Finset.mem_univ vl) (Finset.mem_univ vu) h
  have finish_eq (x y : Vertex B)
      (hxy : CyclicConsecutive (vertexCoord B) S x y)
      (hstart : cyclicEdgeStart
        (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = x) :
      cyclicEdgeFinish (Finset.univ : Finset (Vertex B)) (OnLine B)
        (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = y := by
    have hspec := cyclicEdgeFinish_spec (Finset.univ : Finset (Vertex B)) (OnLine B)
      (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e)
    rw [projectiveStrictEdgeToCyclic_line B ha hb hc hncol pick e, hstart] at hspec
    exact (cyclicConsecutive_right_unique (vertexCoord B) S hinj hxy hspec).symm
  by_cases hpos : 0 < z
  · by_cases hlt : vertexCoord B vl < vertexCoord B vu
    · have hcyc : CyclicConsecutive (vertexCoord B) S vl vu := by
        exact lower_upper_cyclicConsecutive_of_sameSign_of_lt
          B ha hb hc hncol pick e hpos hlt
      have hstart : cyclicEdgeStart
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vl := by
        unfold projectiveStrictEdgeToCyclic
        dsimp only
        rw [dif_pos hpos, dif_pos hlt]
        rfl
      rw [cyclicEdgeVertices, hstart, finish_eq vl vu hcyc hstart]

    · have hgt : vertexCoord B vu < vertexCoord B vl :=
        lt_of_le_of_ne (le_of_not_gt hlt) hcoordne.symm
      have hcyc : CyclicConsecutive (vertexCoord B) S vu vl := by
        exact upper_lower_cyclicConsecutive_of_sameSign_of_lt
          B ha hb hc hncol pick e hpos hgt
      have hstart : cyclicEdgeStart
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vu := by
        unfold projectiveStrictEdgeToCyclic
        dsimp only
        rw [dif_pos hpos, dif_neg hlt]
        rfl
      rw [cyclicEdgeVertices, hstart, finish_eq vu vl hcyc hstart, Finset.pair_comm]
  · have hz : z ≠ 0 := mul_ne_zero
        (chartF_lowerEdgeRaw_ne_zero B ha hb hc hncol pick e)
        (chartF_upperEdgeRaw_ne_zero B ha hb hc hncol pick e)
    have hneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hz
    by_cases hlt : vertexCoord B vl < vertexCoord B vu
    · have hcyc : CyclicConsecutive (vertexCoord B) S vu vl := by
        exact upper_lower_cyclicConsecutive_of_oppositeSign_of_lt
          B ha hb hc hncol pick e hneg hlt
      have hstart : cyclicEdgeStart
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vu := by
        unfold projectiveStrictEdgeToCyclic
        dsimp only
        rw [dif_neg hpos, dif_pos hlt]
        rfl
      rw [cyclicEdgeVertices, hstart, finish_eq vu vl hcyc hstart, Finset.pair_comm]
    · have hgt : vertexCoord B vu < vertexCoord B vl :=
        lt_of_le_of_ne (le_of_not_gt hlt) hcoordne.symm
      have hcyc : CyclicConsecutive (vertexCoord B) S vl vu := by
        exact lower_upper_cyclicConsecutive_of_oppositeSign_of_lt
          B ha hb hc hncol pick e hneg hgt
      have hstart : cyclicEdgeStart
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vl := by
        unfold projectiveStrictEdgeToCyclic
        dsimp only
        rw [dif_neg hpos, dif_neg hlt]
        rfl
      rw [cyclicEdgeVertices, hstart, finish_eq vl vu hcyc hstart]

/-- The cyclic successor is determined once the genuine start and its
geometric successor proof are known. -/
theorem projectiveStrictEdgeToCyclic_finish_eq_of_start_eq
    (e : ProjectiveStrictEdge pick (normals B)) (x y : Vertex B)
    (hxy : CyclicConsecutive (vertexCoord B)
      (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1) x y)
    (hstart : cyclicEdgeStart
      (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = x) :
    cyclicEdgeFinish (Finset.univ : Finset (Vertex B)) (OnLine B)
      (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = y := by
  let S := verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1
  have hinj : Set.InjOn (vertexCoord B) (S : Set (Vertex B)) :=
    (vertexCoord_injective B).mono (Finset.filter_subset _ _)
  have hspec := cyclicEdgeFinish_spec (Finset.univ : Finset (Vertex B)) (OnLine B)
    (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e)
  rw [projectiveStrictEdgeToCyclic_line B ha hb hc hncol pick e, hstart] at hspec
  exact (cyclicConsecutive_right_unique (vertexCoord B) S hinj hxy hspec).symm

/-- A canonical affine-chart vector in the interior of a projective cyclic
edge.  Ordinary edges use the sum of the normalized endpoint
representatives; the wrap edge uses their difference. -/
noncomputable def cyclicInteriorRaw
    (c : CyclicSkeletonEdge (Finset.univ : Finset (Vertex B)) (OnLine B)) : Vec3 :=
  let x := cyclicEdgeStart c
  let y := cyclicEdgeFinish (Finset.univ : Finset (Vertex B)) (OnLine B)
    (vertexCoord B) c
  if vertexCoord B x < vertexCoord B y then
    chartRep (chartF B) x.1 + chartRep (chartF B) y.1
  else
    chartRep (chartF B) x.1 - chartRep (chartF B) y.1

theorem chartRep_lowerEdgeVertex
    (e : ProjectiveStrictEdge pick (normals B)) :
    chartRep (chartF B) (lowerEdgeVertex B ha hb hc hncol pick e).1 =
      (chartF B (lowerEdgeRaw B ha hb hc hncol pick e))⁻¹ •
        lowerEdgeRaw B ha hb hc hncol pick e := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  apply chartRep_mk_eq_inv_smul
  exact chartF_lowerEdgeRaw_ne_zero B ha hb hc hncol pick e

theorem chartRep_upperEdgeVertex
    (e : ProjectiveStrictEdge pick (normals B)) :
    chartRep (chartF B) (upperEdgeVertex B ha hb hc hncol pick e).1 =
      (chartF B (upperEdgeRaw B ha hb hc hncol pick e))⁻¹ •
        upperEdgeRaw B ha hb hc hncol pick e := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  apply chartRep_mk_eq_inv_smul
  exact chartF_upperEdgeRaw_ne_zero B ha hb hc hncol pick e

/-- Orient a vector on an edge's supporting line so that the fixed
projective representative selector sees its chosen other line positively. -/
def orientForProjectiveEdge (e : ProjectiveStrictEdge pick (normals B))
    (z : Vec3) : Vec3 :=
  if 0 < otherNormals (normals B) e.1.1.1 (pick e.1.1.1) ⬝ᵥ z then z else -z

/-- A same-sign linear combination of the literal endpoint vectors,
oriented by the fixed projective selector, realizes the original restricted
sign sector. -/
theorem orient_endpointCombination_realizes
    (e : ProjectiveStrictEdge pick (normals B)) (A C : ℝ)
    (hAC : 0 < A * C) :
    Realizes (otherNormals (normals B) e.1.1.1) e.1.1.2
      (orientForProjectiveEdge B pick e
        (A • lowerEdgeRaw B ha hb hc hncol pick e +
          C • upperEdgeRaw B ha hb hc hncol pick e)) := by
  let := restrictedIndexNonempty B ha hb hc hncol e.1.1.1
  let D := edgeEndpointData B ha hb hc hncol pick e
  let l := lowerEdgeParameter B ha hb hc hncol pick e
  let u := upperEdgeParameter B ha hb hc hncol pick e
  let t := (A * l + C * u) / (A + C)
  have hsum : A + C ≠ 0 := by
    intro hzero
    have : C = -A := by linarith
    rw [this] at hAC
    nlinarith [sq_nonneg A]
  have ht := sameSign_weightedParameter_between D.lower_lt_upper hAC
  change l < t ∧ t < u at ht
  let xt := chartPoint (otherNormals (normals B) e.1.1.1) e.1.1.2
    (normals B e.1.1.1) (edgeWitness B pick e) t
  have hreal : Realizes (otherNormals (normals B) e.1.1.1) e.1.1.2 xt :=
    (D.realizes_iff t).2 ht
  let z := A • lowerEdgeRaw B ha hb hc hncol pick e +
    C • upperEdgeRaw B ha hb hc hncol pick e
  have hz : z = (A + C) • xt := by
    exact weighted_chartPoint_identity
      (edgeWitness B pick e)
      (direction (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1)) l u A C hsum
  let j := pick e.1.1.1
  have hjtrue : e.1.1.2 j = true := e.2
  have hjpos : 0 < otherNormals (normals B) e.1.1.1 j ⬝ᵥ xt := by
    simpa [hjtrue, signed] using hreal j
  rcases lt_or_gt_of_ne hsum with hsumneg | hsumpos
  · have hjzneg : ¬ 0 < otherNormals (normals B) e.1.1.1 j ⬝ᵥ z := by
      rw [hz, dotProduct_smul, smul_eq_mul]
      nlinarith
    rw [show orientForProjectiveEdge B pick e z = -z by
      simp [orientForProjectiveEdge, j, hjzneg]]
    intro k
    rw [hz, ← neg_smul, dotProduct_smul, smul_eq_mul, signed_mul]
    exact mul_pos (by linarith) (hreal k)
  · have hjzpos : 0 < otherNormals (normals B) e.1.1.1 j ⬝ᵥ z := by
      rw [hz, dotProduct_smul, smul_eq_mul]
      exact mul_pos hsumpos hjpos
    rw [show orientForProjectiveEdge B pick e z = z by
      simp [orientForProjectiveEdge, j, hjzpos]]
    intro k
    rw [hz, dotProduct_smul, smul_eq_mul, signed_mul]
    exact mul_pos hsumpos (hreal k)

/-- The canonical chart interior of the genuine cyclic edge attached to a
restriction sector realizes that sector (after the fixed projective
orientation).  This is the inverse-recovery input for injectivity. -/
theorem orient_cyclicInteriorRaw_realizes
    (e : ProjectiveStrictEdge pick (normals B)) :
    Realizes (otherNormals (normals B) e.1.1.1) e.1.1.2
      (orientForProjectiveEdge B pick e
        (cyclicInteriorRaw B
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e))) := by
  let vl := lowerEdgeVertex B ha hb hc hncol pick e
  let vu := upperEdgeVertex B ha hb hc hncol pick e
  let yl := lowerEdgeRaw B ha hb hc hncol pick e
  let yu := upperEdgeRaw B ha hb hc hncol pick e
  let fl := chartF B yl
  let fu := chartF B yu
  let z := fl * fu
  have hfl : fl ≠ 0 := chartF_lowerEdgeRaw_ne_zero B ha hb hc hncol pick e
  have hfu : fu ≠ 0 := chartF_upperEdgeRaw_ne_zero B ha hb hc hncol pick e
  have hcoordne : vertexCoord B vl ≠ vertexCoord B vu := fun h ↦
    lowerEdgeVertex_ne_upperEdgeVertex B ha hb hc hncol pick e <|
      vertexCoord_injective B (Finset.mem_univ vl) (Finset.mem_univ vu) h
  have hrep_l : chartRep (chartF B) vl.1 = fl⁻¹ • yl := by
    exact chartRep_lowerEdgeVertex B ha hb hc hncol pick e
  have hrep_u : chartRep (chartF B) vu.1 = fu⁻¹ • yu := by
    exact chartRep_upperEdgeVertex B ha hb hc hncol pick e
  by_cases hpos : 0 < z
  · have hcyc_same (hxy : vertexCoord B vl < vertexCoord B vu) :
        CyclicConsecutive (vertexCoord B)
          (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
          vl vu :=
      lower_upper_cyclicConsecutive_of_sameSign_of_lt
        B ha hb hc hncol pick e hpos hxy
    by_cases hlt : vertexCoord B vl < vertexCoord B vu
    · have hstart : cyclicEdgeStart
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vl := by
        unfold projectiveStrictEdgeToCyclic
        dsimp only
        rw [dif_pos hpos, dif_pos hlt]
        rfl
      have hfinish : cyclicEdgeFinish (Finset.univ : Finset (Vertex B)) (OnLine B)
          (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vu :=
        projectiveStrictEdgeToCyclic_finish_eq_of_start_eq
          B ha hb hc hncol pick e vl vu (hcyc_same hlt) hstart
      have hraw : cyclicInteriorRaw B
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) =
            fl⁻¹ • yl + fu⁻¹ • yu := by
        simp only [cyclicInteriorRaw, hstart, hfinish, if_pos hlt, hrep_l, hrep_u]
      rw [hraw]
      apply orient_endpointCombination_realizes B ha hb hc hncol pick e
      rw [← mul_inv]
      exact inv_pos.mpr hpos
    · have hgt : vertexCoord B vu < vertexCoord B vl :=
        lt_of_le_of_ne (le_of_not_gt hlt) hcoordne.symm
      have hcyc : CyclicConsecutive (vertexCoord B)
          (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
          vu vl :=
        upper_lower_cyclicConsecutive_of_sameSign_of_lt
          B ha hb hc hncol pick e hpos hgt
      have hstart : cyclicEdgeStart
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vu := by
        unfold projectiveStrictEdgeToCyclic
        dsimp only
        rw [dif_pos hpos, dif_neg hlt]
        rfl
      have hfinish : cyclicEdgeFinish (Finset.univ : Finset (Vertex B)) (OnLine B)
          (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vl :=
        projectiveStrictEdgeToCyclic_finish_eq_of_start_eq
          B ha hb hc hncol pick e vu vl hcyc hstart
      have hraw : cyclicInteriorRaw B
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) =
            fl⁻¹ • yl + fu⁻¹ • yu := by
        simp only [cyclicInteriorRaw, hstart, hfinish, if_pos hgt, hrep_l, hrep_u]
        rw [add_comm]
      rw [hraw]
      apply orient_endpointCombination_realizes B ha hb hc hncol pick e
      rw [← mul_inv]
      exact inv_pos.mpr hpos
  · have hz : z ≠ 0 := mul_ne_zero hfl hfu
    have hneg : z < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hz
    by_cases hlt : vertexCoord B vl < vertexCoord B vu
    · have hcyc : CyclicConsecutive (vertexCoord B)
          (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
          vu vl :=
        upper_lower_cyclicConsecutive_of_oppositeSign_of_lt
          B ha hb hc hncol pick e hneg hlt
      have hstart : cyclicEdgeStart
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vu := by
        unfold projectiveStrictEdgeToCyclic
        dsimp only
        rw [dif_neg hpos, dif_pos hlt]
        rfl
      have hfinish : cyclicEdgeFinish (Finset.univ : Finset (Vertex B)) (OnLine B)
          (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vl :=
        projectiveStrictEdgeToCyclic_finish_eq_of_start_eq
          B ha hb hc hncol pick e vu vl hcyc hstart
      have hraw : cyclicInteriorRaw B
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) =
            (-fl⁻¹) • yl + fu⁻¹ • yu := by
        have hnlt : ¬ vertexCoord B vu < vertexCoord B vl := not_lt_of_ge hlt.le
        simp only [cyclicInteriorRaw, hstart, hfinish, if_neg hnlt, hrep_l, hrep_u]
        simp [sub_eq_add_neg, neg_smul, add_comm]
      rw [hraw]
      apply orient_endpointCombination_realizes B ha hb hc hncol pick e
      have hinv : z⁻¹ < 0 := inv_lt_zero.mpr hneg
      rw [mul_inv] at hinv
      nlinarith

    · have hgt : vertexCoord B vu < vertexCoord B vl :=
        lt_of_le_of_ne (le_of_not_gt hlt) hcoordne.symm
      have hcyc : CyclicConsecutive (vertexCoord B)
          (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1.1)
          vl vu :=
        lower_upper_cyclicConsecutive_of_oppositeSign_of_lt
          B ha hb hc hncol pick e hneg hgt
      have hstart : cyclicEdgeStart
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vl := by
        unfold projectiveStrictEdgeToCyclic
        dsimp only
        rw [dif_neg hpos, dif_neg hlt]
        rfl
      have hfinish : cyclicEdgeFinish (Finset.univ : Finset (Vertex B)) (OnLine B)
          (vertexCoord B) (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) = vu :=
        projectiveStrictEdgeToCyclic_finish_eq_of_start_eq
          B ha hb hc hncol pick e vl vu hcyc hstart
      have hraw : cyclicInteriorRaw B
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e) =
            fl⁻¹ • yl + (-fu⁻¹) • yu := by
        have hnlt : ¬ vertexCoord B vl < vertexCoord B vu := not_lt_of_ge hgt.le
        simp only [cyclicInteriorRaw, hstart, hfinish, if_neg hnlt, hrep_l, hrep_u]
        simp [sub_eq_add_neg, neg_smul]
      rw [hraw]
      apply orient_endpointCombination_realizes B ha hb hc hncol pick e
      have hinv : z⁻¹ < 0 := inv_lt_zero.mpr hneg
      rw [mul_inv] at hinv
      nlinarith

theorem sign_eq_of_same_realizer {J : Type*} {n : J → Vec3}
    {s t : J → Bool} {x : Vec3}
    (hs : Realizes n s x) (ht : Realizes n t x) : s = t := by
  funext j
  cases hsj : s j <;> cases htj : t j
  · rfl
  · have hspos := hs j
    have htpos := ht j
    simp [hsj, htj, signed] at hspos htpos
    linarith
  · have hspos := hs j
    have htpos := ht j
    simp [hsj, htj, signed] at hspos htpos
    linarith
  · rfl

/-- The genuine sector-to-cyclic-edge map is injective: its support line and
its canonical chart-interior realizer recover the complete restricted sign
pattern. -/
theorem projectiveStrictEdgeToCyclic_injective :
    Function.Injective
      (projectiveStrictEdgeToCyclic B ha hb hc hncol pick) := by
  rintro ⟨⟨⟨i₁, s₁⟩, hfeas₁⟩, hpositive₁⟩
    ⟨⟨⟨i₂, s₂⟩, hfeas₂⟩, hpositive₂⟩ heq
  let e₁ : ProjectiveStrictEdge pick (normals B) :=
    ⟨⟨⟨i₁, s₁⟩, hfeas₁⟩, hpositive₁⟩
  let e₂ : ProjectiveStrictEdge pick (normals B) :=
    ⟨⟨⟨i₂, s₂⟩, hfeas₂⟩, hpositive₂⟩
  change e₁ = e₂
  have heq' : projectiveStrictEdgeToCyclic B ha hb hc hncol pick e₁ =
      projectiveStrictEdgeToCyclic B ha hb hc hncol pick e₂ := heq
  have howner : i₁ = i₂ := by
    have h := congrArg (fun c ↦ c.1) heq'
    simpa only [projectiveStrictEdgeToCyclic_line] using h
  subst i₂
  have hraw := congrArg (cyclicInteriorRaw B) heq'
  have hvec : orientForProjectiveEdge B pick e₁
        (cyclicInteriorRaw B
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e₁)) =
      orientForProjectiveEdge B pick e₂
        (cyclicInteriorRaw B
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e₂)) := by
    unfold orientForProjectiveEdge
    rw [hraw]
  have hr₁ := orient_cyclicInteriorRaw_realizes B ha hb hc hncol pick e₁
  have hr₂ := orient_cyclicInteriorRaw_realizes B ha hb hc hncol pick e₂
  have hr₂' : Realizes (otherNormals (normals B) i₁) s₂
      (orientForProjectiveEdge B pick e₁
        (cyclicInteriorRaw B
          (projectiveStrictEdgeToCyclic B ha hb hc hncol pick e₁))) := by
    rw [hvec]
    exact hr₂
  have hsign : s₁ = s₂ :=
    sign_eq_of_same_realizer hr₁ hr₂'
  subst s₂
  rfl

theorem projectiveStrictEdgeToCyclic_bijective :
    Function.Bijective
      (projectiveStrictEdgeToCyclic B ha hb hc hncol pick) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨projectiveStrictEdgeToCyclic_injective B ha hb hc hncol pick, ?_⟩
  exact card_projectiveStrictEdge_eq_cyclic_of_restrictedFaceCount
    pick (normals B) (Finset.univ : Finset (Vertex B)) (OnLine B)
    (concreteRestrictedFaceCount B ha hb hc hncol)

/-- The actual owner-preserving equivalence between feasible projective
restriction sectors and the genuine cyclic-successor intervals of the
projective arrangement. -/
noncomputable def projectiveStrictEdgeCyclicEquiv :
    ProjectiveStrictEdge pick (normals B) ≃
      CyclicSkeletonEdge (Finset.univ : Finset (Vertex B)) (OnLine B) :=
  Equiv.ofBijective (projectiveStrictEdgeToCyclic B ha hb hc hncol pick)
    (projectiveStrictEdgeToCyclic_bijective B ha hb hc hncol pick)

@[simp] theorem projectiveStrictEdgeCyclicEquiv_apply
    (e : ProjectiveStrictEdge pick (normals B)) :
    projectiveStrictEdgeCyclicEquiv B ha hb hc hncol pick e =
      projectiveStrictEdgeToCyclic B ha hb hc hncol pick e := rfl

@[simp] theorem projectiveStrictEdgeCyclicEquiv_line
    (e : ProjectiveStrictEdge pick (normals B)) :
    cyclicEdgeLine (projectiveStrictEdgeCyclicEquiv B ha hb hc hncol pick e) =
      e.1.1.1 := by
  exact projectiveStrictEdgeToCyclic_line B ha hb hc hncol pick e

theorem projectiveStrictEdgeCyclicEquiv_vertices
    (e : ProjectiveStrictEdge pick (normals B)) :
    cyclicEdgeVertices (Finset.univ : Finset (Vertex B)) (OnLine B)
        (vertexCoord B) (projectiveStrictEdgeCyclicEquiv B ha hb hc hncol pick e) =
      {lowerEdgeVertex B ha hb hc hncol pick e,
        upperEdgeVertex B ha hb hc hncol pick e} := by
  exact projectiveStrictEdgeToCyclic_vertices B ha hb hc hncol pick e

/-- The antipodal two-sheet lift of the genuine projective cyclic-edge
equivalence.  Its Boolean coordinate is the canonical sign-vector sheet. -/
noncomputable def strictEdgeLiftedCyclicEquiv :
    StrictEdge (normals B) ≃
      LiftedCyclicSkeletonEdge (Finset.univ : Finset (Vertex B)) (OnLine B) :=
  strictEdgeEquivLiftedCyclic pick (normals B)
    (projectiveStrictEdgeCyclicEquiv B ha hb hc hncol pick)

@[simp] theorem strictEdgeLiftedCyclicEquiv_line
    (e : StrictEdge (normals B)) :
    cyclicEdgeLine (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1 =
      e.1.1 := by
  change cyclicEdgeLine
      (projectiveStrictEdgeCyclicEquiv B ha hb hc hncol pick
        (normalizeProjectiveEdge pick (normals B) e)) = e.1.1
  rw [projectiveStrictEdgeCyclicEquiv_line, normalizeProjectiveEdge_support]

theorem strictEdgeLiftedCyclicEquiv_projectiveVertices
    (e : StrictEdge (normals B)) :
    cyclicEdgeVertices (Finset.univ : Finset (Vertex B)) (OnLine B)
        (vertexCoord B) (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1 =
      {lowerEdgeVertex B ha hb hc hncol pick
          (normalizeProjectiveEdge pick (normals B) e),
        upperEdgeVertex B ha hb hc hncol pick
          (normalizeProjectiveEdge pick (normals B) e)} := by
  exact projectiveStrictEdgeCyclicEquiv_vertices B ha hb hc hncol pick
    (normalizeProjectiveEdge pick (normals B) e)

end ConcreteEdge

end

end Erdos735.SignVector.ProjectiveEdgeEndpointEquiv
