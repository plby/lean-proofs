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

import ErdosProblems.Erdos735.LeviExteriorSector
import ErdosProblems.Erdos735.ConcretePolarLineBelt
import ErdosProblems.Erdos735.LeviCyclicDegenerate
import ErdosProblems.Erdos735.Primal

/-!
# The projective (antipodal-orbit) form of Levi's triangle bound

`StrictFace` describes spherical chambers.  A projective chamber is a free
antipodal pair, so the Stage-4 use of Levi needs three *antipodal orbits*,
not merely three spherical faces.  This file records the finite six-face
criterion and proves it for the nondegenerate affine-hull branch of the
concrete exterior-sector construction.
-/

open Classical
open scoped LinearAlgebra.Projectivization Matrix
noncomputable section

namespace Erdos735.SignVectorArrangement

open SignVector

universe u

variable {I : Type u} [Fintype I] [DecidableEq I]

@[simp] theorem antipodalStrictFace_involutive
    {n : I → Vec3} (f : StrictFace n) :
    antipodalStrictFace (antipodalStrictFace f) = f := by
  apply Subtype.ext
  simp [antipodalStrictFace, antipodalSign_antipodalSign]

/-- Three triangular faces, no one antipodal to another, give six distinct
spherical triangles after adjoining all antipodes.  This is exactly the
cardinality form of three projective triangle orbits. -/
theorem six_le_incident_triangles_of_three_antipodal_orbits
    {n : I → Vec3} (i : I) (face : Fin 3 → StrictFace n)
    (hface : Function.Injective face)
    (hanti : ∀ s t, face s ≠ antipodalStrictFace (face t))
    (hincident : ∀ t, LineFaceIncident n i (face t))
    (hdegree : ∀ t, strictFaceDegree n (face t) = 3) :
    6 ≤ (Finset.univ.filter fun f : StrictFace n ↦
      LineFaceIncident n i f ∧ strictFaceDegree n f = 3).card := by
  let sixFace : Fin 3 × Bool → StrictFace n := fun tb ↦
    if tb.2 then antipodalStrictFace (face tb.1) else face tb.1
  have hsix : Function.Injective sixFace := by
    rintro ⟨s, bs⟩ ⟨t, bt⟩ h
    cases bs <;> cases bt
    · have hst : s = t := hface (by simpa [sixFace] using h)
      subst t
      rfl
    · exact (hanti s t (by simpa [sixFace] using h)).elim
    · exact (hanti t s (by simpa [sixFace] using h.symm)).elim
    · have hant : antipodalStrictFace (face s) =
          antipodalStrictFace (face t) := by simpa [sixFace] using h
      have hst : s = t := hface (by
        have := congrArg antipodalStrictFace hant
        simpa using this)
      subst t
      rfl
  let T : Finset (StrictFace n) := Finset.univ.image sixFace
  have hTcard : T.card = 6 := by
    rw [Finset.card_image_of_injective _ hsix]
    simp
  have hsubset : T ⊆ Finset.univ.filter fun f : StrictFace n ↦
      LineFaceIncident n i f ∧ strictFaceDegree n f = 3 := by
    intro f hf
    obtain ⟨⟨t, b⟩, -, rfl⟩ := Finset.mem_image.mp hf
    cases b
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hincident t, hdegree t⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · change LineFaceIncident n i (antipodalStrictFace (face t))
        rw [← mem_faceEdgeOwners_iff,
          faceEdgeOwners_antipodalStrictFace,
          mem_faceEdgeOwners_iff]
        exact hincident t
      · change strictFaceDegree n (antipodalStrictFace (face t)) = 3
        rw [← card_faceEdgeOwners,
          faceEdgeOwners_antipodalStrictFace,
          card_faceEdgeOwners]
        exact hdegree t
  calc
    6 = T.card := hTcard.symm
    _ ≤ _ := Finset.card_le_card hsubset

theorem HasProjectiveSignVectorLeviProperty.six_le_incident_triangles
    {n : I → Vec3} (H : HasProjectiveSignVectorLeviProperty n) (i : I) :
    6 ≤ (Finset.univ.filter fun f : StrictFace n ↦
      LineFaceIncident n i f ∧ strictFaceDegree n f = 3).card :=
  H i

end Erdos735.SignVectorArrangement

namespace Erdos735.ConcretePolarLineBelt

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement

variable (B : Finset ProjectiveArrangement.Point)
variable {a b c : ProjectiveArrangement.Point}
variable (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
variable [Nonempty (Line B)]

/-- Degenerate-branch endpoint for projective Levi.  If every spherical
face in a fixed literal line belt is triangular, the belt contains four
faces per projective vertex and every represented line has at least two
vertices.  Thus there are at least eight, in particular six, incident
triangles. -/
theorem six_le_incident_triangles_of_all_incident_triangular
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (hall : ∀ f : StrictFace (normals B),
      LineFaceIncident (normals B) s f → strictFaceDegree (normals B) f = 3) :
    6 ≤ (Finset.univ.filter fun f : StrictFace (normals B) ↦
      LineFaceIncident (normals B) s f ∧
        strictFaceDegree (normals B) f = 3).card := by
  have hcard := card_incidentFaces_eq_four_mul_verticesOn
    B ha hb hc hncol pick s
  have hvertices : 2 ≤
      (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) s).card :=
    two_vertices_on_every_line B ha hb hc hncol s
  have hinc : 8 ≤ Fintype.card
      {f : StrictFace (normals B) // LineFaceIncident (normals B) s f} := by
    rw [hcard]
    omega
  have heq : (Finset.univ.filter fun f : StrictFace (normals B) ↦
      LineFaceIncident (normals B) s f ∧
        strictFaceDegree (normals B) f = 3) =
      Finset.univ.filter fun f : StrictFace (normals B) ↦
        LineFaceIncident (normals B) s f := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact And.left
    · intro hf
      exact ⟨hf, hall f hf⟩
  rw [heq, ← Fintype.card_subtype]
  omega

end Erdos735.ConcretePolarLineBelt

namespace Erdos735.LeviExteriorSector

open ProjectiveArrangement
open SignVector SignVectorArrangement
open Matrix
open LeviAffineChart LeviAffineVertices
open SignVector.PolarFace SignVector.PolarPlaneChart
open SignVector.PolarBoundaryOrder

variable {B : Finset Point}

private theorem normal_cross
    {B : Finset Point} (i j : B) (hij : i ≠ j) :
    normalVec i.1 ⨯₃ normalVec j.1 ≠ 0 := by
  apply normalVec_cross_ne_zero
  intro h
  exact hij (Subtype.ext h)

private theorem chartPoint_ne_zero (p u : Point) :
    LeviAffineChart.chartPoint p u ≠ 0 := by
  intro hzero
  have hone := LeviAffineChart.selected_dot_chartPoint p u
  rw [hzero] at hone
  simp at hone

theorem projectivized_chartPoint_injective (p : Point) :
    Function.Injective (fun u : Point ↦
      Projectivization.mk ℝ (LeviAffineChart.chartPoint p u)
        (chartPoint_ne_zero p u)) := by
  intro u v huv
  rw [Projectivization.mk_eq_mk_iff'] at huv
  obtain ⟨a, ha⟩ := huv
  have hadot := congrArg (fun z : SignVector.Vec3 ↦ normalVec p ⬝ᵥ z) ha
  rw [dotProduct_smul, LeviAffineChart.selected_dot_chartPoint,
    LeviAffineChart.selected_dot_chartPoint] at hadot
  simp only [smul_eq_mul, mul_one] at hadot
  have haone : a = 1 := by linarith
  apply LeviAffineChart.chartPoint_injective p
  simpa [haone] using ha.symm

/-- In a proper affine-span branch, every three affine crossing points are
collinear.  Otherwise those three points would be an affine basis of the
two-dimensional chart and force the whole crossing set to span the plane. -/
theorem collinear3_of_mem_vertexFinset_of_affineSpan_ne_top
    (p : B)
    (hspan : affineSpan ℝ (vertexFinset B p : Set Point) ≠ ⊤)
    {u v z : Point}
    (hu : u ∈ vertexFinset B p) (hv : v ∈ vertexFinset B p)
    (hz : z ∈ vertexFinset B p) :
    ProjectiveDuality.Collinear3 u v z := by
  by_contra hncol
  have huv : u ≠ v := by
    intro huv
    apply hncol
    simp [huv, ProjectiveDuality.Collinear3,
      ProjectiveDuality.orientationDet]
  have hnotcol : ¬ Collinear ℝ ({u, v, z} : Set Point) := by
    intro hcol
    have hzline : z ∈ line[ℝ, u, v] :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) huv
    apply hncol
    have hcol' : Erdos735.Collinear3 u v z :=
      (collinear3_iff_mem_affineSpan_pair huv).mpr hzline
    simpa [Erdos735.Collinear3, Erdos735.orientationDet,
      ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet] using hcol'
  let points : Fin 3 → Point := ![u, v, z]
  have hind : AffineIndependent ℝ points := by
    apply affineIndependent_iff_not_collinear_set.mpr
    simpa [points] using hnotcol
  have hrange : Set.range points ⊆ (vertexFinset B p : Set Point) := by
    rintro y ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hv
    · exact hz
  apply hspan
  apply top_unique
  rw [← (hind.affineSpan_eq_top_iff_card_eq_finrank_add_one).mpr (by simp)]
  exact affineSpan_mono ℝ hrange

/-- An affine line owner is determined by two distinct chart points. -/
theorem owner_eq_of_lineEval_eq_zero_at_two_points
    (p q r : Point) {u v : Point} (huv : u ≠ v)
    (hqu : lineEval p q u = 0) (hqv : lineEval p q v = 0)
    (hru : lineEval p r u = 0) (hrv : lineEval p r v = 0) :
    q = r := by
  by_contra hqr
  have hproj := ProjectiveArrangement.eq_of_two_common_lines hqr
    (x := Projectivization.mk ℝ (LeviAffineChart.chartPoint p u)
      (chartPoint_ne_zero p u))
    (y := Projectivization.mk ℝ (LeviAffineChart.chartPoint p v)
      (chartPoint_ne_zero p v))
    (by
      change OnProjectiveLine (normalVec q)
        (Projectivization.mk ℝ (LeviAffineChart.chartPoint p u)
          (chartPoint_ne_zero p u))
      exact (onProjectiveLine_mk_iff _ _ _).mpr (by simpa using hqu))
    (by
      change OnProjectiveLine (normalVec r)
        (Projectivization.mk ℝ (LeviAffineChart.chartPoint p u)
          (chartPoint_ne_zero p u))
      exact (onProjectiveLine_mk_iff _ _ _).mpr (by simpa using hru))
    (by
      change OnProjectiveLine (normalVec q)
        (Projectivization.mk ℝ (LeviAffineChart.chartPoint p v)
          (chartPoint_ne_zero p v))
      exact (onProjectiveLine_mk_iff _ _ _).mpr (by simpa using hqv))
    (by
      change OnProjectiveLine (normalVec r)
        (Projectivization.mk ℝ (LeviAffineChart.chartPoint p v)
          (chartPoint_ne_zero p v))
      exact (onProjectiveLine_mk_iff _ _ _).mpr (by simpa using hrv))
  exact huv (projectivized_chartPoint_injective p hproj)

theorem lineEval_eq_zero_of_collinear_of_two
    (p q : Point) {u v z : Point} (huv : u ≠ v)
    (hcol : ProjectiveDuality.Collinear3 u v z)
    (hu : lineEval p q u = 0) (hv : lineEval p q v = 0) :
    lineEval p q z = 0 := by
  have hcol' : Erdos735.Collinear3 u v z := by
    simpa [Erdos735.Collinear3, Erdos735.orientationDet,
      ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet] using hcol
  have hzline := (collinear3_iff_mem_affineSpan_pair huv).mp hcol'
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hzline
  simp [LeviAffineChart.lineEval, AffineMap.lineMap_apply_module'] at hu hv ⊢
  linear_combination (1 - t) * hu + t * hv

/-- A boundary corner whose two owners are different from the selected
line is an affine crossing in the chart obtained by sending that selected
line to infinity.  The conclusion remembers the exact projective boundary
vertex, which is what makes the singleton and collinear degeneracies usable
in the cyclic boundary. -/
theorem exists_vertexFinset_eq_boundaryProjectiveVertex
    [Nonempty B] (p : B)
    (f : StrictFace (fun q : B ↦ normalVec q.1))
    {x : SignVector.Vec3}
    (hx : Realizes (fun q : B ↦ normalVec q.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun q : B ↦ normalVec q.1)) = ⊤)
    (hpowner : p ∈ edgeOwners (fun q : B ↦ normalVec q.1) f.1)
    (t : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)))
    (hleft : boundaryOwner f hx normal_cross hspan t ≠ p)
    (hright : boundaryOwner f hx normal_cross hspan
      (Erdos957.cyclicSucc t) ≠ p) :
    ∃ v ∈ vertexFinset B p,
      Projectivization.mk ℝ (LeviAffineChart.chartPoint p.1 v)
          (chartPoint_ne_zero p.1 v) =
        boundaryProjectiveVertex f hx normal_cross hspan t := by
  let q : OtherPoint B p :=
    ⟨boundaryOwner f hx normal_cross hspan t, hleft⟩
  let r : OtherPoint B p :=
    ⟨boundaryOwner f hx normal_cross hspan (Erdos957.cyclicSucc t), hright⟩
  have hpCorner : normalVec p.1 ⬝ᵥ
      cornerVector f hx normal_cross hspan t ≠ 0 := by
    intro hzero
    rcases owner_eq_endpoint_of_dot_cornerVector_eq_zero
        f hx normal_cross hspan t p hpowner hzero with h | h
    · exact hleft h.symm
    · exact hright h.symm
  have hncol : ¬ ProjectiveDuality.Collinear3 p.1 q.1.1 r.1.1 := by
    intro hcol
    apply hpCorner
    have hinc : Incident
        (boundaryProjectiveVertex f hx normal_cross hspan t) p.1 := by
      change OnProjectiveLine (normalVec p.1)
        (boundaryProjectiveVertex f hx normal_cross hspan t)
      rw [boundaryProjectiveVertex, onProjectiveLine_mk_iff]
      dsimp [q, r] at hcol
      simp [ProjectiveDuality.Collinear3,
        ProjectiveDuality.orientationDet, vec3_dotProduct, cross_apply,
        normalVec] at hcol ⊢
      linear_combination hcol
    rw [← cornerProjectiveVertex_eq_boundaryProjectiveVertex
      f hx normal_cross hspan t] at hinc
    exact (onProjectiveLine_mk_iff _ _
      (cornerVector_ne_zero f hx normal_cross hspan t)).mp hinc
  have hparallel : Nonparallel p.1 q.1.1 r.1.1 :=
    (nonparallel_iff_not_collinear _ _ _).2 hncol
  let qr : CrossingPair B p := ⟨(q, r), hparallel⟩
  let v := indexedCrossing B p qr
  refine ⟨v, indexedCrossing_mem B p qr, ?_⟩
  have hqr : q.1.1 ≠ r.1.1 := by
    intro h
    exact (boundaryOwner_ne_succ f hx normal_cross hspan t)
      (Subtype.ext h)
  apply eq_of_two_common_lines hqr
  · apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 v)).2
    rw [normalVec_dot_chartPoint]
    exact indexedCrossing_on_left B p qr
  · apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 v)).2
    rw [normalVec_dot_chartPoint]
    exact indexedCrossing_on_right B p qr
  · exact boundaryProjectiveVertex_on_left f hx normal_cross hspan t
  · exact boundaryProjectiveVertex_on_right f hx normal_cross hspan t

theorem boundaryOwner_index_eq_endpoint_of_lineEval_eq_zero
    [Nonempty B] (p : B)
    (f : StrictFace (fun q : B ↦ normalVec q.1))
    {x : SignVector.Vec3}
    (hx : Realizes (fun q : B ↦ normalVec q.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun q : B ↦ normalVec q.1)) = ⊤)
    (t z : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)))
    (u : Point)
    (hu : Projectivization.mk ℝ (LeviAffineChart.chartPoint p.1 u)
        (chartPoint_ne_zero p.1 u) =
      boundaryProjectiveVertex f hx normal_cross hspan t)
    (hzero : lineEval p.1
      (boundaryOwner f hx normal_cross hspan z).1 u = 0) :
    z = t ∨ z = Erdos957.cyclicSucc t := by
  have hinc : OnProjectiveLine
      (normalVec (boundaryOwner f hx normal_cross hspan z).1)
      (boundaryProjectiveVertex f hx normal_cross hspan t) := by
    rw [← hu]
    exact (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u)).mpr
      (by simpa using hzero)
  rw [← cornerProjectiveVertex_eq_boundaryProjectiveVertex
    f hx normal_cross hspan t] at hinc
  have hcorner : normalVec (boundaryOwner f hx normal_cross hspan z).1 ⬝ᵥ
      cornerVector f hx normal_cross hspan t = 0 :=
    (onProjectiveLine_mk_iff _ _
      (cornerVector_ne_zero f hx normal_cross hspan t)).mp hinc
  rcases owner_eq_endpoint_of_dot_cornerVector_eq_zero
      f hx normal_cross hspan t
      (boundaryOwner f hx normal_cross hspan z)
      (boundaryOwnerEquiv f hx normal_cross hspan z).2 hcorner with h | h
  · left
    apply (boundaryOwnerEquiv f hx normal_cross hspan).injective
    exact Subtype.ext h
  · right
    apply (boundaryOwnerEquiv f hx normal_cross hspan).injective
    exact Subtype.ext h

/-- In the proper affine-span branch, three consecutive boundary corners
away from the selected owner are impossible.  Their three affine crossings
are collinear; hence the two middle boundary owners are both the unique
affine line through the last two crossings, contradicting owner
injectivity. -/
theorem false_of_three_consecutive_nonselected_corners_of_affineSpan_ne_top
    [Nonempty B] (p : B)
    (f : StrictFace (fun q : B ↦ normalVec q.1))
    {x : SignVector.Vec3}
    (hx : Realizes (fun q : B ↦ normalVec q.1) f.1 x)
    (hspanNormals : Submodule.span ℝ
      (Set.range (fun q : B ↦ normalVec q.1)) = ⊤)
    (hspanVertices : affineSpan ℝ (vertexFinset B p : Set Point) ≠ ⊤)
    (hpowner : p ∈ edgeOwners (fun q : B ↦ normalVec q.1) f.1)
    (t : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)))
    (h0 : boundaryOwner f hx normal_cross hspanNormals t ≠ p)
    (h1 : boundaryOwner f hx normal_cross hspanNormals
      (Erdos957.cyclicSucc t) ≠ p)
    (h2 : boundaryOwner f hx normal_cross hspanNormals
      (Erdos957.cyclicSucc (Erdos957.cyclicSucc t)) ≠ p)
    (h3 : boundaryOwner f hx normal_cross hspanNormals
      (Erdos957.cyclicSucc (Erdos957.cyclicSucc
        (Erdos957.cyclicSucc t))) ≠ p) : False := by
  let s : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)) →
      Fin (Erdos957.hullVertexCount
        (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)) :=
    Erdos957.cyclicSucc
  obtain ⟨u0, hu0mem, hu0⟩ :=
    exists_vertexFinset_eq_boundaryProjectiveVertex p f hx hspanNormals
      hpowner t h0 h1
  obtain ⟨u1, hu1mem, hu1⟩ :=
    exists_vertexFinset_eq_boundaryProjectiveVertex p f hx hspanNormals
      hpowner (s t) h1 h2
  obtain ⟨u2, hu2mem, hu2⟩ :=
    exists_vertexFinset_eq_boundaryProjectiveVertex p f hx hspanNormals
      hpowner (s (s t)) h2 h3
  have hthree : 3 ≤ Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x) := by
    rw [Erdos957.hullVertexCount,
      hullVertices_boundaryPolygon hx normal_cross]
    exact three_le_boundaryPolygon_card f hx normal_cross hspanNormals
  have hu01 : u0 ≠ u1 := by
    intro huv
    subst u1
    have hvertices : boundaryProjectiveVertex f hx normal_cross hspanNormals t =
        boundaryProjectiveVertex f hx normal_cross hspanNormals (s t) :=
      hu0.symm.trans hu1
    have hindices :=
      boundaryProjectiveVertex_injective f hx normal_cross hspanNormals hvertices
    exact Erdos957.cyclicSucc_ne_self (by omega) t hindices.symm
  have hu12 : u1 ≠ u2 := by
    intro huv
    subst u2
    have hvertices : boundaryProjectiveVertex f hx normal_cross hspanNormals (s t) =
        boundaryProjectiveVertex f hx normal_cross hspanNormals (s (s t)) :=
      hu1.symm.trans hu2
    have hindices :=
      boundaryProjectiveVertex_injective f hx normal_cross hspanNormals hvertices
    exact Erdos957.cyclicSucc_ne_self (by omega) (s t) hindices.symm
  let q : B := boundaryOwner f hx normal_cross hspanNormals (s t)
  let r : B := boundaryOwner f hx normal_cross hspanNormals (s (s t))
  have hq0 : lineEval p.1 q.1 u0 = 0 := by
    rw [← normalVec_dot_chartPoint]
    apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u0)).mp
    rw [hu0]
    exact boundaryProjectiveVertex_on_right f hx normal_cross hspanNormals t
  have hq1 : lineEval p.1 q.1 u1 = 0 := by
    rw [← normalVec_dot_chartPoint]
    apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u1)).mp
    rw [hu1]
    exact boundaryProjectiveVertex_on_left f hx normal_cross hspanNormals (s t)
  have hr1 : lineEval p.1 r.1 u1 = 0 := by
    rw [← normalVec_dot_chartPoint]
    apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u1)).mp
    rw [hu1]
    exact boundaryProjectiveVertex_on_right f hx normal_cross hspanNormals (s t)
  have hr2 : lineEval p.1 r.1 u2 = 0 := by
    rw [← normalVec_dot_chartPoint]
    apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u2)).mp
    rw [hu2]
    exact boundaryProjectiveVertex_on_left f hx normal_cross hspanNormals (s (s t))
  have hcol := collinear3_of_mem_vertexFinset_of_affineSpan_ne_top p
    hspanVertices hu0mem hu1mem hu2mem
  have hq2 : lineEval p.1 q.1 u2 = 0 :=
    lineEval_eq_zero_of_collinear_of_two p.1 q.1 hu01 hcol hq0 hq1
  have hqrval : q.1 = r.1 := owner_eq_of_lineEval_eq_zero_at_two_points
    p.1 q.1 r.1 hu12 hq1 hq2 hr1 hr2
  have hqr : q = r := Subtype.ext hqrval
  have hindices : s t = s (s t) := by
    apply (boundaryOwnerEquiv f hx normal_cross hspanNormals).injective
    apply Subtype.ext
    exact hqr
  exact Erdos957.cyclicSucc_ne_self (by omega) (s t) hindices.symm

/-- A four-owner incident boundary is also impossible in the proper
affine-collinear branch.  If the first and third nonselected owners meet in
the affine chart, their crossing lies on the common crossing line and
forces two consecutive owners to agree.  Hence they are parallel in this
chart, so their common point at infinity makes the first and last cyclic
boundary vertices equal. -/
theorem false_of_four_cycle_of_affineSpan_ne_top
    [Nonempty B] (p : B)
    (f : StrictFace (fun q : B ↦ normalVec q.1))
    {x : SignVector.Vec3}
    (hx : Realizes (fun q : B ↦ normalVec q.1) f.1 x)
    (hspanNormals : Submodule.span ℝ
      (Set.range (fun q : B ↦ normalVec q.1)) = ⊤)
    (hspanVertices : affineSpan ℝ (vertexFinset B p : Set Point) ≠ ⊤)
    (hpowner : p ∈ edgeOwners (fun q : B ↦ normalVec q.1) f.1)
    (t : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)))
    (htp : boundaryOwner f hx normal_cross hspanNormals t = p)
    (hcycle : Erdos957.cyclicSucc (Erdos957.cyclicSucc
      (Erdos957.cyclicSucc (Erdos957.cyclicSucc t))) = t) : False := by
  let s : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)) →
      Fin (Erdos957.hullVertexCount
        (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)) :=
    Erdos957.cyclicSucc
  let t1 := s t
  let t2 := s t1
  let t3 := s t2
  have hthree : 3 ≤ Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x) := by
    rw [Erdos957.hullVertexCount,
      hullVertices_boundaryPolygon hx normal_cross]
    exact three_le_boundaryPolygon_card f hx normal_cross hspanNormals
  have hsuccInjective : Function.Injective s := (finRotate _).injective
  have ht1t : t1 ≠ t := Erdos957.cyclicSucc_ne_self (by omega) t
  have ht2t : t2 ≠ t := Erdos957.cyclicSucc_cyclicSucc_ne_self hthree t
  have ht1t2 : t1 ≠ t2 := by
    exact (Erdos957.cyclicSucc_ne_self (by omega) t1).symm
  have ht2t3 : t2 ≠ t3 := by
    exact (Erdos957.cyclicSucc_ne_self (by omega) t2).symm
  have ht1t3 : t1 ≠ t3 := by
    intro h
    have hs := congrArg s h
    change t2 = s t3 at hs
    rw [show s t3 = t by exact hcycle] at hs
    exact ht2t hs
  have ht3t : t3 ≠ t := by
    intro h
    have hs := congrArg s h
    change s t3 = s t at hs
    rw [show s t3 = t by exact hcycle] at hs
    exact ht1t hs.symm
  let owner : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun q : B ↦ normalVec q.1) f.1 x)) → B :=
    boundaryOwner f hx normal_cross hspanNormals
  have howner : Function.Injective owner := by
    intro i j hij
    apply (boundaryOwnerEquiv f hx normal_cross hspanNormals).injective
    exact Subtype.ext hij
  have h1p : owner t1 ≠ p := by
    intro h
    exact ht1t (howner (h.trans htp.symm))
  have h2p : owner t2 ≠ p := by
    intro h
    exact ht2t (howner (h.trans htp.symm))
  have h3p : owner t3 ≠ p := by
    intro h
    exact ht3t (howner (h.trans htp.symm))
  let q1 : OtherPoint B p := ⟨owner t1, h1p⟩
  let q3 : OtherPoint B p := ⟨owner t3, h3p⟩
  obtain ⟨u0, hu0mem, hu0⟩ :=
    exists_vertexFinset_eq_boundaryProjectiveVertex p f hx hspanNormals
      hpowner t1 h1p h2p
  obtain ⟨u1, hu1mem, hu1⟩ :=
    exists_vertexFinset_eq_boundaryProjectiveVertex p f hx hspanNormals
      hpowner t2 h2p h3p
  have hu01 : u0 ≠ u1 := by
    intro huv
    subst u1
    have hvertices : boundaryProjectiveVertex f hx normal_cross hspanNormals t1 =
        boundaryProjectiveVertex f hx normal_cross hspanNormals t2 :=
      hu0.symm.trans hu1
    exact ht1t2
      (boundaryProjectiveVertex_injective f hx normal_cross hspanNormals hvertices)
  have hq1u0 : lineEval p.1 q1.1.1 u0 = 0 := by
    rw [← normalVec_dot_chartPoint]
    apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u0)).mp
    rw [hu0]
    exact boundaryProjectiveVertex_on_left f hx normal_cross hspanNormals t1
  have hq2u0 : lineEval p.1 (owner t2).1 u0 = 0 := by
    rw [← normalVec_dot_chartPoint]
    apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u0)).mp
    rw [hu0]
    exact boundaryProjectiveVertex_on_right f hx normal_cross hspanNormals t1
  have hq2u1 : lineEval p.1 (owner t2).1 u1 = 0 := by
    rw [← normalVec_dot_chartPoint]
    apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u1)).mp
    rw [hu1]
    exact boundaryProjectiveVertex_on_left f hx normal_cross hspanNormals t2
  have hq3u1 : lineEval p.1 q3.1.1 u1 = 0 := by
    rw [← normalVec_dot_chartPoint]
    apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero p.1 u1)).mp
    rw [hu1]
    exact boundaryProjectiveVertex_on_right f hx normal_cross hspanNormals t2
  have hparallel : ¬ Nonparallel p.1 q1.1.1 q3.1.1 := by
    intro hpar
    let qr : CrossingPair B p := ⟨(q1, q3), hpar⟩
    let u := indexedCrossing B p qr
    have huMem : u ∈ vertexFinset B p := indexedCrossing_mem B p qr
    have hq1u : lineEval p.1 q1.1.1 u = 0 := indexedCrossing_on_left B p qr
    have hq3u : lineEval p.1 q3.1.1 u = 0 := indexedCrossing_on_right B p qr
    have huu0 : u ≠ u0 := by
      intro huu0
      have hq3u0 : lineEval p.1 (owner t3).1 u0 = 0 := by
        rw [← huu0]
        simpa [q3, owner] using hq3u
      rcases boundaryOwner_index_eq_endpoint_of_lineEval_eq_zero
          p f hx hspanNormals t1 t3 u0 hu0
            hq3u0 with h | h
      · exact ht1t3 h.symm
      · exact ht2t3 h.symm
    have hcol := collinear3_of_mem_vertexFinset_of_affineSpan_ne_top p
      hspanVertices hu0mem huMem hu1mem
    have hq1u1 : lineEval p.1 q1.1.1 u1 = 0 :=
      lineEval_eq_zero_of_collinear_of_two p.1 q1.1.1 huu0.symm hcol
        hq1u0 hq1u
    have hq12 : q1.1.1 = (owner t2).1 :=
      owner_eq_of_lineEval_eq_zero_at_two_points p.1 q1.1.1 (owner t2).1
        hu01 hq1u0 hq1u1 hq2u0 hq2u1
    apply ht1t2
    apply howner
    exact Subtype.ext hq12
  have hcolp : ProjectiveDuality.Collinear3 p.1 q1.1.1 q3.1.1 :=
    by
      by_contra hncol
      exact hparallel ((nonparallel_iff_not_collinear _ _ _).2 hncol)
  have hstartP : Incident
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t) p.1 := by
    change OnProjectiveLine (normalVec p.1)
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t)
    rw [← htp]
    exact boundaryProjectiveVertex_on_left f hx normal_cross hspanNormals t
  have hstartQ3 : Incident
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t) q3.1.1 := by
    change OnProjectiveLine (normalVec q3.1.1)
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t)
    rw [boundaryProjectiveVertex, onProjectiveLine_mk_iff]
    change normalVec q3.1.1 ⬝ᵥ
      (normalVec (owner t).1 ⨯₃ normalVec (owner (s t)).1) = 0
    rw [show owner t = p by exact htp]
    change normalVec q3.1.1 ⬝ᵥ (normalVec p.1 ⨯₃ normalVec q1.1.1) = 0
    rw [ProjectiveArrangement.normalVec_dot_cross_eq_neg_orientation]
    dsimp [ProjectiveDuality.Collinear3] at hcolp
    dsimp [ProjectiveDuality.orientationDet] at hcolp ⊢
    linear_combination hcolp
  have hendQ3 : Incident
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t3) q3.1.1 := by
    change OnProjectiveLine (normalVec q3.1.1)
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t3)
    exact boundaryProjectiveVertex_on_left f hx normal_cross hspanNormals t3
  have hendP : Incident
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t3) p.1 := by
    change OnProjectiveLine (normalVec p.1)
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t3)
    have hright := boundaryProjectiveVertex_on_right
      f hx normal_cross hspanNormals t3
    change OnProjectiveLine (normalVec (owner (s t3)).1)
      (boundaryProjectiveVertex f hx normal_cross hspanNormals t3) at hright
    rw [show s t3 = t by exact hcycle, show owner t = p by exact htp] at hright
    exact hright
  have hpq3 : p.1 ≠ q3.1.1 := by
    intro h
    apply h3p
    exact Subtype.ext h.symm
  have hvertices : boundaryProjectiveVertex f hx normal_cross hspanNormals t =
      boundaryProjectiveVertex f hx normal_cross hspanNormals t3 :=
    eq_of_two_common_lines hpq3 hstartP hstartQ3 hendP hendQ3
  exact ht3t
    (boundaryProjectiveVertex_injective f hx normal_cross hspanNormals hvertices).symm

private theorem cyclicSucc_four_eq_self_of_card_eq_four
    {k : ℕ} (hk : k = 4) (r : Fin k) :
    Erdos957.cyclicSucc (Erdos957.cyclicSucc
      (Erdos957.cyclicSucc (Erdos957.cyclicSucc r))) = r := by
  subst k
  exact LeviCyclicDegenerate.cyclicSucc_four_eq_self r

/-- If the affine crossing set is contained in a proper affine subspace but
has more than one point, every incident face is still triangular.  The
three-consecutive-corner argument bounds its degree by four, and the exact
four-cycle argument excludes equality. -/
theorem incident_face_degree_eq_three_of_affineSpan_ne_top
    [Nonempty B] (p : B)
    (hspanNormals : Submodule.span ℝ
      (Set.range (fun q : B ↦ normalVec q.1)) = ⊤)
    (hspanVertices : affineSpan ℝ (vertexFinset B p : Set Point) ≠ ⊤)
    (f : StrictFace (fun q : B ↦ normalVec q.1))
    (hincident : LineFaceIncident (fun q : B ↦ normalVec q.1) p f) :
    strictFaceDegree (fun q : B ↦ normalVec q.1) f = 3 := by
  classical
  let n : B → SignVector.Vec3 := fun q ↦ normalVec q.1
  let x := faceWitness n f
  have hx : Realizes n f.1 x := faceWitness_realizes n f
  have hpowner : p ∈ edgeOwners n f.1 := by
    rw [mem_edgeOwners]
    apply (SignVectorArrangement.mem_faceEdgeOwners_iff_edgeFeasible_faceEdgeCode
      n f p).mp
    exact (SignVectorArrangement.mem_faceEdgeOwners_iff n f p).mpr hincident
  let owner : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x)) → B :=
    boundaryOwner f hx normal_cross hspanNormals
  have howner : Function.Injective owner := by
    intro i j hij
    apply (boundaryOwnerEquiv f hx normal_cross hspanNormals).injective
    exact Subtype.ext hij
  have hlefour : Erdos957.hullVertexCount (boundaryPolygon n f.1 x) ≤ 4 :=
    LeviCyclicDegenerate.card_le_four_of_three_consecutive_nonselected_corners_impossible
      owner howner p (by
        intro t h0 h1 h2 h3
        exact false_of_three_consecutive_nonselected_corners_of_affineSpan_ne_top
          p f hx hspanNormals hspanVertices hpowner t h0 h1 h2 h3)
  have hthree : 3 ≤ Erdos957.hullVertexCount (boundaryPolygon n f.1 x) := by
    rw [Erdos957.hullVertexCount,
      hullVertices_boundaryPolygon hx normal_cross]
    exact three_le_boundaryPolygon_card f hx normal_cross hspanNormals
  have hnotfour : Erdos957.hullVertexCount (boundaryPolygon n f.1 x) ≠ 4 := by
    intro hfour
    let pp : {i // i ∈ edgeOwners n f.1} := ⟨p, hpowner⟩
    obtain ⟨t, ht⟩ := (boundaryOwnerEquiv f hx normal_cross hspanNormals).surjective pp
    have htp : boundaryOwner f hx normal_cross hspanNormals t = p :=
      congrArg Subtype.val ht
    exact false_of_four_cycle_of_affineSpan_ne_top p f hx hspanNormals
      hspanVertices hpowner t htp
      (cyclicSucc_four_eq_self_of_card_eq_four hfour t)
  have hm : Erdos957.hullVertexCount (boundaryPolygon n f.1 x) = 3 := by
    omega
  change (faceEdges n f).card = 3
  rw [← boundaryPolygon_card_eq_faceEdges_card f hx normal_cross]
  rw [← hullVertices_boundaryPolygon hx normal_cross]
  exact hm

/-- If all affine crossings left after selecting `p` coincide, every face
incident with `p` is triangular.  Indeed, every cyclic corner not touching
the `p`-edge is the projectivization of that unique affine crossing, while
the projective boundary vertices are injectively indexed. -/
theorem incident_face_degree_eq_three_of_vertex_card_eq_one
    [Nonempty B] (p : B)
    (hspan : Submodule.span ℝ
      (Set.range (fun q : B ↦ normalVec q.1)) = ⊤)
    (hvertices : (vertexFinset B p).card = 1)
    (f : StrictFace (fun q : B ↦ normalVec q.1))
    (hincident : LineFaceIncident (fun q : B ↦ normalVec q.1) p f) :
    strictFaceDegree (fun q : B ↦ normalVec q.1) f = 3 := by
  classical
  let n : B → SignVector.Vec3 := fun q ↦ normalVec q.1
  let x := faceWitness n f
  have hx : Realizes n f.1 x := faceWitness_realizes n f
  have hpowner : p ∈ edgeOwners n f.1 := by
    rw [mem_edgeOwners]
    apply (SignVectorArrangement.mem_faceEdgeOwners_iff_edgeFeasible_faceEdgeCode
      n f p).mp
    exact (SignVectorArrangement.mem_faceEdgeOwners_iff n f p).mpr hincident
  obtain ⟨v, hV⟩ := Finset.card_eq_one.mp hvertices
  let owner : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x)) → B :=
    boundaryOwner f hx normal_cross hspan
  let vertex : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x)) →
      ℙ ℝ SignVector.Vec3 :=
    boundaryProjectiveVertex f hx normal_cross hspan
  let pv : ℙ ℝ SignVector.Vec3 :=
    Projectivization.mk ℝ (LeviAffineChart.chartPoint p.1 v)
      (chartPoint_ne_zero p.1 v)
  have howner : Function.Injective owner := by
    intro s t hst
    apply (boundaryOwnerEquiv f hx normal_cross hspan).injective
    exact Subtype.ext hst
  have hvertex : Function.Injective vertex :=
    boundaryProjectiveVertex_injective f hx normal_cross hspan
  have hconstant : ∀ t,
      owner t ≠ p → owner (Erdos957.cyclicSucc t) ≠ p → vertex t = pv := by
    intro t hleft hright
    obtain ⟨u, hu, huvertex⟩ :=
      exists_vertexFinset_eq_boundaryProjectiveVertex p f hx hspan hpowner t
        hleft hright
    have huv : u = v := by
      rw [hV] at hu
      simpa using hu
    subst u
    exact huvertex.symm
  have hcard : Erdos957.hullVertexCount (boundaryPolygon n f.1 x) ≤ 3 :=
    LeviCyclicDegenerate.card_le_three_of_nonselected_corners_constant
      owner vertex howner hvertex p pv hconstant
  have hthree : 3 ≤ Erdos957.hullVertexCount (boundaryPolygon n f.1 x) := by
    rw [Erdos957.hullVertexCount,
      hullVertices_boundaryPolygon hx normal_cross]
    exact three_le_boundaryPolygon_card f hx normal_cross hspan
  have hm : Erdos957.hullVertexCount (boundaryPolygon n f.1 x) = 3 := by
    omega
  change (faceEdges n f).card = 3
  rw [← boundaryPolygon_card_eq_faceEdges_card f hx normal_cross]
  rw [← hullVertices_boundaryPolygon hx normal_cross]
  exact hm

/-- The concurrent affine-crossing degeneracy still supplies at least six
spherical triangles: every face in the literal belt is triangular, and the
belt has at least eight slots. -/
theorem six_le_incident_triangles_of_vertex_card_eq_one
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (p : B) (hvertices : (vertexFinset B p).card = 1) :
    6 ≤ (Finset.univ.filter fun f : StrictFace
        (fun q : B ↦ normalVec q.1) ↦
      LineFaceIncident (fun q : B ↦ normalVec q.1) p f ∧
        strictFaceDegree (fun q : B ↦ normalVec q.1) f = 3).card := by
  classical
  let pa : ProjectiveBoundaryExtraction.Line B := ⟨a, ha⟩
  let pb : ProjectiveBoundaryExtraction.Line B := ⟨b, hb⟩
  have hab : pa ≠ pb := by
    intro h
    apply hncol
    have hab' : a = b := congrArg Subtype.val h
    simp [hab', ProjectiveDuality.Collinear3,
      ProjectiveDuality.orientationDet]
  let pick : OtherLineChoice (ProjectiveBoundaryExtraction.Line B) :=
    ProjectiveBoundaryExtraction.otherLineChoiceOfPair pa pb hab
  let : Nonempty (ProjectiveBoundaryExtraction.Line B) := ⟨p⟩
  apply ConcretePolarLineBelt.six_le_incident_triangles_of_all_incident_triangular
    B ha hb hc hncol pick p
  intro f hf
  exact incident_face_degree_eq_three_of_vertex_card_eq_one p
    (ProjectiveArrangement.span_normalVec_range_eq_top_of_noncollinear_triple
      B ha hb hc hncol) hvertices f hf

/-- The proper affine-span branch supplies six spherical triangles because
the preceding cyclic argument makes every face in the selected literal belt
triangular. -/
theorem six_le_incident_triangles_of_affineSpan_ne_top
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (p : B) (hspanVertices :
      affineSpan ℝ (vertexFinset B p : Set Point) ≠ ⊤) :
    6 ≤ (Finset.univ.filter fun f : StrictFace
        (fun q : B ↦ normalVec q.1) ↦
      LineFaceIncident (fun q : B ↦ normalVec q.1) p f ∧
        strictFaceDegree (fun q : B ↦ normalVec q.1) f = 3).card := by
  classical
  let pa : ProjectiveBoundaryExtraction.Line B := ⟨a, ha⟩
  let pb : ProjectiveBoundaryExtraction.Line B := ⟨b, hb⟩
  have hab : pa ≠ pb := by
    intro h
    apply hncol
    have hab' : a = b := congrArg Subtype.val h
    simp [hab', ProjectiveDuality.Collinear3,
      ProjectiveDuality.orientationDet]
  let pick : OtherLineChoice (ProjectiveBoundaryExtraction.Line B) :=
    ProjectiveBoundaryExtraction.otherLineChoiceOfPair pa pb hab
  let : Nonempty (ProjectiveBoundaryExtraction.Line B) := ⟨p⟩
  apply ConcretePolarLineBelt.six_le_incident_triangles_of_all_incident_triangular
    B ha hb hc hncol pick p
  intro f hf
  exact incident_face_degree_eq_three_of_affineSpan_ne_top p
    (ProjectiveArrangement.span_normalVec_range_eq_top_of_noncollinear_triple
      B ha hb hc hncol) hspanVertices f hf

/-- When the affine crossing set left after sending `p` to infinity spans
the plane, its convex hull has at least three vertices.  The three exterior
sector certificates are in distinct antipodal orbits, hence supply six
spherical triangular chambers incident with `p`. -/
theorem six_le_incident_triangles_of_affineSpan_eq_top
    (p : B)
    (hspan : affineSpan ℝ (vertexFinset B p : Set Point) = ⊤) :
    6 ≤ (Finset.univ.filter fun f : SignVector.StrictFace
        (fun a : B ↦ ProjectiveArrangement.normalVec a.1) ↦
      SignVectorArrangement.LineFaceIncident
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) p f ∧
        SignVectorArrangement.strictFaceDegree
          (fun a : B ↦ ProjectiveArrangement.normalVec a.1) f = 3).card := by
  classical
  let V := {v // v ∈ Erdos957.hullVertices (vertexFinset B p)}
  have hVcard : 3 ≤ Fintype.card V := by
    rw [show Fintype.card V =
        Erdos957.hullVertexCount (vertexFinset B p) by
      simp [V, Erdos957.hullVertexCount]]
    exact three_le_hullVertexCount_of_affineSpan_eq_top B p hspan
  let vertex : Fin 3 → V := fun t ↦
    (Fintype.equivFin V).symm ⟨t.1, lt_of_lt_of_le t.2 hVcard⟩
  have hvertex : Function.Injective vertex := by
    intro s t hst
    have hfin := (Fintype.equivFin V).symm.injective hst
    apply Fin.ext
    exact congrArg (fun x : Fin (Fintype.card V) ↦ x.1) hfin
  let face : Fin 3 → SignVector.StrictFace
      (fun a : B ↦ ProjectiveArrangement.normalVec a.1) := fun t ↦
    (hullVertexTriangleCertificate B p (vertex t)).face
  have hface : Function.Injective face := by
    intro s t hst
    apply hvertex
    exact hullVertexTriangleFace_injective B p hst
  let : Nonempty B := ⟨p⟩
  have hanti : ∀ s t, face s ≠
      SignVectorArrangement.antipodalStrictFace (face t) := by
    intro s t
    by_cases hst : s = t
    · subst t
      exact (SignVectorArrangement.antipodalStrictFace_ne (face s)).symm
    · exact hullVertexTriangleFace_ne_antipodal_of_ne B p
        (hvertex.ne (Ne.symm hst))
  apply SignVectorArrangement.six_le_incident_triangles_of_three_antipodal_orbits
    p face hface hanti
  · intro t
    exact (hullVertexTriangleCertificate B p (vertex t)).incident_and_degree_three.1
  · intro t
    exact (hullVertexTriangleCertificate B p (vertex t)).incident_and_degree_three.2

/-- The strengthened concrete Levi theorem: every represented dual line is
incident with at least three projective triangle orbits, equivalently six
spherical triangular strict faces. -/
theorem hasProjectiveSignVectorLeviProperty_of_noncollinear_triple
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    HasProjectiveSignVectorLeviProperty
      (fun q : B ↦ normalVec q.1) := by
  classical
  intro p
  by_cases hspanVertices :
      affineSpan ℝ (vertexFinset B p : Set Point) = ⊤
  · exact six_le_incident_triangles_of_affineSpan_eq_top p hspanVertices
  · exact six_le_incident_triangles_of_affineSpan_ne_top
      B ha hb hc hncol p hspanVertices

end Erdos735.LeviExteriorSector
