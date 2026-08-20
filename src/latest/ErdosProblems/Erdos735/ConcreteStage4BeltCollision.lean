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

import ErdosProblems.Erdos735.ConcreteStage4EndpointBeltClosure
import ErdosProblems.Erdos735.ConcreteStage4BeltNoncollision

/-!
# Collision-safe local geometry for the Stage-4 belt

When two distinct graph neighbors of one belt cell project to the same
cyclic interval, their two geometric incidences exhibit both endpoints of
that interval.  This file supplies the literal quadrangle bookkeeping used
to turn that fact into the directed successor relation required by the
occupied-belt argument.
-/

open Classical
noncomputable section

namespace Erdos735

namespace ABKPR.Data

universe uV uEd uF uL

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable {A : ABKPR.Data C}

/-- The boundary index at which a geometric helper attaches to a fixed
evil's bad quadrangle. -/
noncomputable def geometricFlankIndex
    {Line : Type uL} [Fintype Line] [DecidableEq Line]
    (edgeLine : Edge → Line)
    (e : A.EvilFace)
    (h : {h : A.HelpingPair // A.IsGeometricFlank edgeLine e h}) :
    Fin (C.faceDegree (A.across (A.evilDart e)).1) :=
  Classical.choose h.2.1

theorem geometricFlankIndex_spec
    {Line : Type uL} [Fintype Line] [DecidableEq Line]
    (edgeLine : Edge → Line) (e : A.EvilFace)
    (h : {h : A.HelpingPair // A.IsGeometricFlank edgeLine e h}) :
    CyclicAdjacentIndex (C := C) (A.across (A.evilDart e)).2
        (A.geometricFlankIndex edgeLine e h) ∧
      (A.across ⟨(A.across (A.evilDart e)).1,
        A.geometricFlankIndex edgeLine e h⟩).1 = h.1.face :=
  Classical.choose_spec h.2.1

@[simp] theorem endpointAdjacentIndex_eq_geometricFlankIndex
    {Line : Type uL} [Fintype Line] [DecidableEq Line]
    (edgeLine : Edge → Line) (e : A.EvilFace)
    (h : {h : A.HelpingPair // A.IsGeometricFlank edgeLine e h}) :
    A.endpointAdjacentIndex edgeLine h.1
        (⟨e, h.2⟩ : {e' : A.EvilFace //
          A.IsGeometricFlank edgeLine e' h.1}) =
      A.geometricFlankIndex edgeLine e h := by
  rfl

/-- For a fixed evil face, its two geometric helpers attach at different
cyclic boundary indices. -/
theorem geometricFlankIndex_injective
    {Line : Type uL} [Fintype Line] [DecidableEq Line]
    (edgeLine : Edge → Line)
    (hinj : ∀ f, Function.Injective
      (fun i ↦ edgeLine (A.boundaryEdge f i)))
    (e : A.EvilFace) :
    Function.Injective (A.geometricFlankIndex edgeLine e) := by
  intro h k hjk
  have hh := A.geometricFlankIndex_spec edgeLine e h
  have hk := A.geometricFlankIndex_spec edgeLine e k
  have hface : h.1.face = k.1.face := by
    calc
      h.1.face = (A.across ⟨(A.across (A.evilDart e)).1,
          A.geometricFlankIndex edgeLine e h⟩).1 := hh.2.symm
      _ = (A.across ⟨(A.across (A.evilDart e)).1,
          A.geometricFlankIndex edgeLine e k⟩).1 := by rw [hjk]
      _ = k.1.face := hk.2
  apply Subtype.ext
  rcases h with ⟨⟨hf, hi⟩, hhgeom⟩
  rcases k with ⟨⟨kf, ki⟩, hkgeom⟩
  change hf = kf at hface
  subst kf
  change (⟨hf, hi⟩ : A.HelpingPair) = ⟨hf, ki⟩
  congr 1
  apply Subtype.ext
  apply hinj hf
  exact hhgeom.2.trans hkgeom.2.symm

/-- The concrete attachment indices of two distinct geometric helpers at
one evil face are distinct, independently of how the existential flank
witnesses were chosen. -/
theorem geometric_flank_indices_ne_of_helpers_ne
    {Line : Type uL} [Fintype Line] [DecidableEq Line]
    (edgeLine : Edge → Line)
    (hinj : ∀ f, Function.Injective
      (fun i ↦ edgeLine (A.boundaryEdge f i)))
    (e : A.EvilFace) {h k : A.HelpingPair}
    (hh : A.IsGeometricFlank edgeLine e h)
    (hk : A.IsGeometricFlank edgeLine e k) (hhk : h ≠ k)
    {j r : Fin (C.faceDegree (A.across (A.evilDart e)).1)}
    (hjface : (A.across ⟨(A.across (A.evilDart e)).1, j⟩).1 = h.face)
    (hrface : (A.across ⟨(A.across (A.evilDart e)).1, r⟩).1 = k.face) :
    j ≠ r := by
  intro hjr
  apply hhk
  have hface : h.face = k.face := by
    calc
      h.face = (A.across ⟨(A.across (A.evilDart e)).1, j⟩).1 := hjface.symm
      _ = (A.across ⟨(A.across (A.evilDart e)).1, r⟩).1 := by rw [hjr]
      _ = k.face := hrface
  rcases h with ⟨hf, hi⟩
  rcases k with ⟨kf, ki⟩
  change hf = kf at hface
  subst kf
  change (⟨hf, hi⟩ : A.HelpingPair) = ⟨hf, ki⟩
  congr 1
  apply Subtype.ext
  apply hinj hf
  exact hh.2.trans hk.2.symm

/-- The two distinct boundary edges adjacent to one edge of a quadrangle
have different endpoints away from that distinguished edge. -/
theorem far_vertices_ne_of_distinct_adjacent
    {f : Face} (hfour : C.faceDegree f = 4)
    (i j k : Fin (C.faceDegree f))
    (hij : CyclicAdjacentIndex (C := C) i j)
    (hik : CyclicAdjacentIndex (C := C) i k)
    (hjk : j ≠ k) {v u : Vertex}
    (hvj : v ∈ C.edgeVertices (A.boundaryEdge f j))
    (huj : u ∈ C.edgeVertices (A.boundaryEdge f k))
    (hvnot : v ∉ C.edgeVertices (A.boundaryEdge f i))
    (hunot : u ∉ C.edgeVertices (A.boundaryEdge f i)) :
    v ≠ u := by
  intro hvu
  subst u
  rw [A.boundaryEdge_vertices] at hvj huj hvnot hunot
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvj huj hvnot hunot
  rcases hij with hij | hij
  · rcases hik with hik | hik
    · exact hjk (hij.symm.trans hik)
    · rcases hvj with hvj | hvj
      · exact hvnot (Or.inr (by simpa [hij] using hvj))
      · rcases huj with huj | huj
        · have hindex := A.boundaryVertex_injective f (hvj.symm.trans huj)
          exact (cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
            C hfour i k (Or.inr hik))
              (hindex.symm.trans (congrArg (faceSucc C f) hij).symm)
        · exact hunot (Or.inl (by simpa [hik] using huj))
  · rcases hik with hik | hik
    · rcases hvj with hvj | hvj
      · rcases huj with huj | huj
        · exact hunot (Or.inr (by simpa [hik] using huj))
        · have hindex := A.boundaryVertex_injective f (hvj.symm.trans huj)
          exact (cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
            C hfour i j (Or.inr hij))
              (hindex.trans (congrArg (faceSucc C f) hik).symm)
      · exact hvnot (Or.inl (by simpa [hij] using hvj))
    · exact hjk ((faceSucc_injective C f) (hij.trans hik.symm))

/-- A vertex common to a cyclic neighbor of a quadrangle edge and the
opposite edge is the far endpoint, hence is not on the original edge. -/
theorem not_mem_path_of_mem_adjacent_and_opposite
    {f : Face} (hfour : C.faceDegree f = 4)
    (i j : Fin (C.faceDegree f))
    (hij : CyclicAdjacentIndex (C := C) i j) {v : Vertex}
    (hvj : v ∈ C.edgeVertices (A.boundaryEdge f j))
    (hvopp : v ∈ C.edgeVertices
      (A.boundaryEdge f (faceSucc C f (faceSucc C f i)))) :
    v ∉ C.edgeVertices (A.boundaryEdge f i) := by
  rw [A.boundaryEdge_vertices] at hvj hvopp ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvj hvopp ⊢
  intro hvpath
  rcases hij with hij | hij
  · rcases hvj with hvj | hvj
    · rcases hvopp with hvopp | hvopp
      · have hidx := A.boundaryVertex_injective f (hvj.symm.trans hvopp)
        exact faceSucc_ne_of_faceDegree_eq_four C hfour
          (faceSucc C f i) (hij.trans hidx).symm
      · have hidx := A.boundaryVertex_injective f (hvj.symm.trans hvopp)
        have hbad : i = faceSucc C f (faceSucc C f i) := by
          exact (faceSucc_injective C f) (hij.trans hidx)
        exact secondSucc_ne_of_faceDegree_eq_four C hfour i hbad.symm
    · rcases hvpath with hvpath | hvpath
      · have hidx := A.boundaryVertex_injective f (hvj.symm.trans hvpath)
        exact secondSucc_ne_of_faceDegree_eq_four C hfour i
          ((congrArg (faceSucc C f) hij).trans hidx)
      · have hidx := A.boundaryVertex_injective f (hvj.symm.trans hvpath)
        exact faceSucc_ne_of_faceDegree_eq_four C hfour
          (faceSucc C f i) ((congrArg (faceSucc C f) hij).trans hidx)
  · rcases hvj with hvj | hvj
    · rcases hvpath with hvpath | hvpath
      · have hidx := A.boundaryVertex_injective f (hvj.symm.trans hvpath)
        exact ne_of_cyclicAdjacent_of_faceDegree_eq_four C hfour i j
          (Or.inr hij) hidx.symm
      · have hidx := A.boundaryVertex_injective f (hvj.symm.trans hvpath)
        have hbad : faceSucc C f (faceSucc C f i) = i := by
          rw [← hidx, hij]
        exact secondSucc_ne_of_faceDegree_eq_four C hfour i hbad
    · rcases hvopp with hvopp | hvopp
      · have hidx := A.boundaryVertex_injective f (hvj.symm.trans hvopp)
        exact secondSucc_ne_of_faceDegree_eq_four C hfour i
          (hij.symm.trans hidx).symm
      · have hidx := A.boundaryVertex_injective f (hvj.symm.trans hvopp)
        have hbad : faceSucc C f i = i := by
          have h := congrArg (faceSucc C f) (hij.symm.trans hidx)
          rw [faceSucc_four_of_faceDegree_eq_four C hfour] at h
          exact h
        exact faceSucc_ne_of_faceDegree_eq_four C hfour i hbad

end ABKPR.Data

namespace ConcreteStage4BeltCollision

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement
open SignVector.ProjectiveEdgeEndpointEquiv
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev Line := ProjectiveBoundaryExtraction.Line (B (P := P))
private abbrev Vertex := ProjectiveBoundaryExtraction.Vertex (B (P := P))

/-- Forgetting the spherical sheet is injective on the two endpoints of a
single strict polar edge. -/
theorem fst_injective_on_concreteEdgeVertices
    (e : StrictEdge (normals (B (P := P)))) :
    Set.InjOn Prod.fst
      (ConcretePolarEdgeVertices.concreteEdgeVertices
        (ConcretePolarABKPRData.hspan ha hb hd hncol) e :
          Set (OrientedVertex (B (P := P)))) := by
  rw [← Finset.card_image_iff]
  rw [ConcretePolarEdgeVertices.concreteEdgeVertices_card]
  rw [← ConcreteStrictEdgeCyclic.strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
    (B (P := P)) ha hb hd hncol
    (ConcreteStage4OccupiedBelt.pick ha hb hncol)
    (ConcretePolarABKPRData.hspan ha hb hd hncol)]
  exact cyclicEdgeVertices_card
    (Finset.univ : Finset (Vertex (P := P)))
    (OnLine (B (P := P))) (vertexCoord (B (P := P)))
    (vertexCoord_injective (B (P := P)))
    (two_vertices_on_every_line (B (P := P)) ha hb hd hncol) _

/-- Literal oriented endpoint membership projects to membership in the
genuine cyclic interval representing the strict edge. -/
theorem fst_mem_cyclicEdgeVertices_of_mem_concrete
    (pick : OtherLineChoice (Line (P := P)))
    (e : StrictEdge (normals (B (P := P))))
    {v : OrientedVertex (B (P := P))}
    (hv : v ∈ ConcretePolarEdgeVertices.concreteEdgeVertices
      (ConcretePolarABKPRData.hspan ha hb hd hncol) e) :
    v.1 ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        pick e).1 := by
  rw [ConcreteStrictEdgeCyclic.strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
    (B (P := P)) ha hb hd hncol pick
    (ConcretePolarABKPRData.hspan ha hb hd hncol)]
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- The far-corner witness for one evil--helper incidence, retaining the
separator index and the fact that the corner is not on the path edge. -/
theorem flank_shared_vertex_data
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    ∃ j : Fin ((C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1),
      ABKPR.Data.CyclicAdjacentIndex
          ((D hred ha hb hd hncol).across
            ((D hred ha hb hd hncol).evilDart e)).2 j ∧
      ((D hred ha hb hd hncol).across ⟨
        ((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = h.face ∧
      ∃ v : OrientedVertex (B (P := P)),
        v ∈ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ((D hred ha hb hd hncol).evilDart e)).1 j) ∧
        v ∈ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).evilBadOppositeDart e).1
            ((D hred ha hb hd hncol).evilBadOppositeDart e).2) ∧
        v ∈ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).helpingOppositeDart h).1
            ((D hred ha hb hd hncol).helpingOppositeDart h).2) ∧
        v ∉ (C ha hb hd hncol).edgeVertices
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ((D hred ha hb hd hncol).evilDart e)).1
            ((D hred ha hb hd hncol).across
              ((D hred ha hb hd hncol).evilDart e)).2) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  obtain ⟨j, hadj, hface, v, hvsep, hvbad, hvhelp⟩ :=
    ConcreteOppositeLineCoherence.oppositeDarts_share_orientedVertex_with_separator_of_adj
      hred ha hb hd hncol L hedge heh
  have hnot := DD.not_mem_path_of_mem_adjacent_and_opposite
    (DD.evilDart_across_bad e).1.1 bad.2 j hadj hvsep hvbad
  exact ⟨j, hadj, hface, v, hvsep, hvbad, hvhelp, hnot⟩

/-- The two distinct helpers adjacent to one evil meet its opposite edge
at its two distinct oriented endpoints. -/
theorem two_helpers_distinct_shared_vertices
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h k : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) (hek : L.Adj e k) (hhk : h ≠ k) :
    ∃ v u : OrientedVertex (B (P := P)), v ≠ u ∧
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).evilBadOppositeDart e).1
          ((D hred ha hb hd hncol).evilBadOppositeDart e).2) ∧
      u ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).evilBadOppositeDart e).1
          ((D hred ha hb hd hncol).evilBadOppositeDart e).2) ∧
      v ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).helpingOppositeDart h).1
          ((D hred ha hb hd hncol).helpingOppositeDart h).2) ∧
      u ∈ (C ha hb hd hncol).edgeVertices
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).helpingOppositeDart k).1
          ((D hred ha hb hd hncol).helpingOppositeDart k).2) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  obtain ⟨j, hjadj, hjface, v, hvj, hvbad, hvh, hvnot⟩ :=
    flank_shared_vertex_data hred ha hb hd hncol L hedge heh
  obtain ⟨r, hradj, hrface, u, hur, hubad, huk, hunot⟩ :=
    flank_shared_vertex_data hred ha hb hd hncol L hedge hek
  obtain ⟨sideh, hsideh⟩ := heh
  obtain ⟨sidek, hsidek⟩ := hek
  have hgeomh := L.evilFlank_geometric e sideh h hsideh
  have hgeomk := L.evilFlank_geometric e sidek k hsidek
  have hgeomh' : DD.IsGeometricFlank
      ConcretePolarFlankBounds.edgeLine e h := by
    simpa only [hedge] using hgeomh
  have hgeomk' : DD.IsGeometricFlank
      ConcretePolarFlankBounds.edgeLine e k := by
    simpa only [hedge] using hgeomk
  have hjr : j ≠ r := DD.geometric_flank_indices_ne_of_helpers_ne
    ConcretePolarFlankBounds.edgeLine
    (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol) e hgeomh' hgeomk' hhk hjface hrface
  have hvu : v ≠ u := DD.far_vertices_ne_of_distinct_adjacent
    (DD.evilDart_across_bad e).1.1 bad.2 j r hjadj hradj hjr
    hvj hur hvnot hunot
  exact ⟨v, u, hvu, hvbad, hubad, hvh, huk⟩

/-- Projective cyclic-edge form of the preceding two-helper endpoint
statement. -/
theorem two_helpers_distinct_projective_vertices
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h k : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) (hek : L.Adj e k) (hhk : h ≠ k) :
    ∃ v u : Vertex (P := P), v ≠ u ∧
      v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4BeltStep.evilOppositeBeltEdge
          hred ha hb hd hncol pick L hedge e).1.1 ∧
      u ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4BeltStep.evilOppositeBeltEdge
          hred ha hb hd hncol pick L hedge e).1.1 ∧
      v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
          hred ha hb hd hncol pick L hedge heh).1.1 ∧
      u ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
          hred ha hb hd hncol pick L hedge hek).1.1 := by
  let DD := D hred ha hb hd hncol
  let edgeE := DD.boundaryEdge (DD.evilBadOppositeDart e).1
    (DD.evilBadOppositeDart e).2
  let edgeH := DD.boundaryEdge (DD.helpingOppositeDart h).1
    (DD.helpingOppositeDart h).2
  let edgeK := DD.boundaryEdge (DD.helpingOppositeDart k).1
    (DD.helpingOppositeDart k).2
  obtain ⟨v, u, hvu, hvE, huE, hvH, huK⟩ :=
    two_helpers_distinct_shared_vertices
      hred ha hb hd hncol L hedge heh hek hhk
  have hvu' : v.1 ≠ u.1 := by
    intro h
    exact hvu (fst_injective_on_concreteEdgeVertices
      ha hb hd hncol edgeE hvE huE h)
  refine ⟨v.1, u.1, hvu', ?_, ?_, ?_, ?_⟩
  · exact fst_mem_cyclicEdgeVertices_of_mem_concrete
      ha hb hd hncol pick edgeE hvE
  · exact fst_mem_cyclicEdgeVertices_of_mem_concrete
      ha hb hd hncol pick edgeE huE
  · exact fst_mem_cyclicEdgeVertices_of_mem_concrete
      ha hb hd hncol pick edgeH hvH
  · exact fst_mem_cyclicEdgeVertices_of_mem_concrete
      ha hb hd hncol pick edgeK huK

end ConcreteStage4BeltCollision

end Erdos735
