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

import ErdosProblems.Erdos735.ConcreteOppositeLineCoherence
import ErdosProblems.Erdos735.ConcretePolarLineBelt
import ErdosProblems.Erdos735.ConcretePolarAcrossSquare

/-!
# One alternating Stage-4 step in the literal line belt

For an evil--helper adjacency, opposite-line coherence puts the opposite
edges of the bad and helping quadrangles on one projective line.  The local
far-corner argument says that the two literal edges share a projective
endpoint.  Transport through the owner-preserving strict-edge/cyclic-edge
equivalence therefore makes them consecutive intervals in the fixed-owner
line belt.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4BeltStep

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement
open SignVector.ProjectiveEdgeEndpointEquiv
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices

universe uV uL

/-- Two cyclic intervals on the same finite cyclically ordered line which
share an endpoint are either the same interval or literal successor
intervals in one of the two orientations. -/
theorem cyclicEdges_eq_or_end_start
    {V : Type uV} {Line : Type uL}
    [Fintype V] [DecidableEq V] [Fintype Line] [DecidableEq Line]
    (vertices : Finset V) (onLine : V → Line → Prop)
    [DecidableRel onLine] (coord : V → ℝ)
    (hinj : Set.InjOn coord (vertices : Set V))
    (e e' : CyclicSkeletonEdge vertices onLine)
    (hline : cyclicEdgeLine e = cyclicEdgeLine e')
    (v : V)
    (hv : v ∈ cyclicEdgeVertices vertices onLine coord e)
    (hv' : v ∈ cyclicEdgeVertices vertices onLine coord e') :
    e = e' ∨
      cyclicEdgeFinish vertices onLine coord e = cyclicEdgeStart e' ∨
      cyclicEdgeFinish vertices onLine coord e' = cyclicEdgeStart e := by
  rcases e with ⟨l, p⟩
  rcases e' with ⟨l', p'⟩
  change l = l' at hline
  subst l'
  have edge_eq_of_start_eq
      (hs : cyclicEdgeStart (⟨l, p⟩ : CyclicSkeletonEdge vertices onLine) =
        cyclicEdgeStart (⟨l, p'⟩ : CyclicSkeletonEdge vertices onLine)) :
      (⟨l, p⟩ : CyclicSkeletonEdge vertices onLine) = ⟨l, p'⟩ := by
    congr 1
    exact Subtype.ext hs
  simp only [cyclicEdgeVertices, Finset.mem_insert,
    Finset.mem_singleton] at hv hv'
  rcases hv with hv | hv <;> rcases hv' with hv' | hv'
  · left
    exact edge_eq_of_start_eq (hv.symm.trans hv')
  · right; right
    exact hv'.symm.trans hv
  · right; left
    exact hv.symm.trans hv'
  · left
    apply edge_eq_of_start_eq
    have hfinish : cyclicEdgeFinish vertices onLine coord
        (⟨l, p⟩ : CyclicSkeletonEdge vertices onLine) =
      cyclicEdgeFinish vertices onLine coord
        (⟨l, p'⟩ : CyclicSkeletonEdge vertices onLine) :=
      hv.symm.trans hv'
    have hspec' := cyclicEdgeFinish_spec vertices onLine coord
      (⟨l, p'⟩ : CyclicSkeletonEdge vertices onLine)
    rw [← hfinish] at hspec'
    apply ChartOrder.cyclicConsecutive_left_unique coord
      (verticesOn vertices onLine l)
      (hinj.mono (Finset.filter_subset _ _))
    · exact cyclicEdgeFinish_spec vertices onLine coord
        (⟨l, p⟩ : CyclicSkeletonEdge vertices onLine)
    · exact hspec'

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

/-- The lifted cyclic interval representing the edge opposite an evil's
path edge, regarded as an interval on its opposite owner line. -/
noncomputable def evilOppositeBeltEdge
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace) :
    ConcretePolarLineBelt.LiftedCyclicEdgeOn (B (P := P))
      (ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) L e) := by
  let DD := D hred ha hb hd hncol
  let edge := DD.boundaryEdge (DD.evilBadOppositeDart e).1
    (DD.evilBadOppositeDart e).2
  refine ⟨strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick edge, ?_⟩
  rw [strictEdgeLiftedCyclicEquiv_line]
  unfold ABKPR.Data.evilOppositeLine
  rw [hedge]
  rfl

/-- The lifted cyclic interval representing the helping opposite edge,
placed in the same owner fiber as an adjacent evil's opposite edge. -/
noncomputable def helperOppositeBeltEdgeOfAdj
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    ConcretePolarLineBelt.LiftedCyclicEdgeOn (B (P := P))
      (ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) L e) := by
  let DD := D hred ha hb hd hncol
  let edge := DD.boundaryEdge (DD.helpingOppositeDart h).1
    (DD.helpingOppositeDart h).2
  refine ⟨strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick edge, ?_⟩
  rw [strictEdgeLiftedCyclicEquiv_line]
  have hcoh := (ConcreteOppositeLineCoherence.oppositeLineCoherence
    hred ha hb hd hncol L hedge).eq_of_adj e h heh
  change ConcretePolarFlankBounds.edgeLine edge =
    ABKPR.Data.evilOppositeLine DD L e
  calc
    ConcretePolarFlankBounds.edgeLine edge =
        ABKPR.Data.helperOppositeLine DD L h := by
      unfold ABKPR.Data.helperOppositeLine
      rw [hedge]
    _ = ABKPR.Data.evilOppositeLine DD L e := hcoh.symm

/-- The two fixed-owner cyclic intervals attached to one evil--helper
incidence share a genuine projective endpoint.  In the cyclic skeleton this
is the exact local successor/consecutiveness relation used to propagate
along the alternating deficient component. -/
theorem oppositeBeltEdges_share_endpoint_of_adj
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    ∃ v : Vertex (P := P),
      v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (evilOppositeBeltEdge hred ha hb hd hncol pick L hedge e).1.1 ∧
      v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (helperOppositeBeltEdgeOfAdj hred ha hb hd hncol
          pick L hedge heh).1.1 := by
  let DD := D hred ha hb hd hncol
  obtain ⟨v, hve, hvh⟩ :=
    ConcreteOppositeLineCoherence.oppositeDarts_share_orientedVertex_of_adj
      hred ha hb hd hncol L hedge heh
  refine ⟨v.1, ?_, ?_⟩
  · change v.1 ∈ cyclicEdgeVertices
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick
        (DD.boundaryEdge (DD.evilBadOppositeDart e).1
          (DD.evilBadOppositeDart e).2)).1
    rw [ConcreteStrictEdgeCyclic.strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
      (B (P := P)) ha hb hd hncol pick
      (ConcretePolarABKPRData.hspan ha hb hd hncol)]
    exact Finset.mem_image.mpr ⟨v, hve, rfl⟩
  · change v.1 ∈ cyclicEdgeVertices
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick
        (DD.boundaryEdge (DD.helpingOppositeDart h).1
          (DD.helpingOppositeDart h).2)).1
    rw [ConcreteStrictEdgeCyclic.strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
      (B (P := P)) ha hb hd hncol pick
      (ConcretePolarABKPRData.hspan ha hb hd hncol)]
    exact Finset.mem_image.mpr ⟨v, hvh, rfl⟩

/-- Opposite boundary edges belonging to adjacent evil and helping cells
are distinct as spherical strict edges.  Otherwise the helping face would
be the face across two distinct edges of the bad quadrangle. -/
theorem oppositeStrictEdges_ne_of_adj
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    (D hred ha hb hd hncol).boundaryEdge
        ((D hred ha hb hd hncol).evilBadOppositeDart e).1
        ((D hred ha hb hd hncol).evilBadOppositeDart e).2 ≠
      (D hred ha hb hd hncol).boundaryEdge
        ((D hred ha hb hd hncol).helpingOppositeDart h).1
        ((D hred ha hb hd hncol).helpingOppositeDart h).2 := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  intro hopEq
  obtain ⟨j, hadj, hface, _v, _hvsep, _hvbad, _hvhelp⟩ :=
    ConcreteOppositeLineCoherence.oppositeDarts_share_orientedVertex_with_separator_of_adj
      hred ha hb hd hncol L hedge heh
  have hbad : DD.IsBadTwoQuadrangle bad.1 := DD.evilDart_across_bad e
  have hopen_ne_j : (DD.evilBadOppositeDart e).2 ≠ j := by
    change ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 bad.2) ≠ j
    exact (ABKPR.cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
      CC hbad.1.1 bad.2 j hadj).symm
  have hhelp_ne_bad : h.face ≠ bad.1 := by
    intro heq
    exact DD.across_otherFace ⟨bad.1, j⟩ (hface.trans heq)
  have hacrossOpp :
      (DD.across (DD.evilBadOppositeDart e)).1 = h.face := by
    exact DD.across_face_eq_of_boundaryEdge_eq hopEq hhelp_ne_bad
  have hne := ConcretePolarABKPRData.concreteData_across_faces_ne
    hred ha hb hd hncol bad.1 (DD.evilBadOppositeDart e).2 j hopen_ne_j
  exact hne (hacrossOpp.trans hface.symm)

/-- The projective cyclic intervals attached to an adjacent evil/helper
pair are distinct.  Equality of projective intervals makes the strict
edges equal or antipodal; the first case is excluded above, and the second
by their checked common oriented endpoint. -/
theorem oppositeBeltEdges_ne_of_adj
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    (evilOppositeBeltEdge
      hred ha hb hd hncol pick L hedge e).1.1 ≠
      (helperOppositeBeltEdgeOfAdj
        hred ha hb hd hncol pick L hedge heh).1.1 := by
  let DD := D hred ha hb hd hncol
  let edgeE := DD.boundaryEdge (DD.evilBadOppositeDart e).1
    (DD.evilBadOppositeDart e).2
  let edgeH := DD.boundaryEdge (DD.helpingOppositeDart h).1
    (DD.helpingOppositeDart h).2
  intro hbase
  have hbase' :
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick edgeE).1 =
        (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick edgeH).1 :=
    hbase
  rcases ConcretePolarLineBelt.eq_or_antipodal_of_liftedCyclic_base_eq
      (B (P := P)) ha hb hd hncol pick edgeE edgeH hbase' with heq | heq
  · exact (oppositeStrictEdges_ne_of_adj
      hred ha hb hd hncol L hedge heh) heq.symm
  · obtain ⟨v, hvE, hvH⟩ :=
      ConcreteOppositeLineCoherence.oppositeDarts_share_orientedVertex_of_adj
        hred ha hb hd hncol L hedge heh
    apply ConcretePolarLineBelt.concreteEdgeVertices_antipodal_disjoint
      (B := B (P := P)) (ConcretePolarABKPRData.hspan ha hb hd hncol) edgeE v hvE
    change v ∈ ConcretePolarEdgeVertices.concreteEdgeVertices
      (ConcretePolarABKPRData.hspan ha hb hd hncol) edgeH at hvH
    rw [heq] at hvH
    exact hvH

/-- Successor form of `oppositeBeltEdges_share_endpoint_of_adj`: the two
fixed-owner cyclic intervals are equal, or the terminal vertex of one is
the initial vertex of the other. -/
theorem oppositeBeltEdges_eq_or_end_start_of_adj
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e : (D hred ha hb hd hncol).EvilFace}
    {h : (D hred ha hb hd hncol).HelpingPair}
    (heh : L.Adj e h) :
    let ee := (evilOppositeBeltEdge
      hred ha hb hd hncol pick L hedge e).1.1
    let eh := (helperOppositeBeltEdgeOfAdj
      hred ha hb hd hncol pick L hedge heh).1.1
    ee = eh ∨
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P))) ee =
        cyclicEdgeStart eh ∨
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P))) eh =
        cyclicEdgeStart ee := by
  let ee := (evilOppositeBeltEdge
    hred ha hb hd hncol pick L hedge e).1.1
  let eh := (helperOppositeBeltEdgeOfAdj
    hred ha hb hd hncol pick L hedge heh).1.1
  obtain ⟨v, hve, hvh⟩ := oppositeBeltEdges_share_endpoint_of_adj
    hred ha hb hd hncol pick L hedge heh
  have hline : cyclicEdgeLine ee = cyclicEdgeLine eh := by
    exact (evilOppositeBeltEdge
      hred ha hb hd hncol pick L hedge e).2.trans
        (helperOppositeBeltEdgeOfAdj
          hred ha hb hd hncol pick L hedge heh).2.symm
  exact cyclicEdges_eq_or_end_start
    (Finset.univ : Finset (Vertex (P := P)))
    (OnLine (B (P := P))) (vertexCoord (B (P := P)))
    (vertexCoord_injective (B (P := P))) ee eh hline v hve hvh

/-- The boundary index of the unique edge on the evil opposite line in a
triangular flank.  The choice is backed by the literal far-corner bridge. -/
noncomputable def triangleFlankOppositeIndex
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (htri : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = 3) :
    Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1) :=
  Classical.choose
    (ConcreteOppositeLineCoherence.triangleFlank_oppositeEdge_bridge
      hred ha hb hd hncol L hedge e j hadj htri)

/-- The endpoint triangle's opposite-owner edge as a slot in the same
fixed-owner lifted cyclic belt as the evil bad-opposite edge. -/
noncomputable def triangleFlankBeltEdge
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (htri : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = 3) :
    ConcretePolarLineBelt.LiftedCyclicEdgeOn (B (P := P))
      (ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) L e) := by
  let DD := D hred ha hb hd hncol
  let flank := DD.across ⟨(DD.across (DD.evilDart e)).1, j⟩
  let u := triangleFlankOppositeIndex
    hred ha hb hd hncol L hedge e j hadj htri
  refine ⟨strictEdgeLiftedCyclicEquiv (B (P := P))
    ha hb hd hncol pick (DD.boundaryEdge flank.1 u), ?_⟩
  rw [strictEdgeLiftedCyclicEquiv_line]
  exact (Classical.choose_spec
    (ConcreteOppositeLineCoherence.triangleFlank_oppositeEdge_bridge
      hred ha hb hd hncol L hedge e j hadj htri)).1

/-- The endpoint-triangle interval contains the literal intersection of
the evil path line and its opposite line.  This is the endpoint of the
interval not supplied by the bad-quadrangle far-corner bridge. -/
theorem triangleFlankBeltEdge_has_path_crossing
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (htri : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = 3) :
    ∃ v : Vertex (P := P),
      v ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P)))
        (triangleFlankBeltEdge
          hred ha hb hd hncol pick L hedge e j hadj htri).1.1 ∧
      OnLine (B (P := P)) v
        (L.edgeLine ((D hred ha hb hd hncol).boundaryEdge
          e.1 ((D hred ha hb hd hncol).evilIndex e))) := by
  let DD := D hred ha hb hd hncol
  let flank := DD.across ⟨(DD.across (DD.evilDart e)).1, j⟩
  let uOpp := triangleFlankOppositeIndex
    hred ha hb hd hncol L hedge e j hadj htri
  have huOpp := (Classical.choose_spec
    (ConcreteOppositeLineCoherence.triangleFlank_oppositeEdge_bridge
      hred ha hb hd hncol L hedge e j hadj htri)).1
  obtain ⟨uPath, hPathOwner, _hne, v, hvOpp, hvPath⟩ :=
    ConcreteOppositeLineCoherence.triangleFlank_pathEdge_bridge
      hred ha hb hd hncol L hedge e j hadj htri uOpp huOpp
  refine ⟨v.1, ?_, ?_⟩
  · change v.1 ∈ cyclicEdgeVertices
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick
        (DD.boundaryEdge flank.1 uOpp)).1
    rw [ConcreteStrictEdgeCyclic.strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
      (B (P := P)) ha hb hd hncol pick
      (ConcretePolarABKPRData.hspan ha hb hd hncol)]
    exact Finset.mem_image.mpr ⟨v, hvOpp, rfl⟩
  · have hvOwner : OnLine (B (P := P)) v.1
        (ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge flank.1 uPath)) :=
      concreteEdgeVertex_on_support
        (ConcretePolarABKPRData.hspan ha hb hd hncol)
        (DD.boundaryEdge flank.1 uPath) v hvPath
    rw [← hedge] at hvOwner
    rw [hPathOwner] at hvOwner
    exact hvOwner

/-- The triangular endpoint-flank interval is equal or consecutive to the
evil bad-opposite interval.  This is the boundary analogue of
`oppositeBeltEdges_eq_or_end_start_of_adj`. -/
theorem triangleFlankBeltEdge_eq_or_end_start
    (pick : OtherLineChoice (Line (P := P)))
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (htri : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = 3) :
    let eb := (evilOppositeBeltEdge
      hred ha hb hd hncol pick L hedge e).1.1
    let et := (triangleFlankBeltEdge
      hred ha hb hd hncol pick L hedge e j hadj htri).1.1
    eb = et ∨
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P))) eb =
        cyclicEdgeStart et ∨
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P))) et =
        cyclicEdgeStart eb := by
  let DD := D hred ha hb hd hncol
  let flank := DD.across ⟨(DD.across (DD.evilDart e)).1, j⟩
  let u := triangleFlankOppositeIndex
    hred ha hb hd hncol L hedge e j hadj htri
  let eb := (evilOppositeBeltEdge
    hred ha hb hd hncol pick L hedge e).1.1
  let et := (triangleFlankBeltEdge
    hred ha hb hd hncol pick L hedge e j hadj htri).1.1
  have hspec := Classical.choose_spec
    (ConcreteOppositeLineCoherence.triangleFlank_oppositeEdge_bridge
      hred ha hb hd hncol L hedge e j hadj htri)
  let v := Classical.choose hspec.2
  have hvbad := (Classical.choose_spec hspec.2).2.1
  have hvtri := (Classical.choose_spec hspec.2).2.2.1
  have hveb : v.1 ∈ cyclicEdgeVertices
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P))) eb := by
    change v.1 ∈ cyclicEdgeVertices
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick
        (DD.boundaryEdge (DD.evilBadOppositeDart e).1
          (DD.evilBadOppositeDart e).2)).1
    rw [ConcreteStrictEdgeCyclic.strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
      (B (P := P)) ha hb hd hncol pick
      (ConcretePolarABKPRData.hspan ha hb hd hncol)]
    exact Finset.mem_image.mpr ⟨v, hvbad, rfl⟩
  have hvet : v.1 ∈ cyclicEdgeVertices
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P))) et := by
    change v.1 ∈ cyclicEdgeVertices
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol pick
        (DD.boundaryEdge flank.1 u)).1
    rw [ConcreteStrictEdgeCyclic.strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
      (B (P := P)) ha hb hd hncol pick
      (ConcretePolarABKPRData.hspan ha hb hd hncol)]
    exact Finset.mem_image.mpr ⟨v, hvtri, rfl⟩
  have hline : cyclicEdgeLine eb = cyclicEdgeLine et :=
    (evilOppositeBeltEdge hred ha hb hd hncol pick L hedge e).2.trans
      (triangleFlankBeltEdge
        hred ha hb hd hncol pick L hedge e j hadj htri).2.symm
  exact cyclicEdges_eq_or_end_start
    (Finset.univ : Finset (Vertex (P := P)))
    (OnLine (B (P := P))) (vertexCoord (B (P := P)))
    (vertexCoord_injective (B (P := P))) eb et hline v.1 hveb hvet

end Erdos735.ConcreteStage4BeltStep
