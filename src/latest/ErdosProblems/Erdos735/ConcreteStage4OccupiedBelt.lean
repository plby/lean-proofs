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

import ErdosProblems.Erdos735.ConcreteStage4ContinuationEndpoints
import ErdosProblems.Erdos735.ConcreteStage4BeltStep
import ErdosProblems.Erdos735.CyclicOrderClosure

/-!
# The occupied fixed-owner belt of a deficient Stage-4 component

This file gives first-class names to the cyclic intervals occupied by the
bad and helping quadrangles of the canonical Hall-deficient component.  It
is the ordered interface between the finite component and the literal
cyclic line geometry.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4OccupiedBelt

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement
open SignVector.ProjectiveEdgeEndpointEquiv

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev Line := ProjectiveBoundaryExtraction.Line (B (P := P))
private abbrev Vertex := ProjectiveBoundaryExtraction.Vertex (B (P := P))

variable (hAcard : 3 ≤ (ordinaryPoints P).card)
variable (hnotFF : ¬ IsFailedFano P)

private abbrev L := ConcreteStage4FlankComplete.flankSystem
  hred ha hb hd hncol hAcard hnotFF
private abbrev G := (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph

/-- A fixed owner-preserving projective-edge orientation. -/
noncomputable def pick : OtherLineChoice (Line (P := P)) :=
  otherLineChoiceOfPair ⟨a, ha⟩ ⟨b, hb⟩ (by
    intro hab
    apply hncol
    have : a = b := congrArg Subtype.val hab
    subst b
    simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet])

private abbrev component
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :=
  (G hred ha hb hd hncol hAcard hnotFF).deficientPathComponent hHall

/-- The alternating cells belonging to the deficient component: its bad
quadrangles (indexed by evil faces) and its helping quadrangles. -/
abbrev ComponentCell
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :=
  {e // e ∈ (component hred ha hb hd hncol hAcard hnotFF hHall).evils} ⊕
  {h // h ∈ (G hred ha hb hd hncol hAcard hnotFF).neighborsOf
    (component hred ha hb hd hncol hAcard hnotFF hHall).evils}

/-- Choose one component evil adjacent to a component helper. -/
noncomputable def helperEvil
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (h : {h // h ∈ (G hred ha hb hd hncol hAcard hnotFF).neighborsOf
      (component hred ha hb hd hncol hAcard hnotFF hHall).evils}) :
    (D hred ha hb hd hncol).EvilFace :=
  Classical.choose
    ((G hred ha hb hd hncol hAcard hnotFF).mem_neighborsOf.mp h.2)

theorem helperEvil_mem
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (h : {h // h ∈ (G hred ha hb hd hncol hAcard hnotFF).neighborsOf
      (component hred ha hb hd hncol hAcard hnotFF hHall).evils}) :
    helperEvil hred ha hb hd hncol hAcard hnotFF hHall h ∈
      (component hred ha hb hd hncol hAcard hnotFF hHall).evils :=
  (Classical.choose_spec
    ((G hred ha hb hd hncol hAcard hnotFF).mem_neighborsOf.mp h.2)).1

theorem helperEvil_adj
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (h : {h // h ∈ (G hred ha hb hd hncol hAcard hnotFF).neighborsOf
      (component hred ha hb hd hncol hAcard hnotFF hHall).evils}) :
    (L hred ha hb hd hncol hAcard hnotFF).Adj
      (helperEvil hred ha hb hd hncol hAcard hnotFF hHall h) h.1 :=
  (Classical.choose_spec
    ((G hred ha hb hd hncol hAcard hnotFF).mem_neighborsOf.mp h.2)).2

/-- The underlying projective cyclic interval occupied by one component
cell.  We deliberately forget the spherical sheet here: the component is
one lift of the projective belt, and antipodality supplies the other lift. -/
noncomputable def cellCyclicEdge
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    ComponentCell hred ha hb hd hncol hAcard hnotFF hHall →
      CyclicSkeletonEdge (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P)))
  | Sum.inl e =>
      (ConcreteStage4BeltStep.evilOppositeBeltEdge
        hred ha hb hd hncol (pick ha hb hncol)
        (L hred ha hb hd hncol hAcard hnotFF)
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF) e.1).1.1
  | Sum.inr h =>
      (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
        hred ha hb hd hncol (pick ha hb hncol)
        (L hred ha hb hd hncol hAcard hnotFF)
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF)
        (helperEvil_adj hred ha hb hd hncol hAcard hnotFF hHall h)).1.1

/-- The literal strict spherical edge underlying a component-cell
projective interval. -/
noncomputable def cellStrictEdge
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    ComponentCell hred ha hb hd hncol hAcard hnotFF hHall →
      StrictEdge (normals (B (P := P)))
  | Sum.inl e =>
      (D hred ha hb hd hncol).boundaryEdge
        ((D hred ha hb hd hncol).evilBadOppositeDart e.1).1
        ((D hred ha hb hd hncol).evilBadOppositeDart e.1).2
  | Sum.inr h =>
      (D hred ha hb hd hncol).boundaryEdge
        ((D hred ha hb hd hncol).helpingOppositeDart h.1).1
        ((D hred ha hb hd hncol).helpingOppositeDart h.1).2

@[simp] theorem cellStrictEdge_lifted_base
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x : ComponentCell hred ha hb hd hncol hAcard hnotFF hHall) :
    (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
      (pick ha hb hncol)
      (cellStrictEdge hred ha hb hd hncol hAcard hnotFF hHall x)).1 =
        cellCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x := by
  rcases x with e | h <;> rfl

/-- The selected common opposite owner line. -/
noncomputable def selectedLine
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    Line (P := P) :=
  ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol)
    (L hred ha hb hd hncol hAcard hnotFF)
    ((component hred ha hb hd hncol hAcard hnotFF hHall).endpoint 0)

/-- Every component cell interval lies on the selected common opposite
line. -/
theorem cellCyclicEdge_line
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x : ComponentCell hred ha hb hd hncol hAcard hnotFF hHall) :
    cyclicEdgeLine
      (cellCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x) =
      selectedLine hred ha hb hd hncol hAcard hnotFF hHall := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let GG := G hred ha hb hd hncol hAcard hnotFF
  let H := component hred ha hb hd hncol hAcard hnotFF hHall
  let K := ConcreteOppositeLineCoherence.oppositeLineCoherence
    hred ha hb hd hncol LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF)
  have common (e : (D hred ha hb hd hncol).EvilFace) (he : e ∈ H.evils) :
      ABKPR.Data.evilOppositeLine (D hred ha hb hd hncol) LL e =
        selectedLine hred ha hb hd hncol hAcard hnotFF hHall := by
    have hp := H.evils_reachable_from_first e he
    have hp' : Relation.ReflTransGen (ABKPR.Data.EvilLinked LL)
        (H.endpoint 0) e := by
      refine Relation.ReflTransGen.mono
        (r := GG.LinkedEvil) (p := ABKPR.Data.EvilLinked LL) ?_
          (H.endpoint 0) e hp
      intro x y hs
      exact (ABKPR.Data.linkedEvil_iff_evilLinked
        (D hred ha hb hd hncol) LL x y).mp hs
    exact (ABKPR.Data.OppositeLineCoherence.evilOppositeLine_eq_of_reflTransGen_evilLinked
        (D hred ha hb hd hncol) LL K hp').symm
  rcases x with e | h
  · change cyclicEdgeLine
        (ConcreteStage4BeltStep.evilOppositeBeltEdge
          hred ha hb hd hncol (pick ha hb hncol) LL _ e.1).1.1 = _
    exact (ConcreteStage4BeltStep.evilOppositeBeltEdge
      hred ha hb hd hncol (pick ha hb hncol) LL _ e.1).2.trans
        (common e.1 e.2)
  · change cyclicEdgeLine
        (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
          hred ha hb hd hncol (pick ha hb hncol) LL _
            (helperEvil_adj hred ha hb hd hncol hAcard hnotFF hHall h)).1.1 = _
    exact (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
      hred ha hb hd hncol (pick ha hb hncol) LL _
        (helperEvil_adj hred ha hb hd hncol hAcard hnotFF hHall h)).2.trans
      (common _ (helperEvil_mem
        hred ha hb hd hncol hAcard hnotFF hHall h))

/-- The underlying projective interval carried by endpoint continuation
triangle `k`. -/
noncomputable def endpointCyclicEdge
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    CyclicSkeletonEdge (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) :=
  let e := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
  (ConcreteStage4BeltStep.triangleFlankBeltEdge
    hred ha hb hd hncol (pick ha hb hncol)
    (L hred ha hb hd hncol hAcard hnotFF)
    (ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF)
    e
    (ConcreteStage4ContinuationEndpoints.endpointIndex
      hred ha hb hd hncol hAcard hnotFF hHall k)
    (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
      hred ha hb hd hncol hAcard hnotFF hHall k)
      (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
      hred ha hb hd hncol hAcard hnotFF hHall k)).1.1

/-- The literal strict edge on the selected opposite line in endpoint
continuation triangle `k`. -/
noncomputable def endpointStrictEdge
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) : StrictEdge (normals (B (P := P))) :=
  let e := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
  let j := ConcreteStage4ContinuationEndpoints.endpointIndex
    hred ha hb hd hncol hAcard hnotFF hHall k
  let flank := (D hred ha hb hd hncol).across
    ⟨((D hred ha hb hd hncol).across
      ((D hred ha hb hd hncol).evilDart e)).1, j⟩
  (D hred ha hb hd hncol).boundaryEdge flank.1
    (ConcreteStage4BeltStep.triangleFlankOppositeIndex
      hred ha hb hd hncol (L hred ha hb hd hncol hAcard hnotFF)
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF)
      e j
      (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
        hred ha hb hd hncol hAcard hnotFF hHall k)
      (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
        hred ha hb hd hncol hAcard hnotFF hHall k))

@[simp] theorem endpointStrictEdge_lifted_base
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
      (pick ha hb hncol)
      (endpointStrictEdge hred ha hb hd hncol hAcard hnotFF hHall k)).1 =
        endpointCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall k := by
  rfl

theorem endpointCyclicEdge_line
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    cyclicEdgeLine
      (endpointCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall k) =
      selectedLine hred ha hb hd hncol hAcard hnotFF hHall := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let K := ConcreteOppositeLineCoherence.oppositeLineCoherence
    hred ha hb hd hncol LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF)
  let e := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
  change cyclicEdgeLine
      (ConcreteStage4BeltStep.triangleFlankBeltEdge
        hred ha hb hd hncol (pick ha hb hncol) LL _ e
          (ConcreteStage4ContinuationEndpoints.endpointIndex
            hred ha hb hd hncol hAcard hnotFF hHall k) _ _).1.1 = _
  exact (ConcreteStage4BeltStep.triangleFlankBeltEdge
    hred ha hb hd hncol (pick ha hb hncol) LL _ e
      (ConcreteStage4ContinuationEndpoints.endpointIndex
        hred ha hb hd hncol hAcard hnotFF hHall k)
      (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
        hred ha hb hd hncol hAcard hnotFF hHall k)
      (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
        hred ha hb hd hncol hAcard hnotFF hHall k)).2.trans
    (ABKPR.Data.OppositeLineCoherence.deficientPath_endpoints_oppositeLine_eq
      (D hred ha hb hd hncol) LL K hHall k).symm

/-- Component quadrangles together with the two endpoint-triangle
intervals. -/
abbrev BeltItem
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :=
  ComponentCell hred ha hb hd hncol hAcard hnotFF hHall ⊕ Fin 2

/-- The bad-quadrangle cell at endpoint `k`, regarded as an augmented belt
item. -/
def endpointEvilItem
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) : BeltItem hred ha hb hd hncol hAcard hnotFF hHall :=
  Sum.inl (Sum.inl
    ⟨(component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k,
      (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint_mem k⟩)

noncomputable def beltCyclicEdge
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    BeltItem hred ha hb hd hncol hAcard hnotFF hHall →
      CyclicSkeletonEdge (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P)))
  | Sum.inl x =>
      cellCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x
  | Sum.inr k =>
      endpointCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall k

noncomputable def beltStrictEdge
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    BeltItem hred ha hb hd hncol hAcard hnotFF hHall →
      StrictEdge (normals (B (P := P)))
  | Sum.inl x => cellStrictEdge hred ha hb hd hncol hAcard hnotFF hHall x
  | Sum.inr k => endpointStrictEdge hred ha hb hd hncol hAcard hnotFF hHall k

@[simp] theorem beltStrictEdge_lifted_base
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x : BeltItem hred ha hb hd hncol hAcard hnotFF hHall) :
    (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
      (pick ha hb hncol)
      (beltStrictEdge hred ha hb hd hncol hAcard hnotFF hHall x)).1 =
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x := by
  rcases x with x | k
  · exact cellStrictEdge_lifted_base
      hred ha hb hd hncol hAcard hnotFF hHall x
  · exact endpointStrictEdge_lifted_base
      hred ha hb hd hncol hAcard hnotFF hHall k

theorem beltCyclicEdge_line
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x : BeltItem hred ha hb hd hncol hAcard hnotFF hHall) :
    cyclicEdgeLine
      (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x) =
      selectedLine hred ha hb hd hncol hAcard hnotFF hHall := by
  rcases x with x | k
  · exact cellCyclicEdge_line
      hred ha hb hd hncol hAcard hnotFF hHall x
  · exact endpointCyclicEdge_line
      hred ha hb hd hncol hAcard hnotFF hHall k

/-- Projective start vertices of intervals occupied by component cells. -/
noncomputable def occupiedStarts
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    Finset {v // v ∈ verticesOn
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P)))
      (selectedLine hred ha hb hd hncol hAcard hnotFF hHall)} :=
  Finset.univ.image fun x :
        BeltItem hred ha hb hd hncol hAcard hnotFF hHall ↦
      ⟨cyclicEdgeStart
        (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x), by
        have hs := cyclicEdgeStart_incident
          (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P)))
          (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x)
        rw [beltCyclicEdge_line
          hred ha hb hd hncol hAcard hnotFF hHall x] at hs
        exact (mem_verticesOn _ _).2 ⟨Finset.mem_univ _, hs⟩⟩

theorem occupiedStarts_nonempty
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    (occupiedStarts hred ha hb hd hncol hAcard hnotFF hHall).Nonempty := by
  let e := (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint 0
  let x : BeltItem hred ha hb hd hncol hAcard hnotFF hHall :=
    Sum.inl (Sum.inl
      ⟨e, (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint_mem 0⟩)
  exact ⟨_, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

/-- A local successor interval for every occupied item implies successor
closure of the occupied start vertices. -/
theorem occupiedStarts_successor_closed_of_finish_covered
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hcover : ∀ x : BeltItem hred ha hb hd hncol hAcard hnotFF hHall,
      ∃ y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall,
        cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
            (OnLine (B (P := P))) (vertexCoord (B (P := P)))
            (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x) =
          cyclicEdgeStart
            (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y)) :
    ∀ x ∈ occupiedStarts hred ha hb hd hncol hAcard hnotFF hHall,
      cyclicSuccessor (vertexCoord (B (P := P)))
        (verticesOn (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P)))
          (selectedLine hred ha hb hd hncol hAcard hnotFF hHall)) x ∈
        occupiedStarts hred ha hb hd hncol hAcard hnotFF hHall := by
  intro x hx
  obtain ⟨item, -, hitem⟩ := Finset.mem_image.mp hx
  subst x
  obtain ⟨next, hnext⟩ := hcover item
  apply Finset.mem_image.mpr
  refine ⟨next, Finset.mem_univ _, Subtype.ext ?_⟩
  change cyclicEdgeStart
      (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall next) =
    (cyclicSuccessor (vertexCoord (B (P := P)))
      (verticesOn (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P)))
        (selectedLine hred ha hb hd hncol hAcard hnotFF hHall)) _).1
  rw [← hnext]
  let e := beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall item
  have heline : cyclicEdgeLine e =
      selectedLine hred ha hb hd hncol hAcard hnotFF hHall :=
    beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall item
  change cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P))) e = _
  change cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P))) e =
    (cyclicSuccessor (vertexCoord (B (P := P)))
      (verticesOn (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P)))
        (selectedLine hred ha hb hd hncol hAcard hnotFF hHall))
      ⟨cyclicEdgeStart e, by
        have hs := cyclicEdgeStart_incident
          (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) e
        rw [heline] at hs
        exact (mem_verticesOn _ _).2 ⟨Finset.mem_univ _, hs⟩⟩).1
  rcases e with ⟨line, start⟩
  change line = selectedLine hred ha hb hd hncol hAcard hnotFF hHall at heline
  subst line
  rfl

/-- Once the local two-endpoint analysis proves successor closure, the
occupied component and endpoint intervals exhaust the entire projective
cyclic line.  This is the global finite step; all remaining work is local
at bad, helping, and endpoint cells. -/
theorem occupiedStarts_eq_univ_of_successor_closed
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hclosed : ∀ x ∈
      occupiedStarts hred ha hb hd hncol hAcard hnotFF hHall,
      cyclicSuccessor (vertexCoord (B (P := P)))
        (verticesOn (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P)))
          (selectedLine hred ha hb hd hncol hAcard hnotFF hHall)) x ∈
        occupiedStarts hred ha hb hd hncol hAcard hnotFF hHall) :
    occupiedStarts hred ha hb hd hncol hAcard hnotFF hHall = Finset.univ := by
  exact ChartOrder.eq_univ_of_nonempty_of_cyclicSuccessor_closed
    (vertexCoord (B (P := P)))
    (verticesOn (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P)))
      (selectedLine hred ha hb hd hncol hAcard hnotFF hHall))
    ((vertexCoord_injective (B (P := P))).mono
      (Finset.filter_subset _ _))
    (occupiedStarts hred ha hb hd hncol hAcard hnotFF hHall)
    (occupiedStarts_nonempty
      hred ha hb hd hncol hAcard hnotFF hHall) hclosed

/-- Adjacency in the augmented belt: evil and helping cells alternate;
each endpoint evil is joined to its continuation triangle; and the two
continuation triangles close the cyclic belt. -/
def BeltAdjacent
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    BeltItem hred ha hb hd hncol hAcard hnotFF hHall →
      BeltItem hred ha hb hd hncol hAcard hnotFF hHall → Prop
  | Sum.inl (Sum.inl e), Sum.inl (Sum.inr h) =>
      (L hred ha hb hd hncol hAcard hnotFF).Adj e.1 h.1
  | Sum.inl (Sum.inr h), Sum.inl (Sum.inl e) =>
      (L hred ha hb hd hncol hAcard hnotFF).Adj e.1 h.1
  | Sum.inl (Sum.inl e), Sum.inr k =>
      e.1 = (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
  | Sum.inr k, Sum.inl (Sum.inl e) =>
      e.1 = (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k
  | Sum.inr k, Sum.inr l => k ≠ l
  | _, _ => False

@[simp] theorem endpointTriangle_adj_endpointEvil
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall
      (Sum.inr k) (endpointEvilItem
        hred ha hb hd hncol hAcard hnotFF hHall k) := rfl

/-- A component cell cannot be adjacent to both distinct endpoint-triangle
items. -/
theorem endpoint_indices_eq_of_component_adjacent
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x : ComponentCell hred ha hb hd hncol hAcard hnotFF hHall)
    {k l : Fin 2}
    (hk : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall
      (Sum.inl x) (Sum.inr k))
    (hl : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall
      (Sum.inl x) (Sum.inr l)) : k = l := by
  rcases x with e | h
  · apply (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint_injective
    exact hk.symm.trans hl
  · exact False.elim hk

theorem beltAdjacent_symmetric
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    Symmetric (BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall) := by
  intro x y hxy
  rcases x with (e | h) | k <;> rcases y with (e' | h') | l <;>
    simp only [BeltAdjacent] at hxy ⊢
  · exact hxy
  · exact hxy
  · exact hxy
  · exact hxy
  · exact hxy.symm

/-- Orientation-free endpoint sharing for the projective cyclic intervals
carried by two augmented belt items. -/
def BeltEdgeNeighbor
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall) : Prop :=
  let ex := beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x
  let ey := beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y
  ex = ey ∨
    cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P))) ex =
      cyclicEdgeStart ey ∨
    cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
        (OnLine (B (P := P))) (vertexCoord (B (P := P))) ey =
      cyclicEdgeStart ex

theorem beltEdgeNeighbor_symmetric
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    {x y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall}
    (hxy : BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall x y) :
    BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall y x := by
  rcases hxy with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem beltEdgeNeighbor_congr_left
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    {x x' y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall}
    (heq : beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x =
      beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x')
    (h : BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall x' y) :
    BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall x y := by
  unfold BeltEdgeNeighbor at h ⊢
  simpa only [heq] using h

/-- Every augmented graph edge except the final endpoint--endpoint closing
edge is already a genuine cyclic-interval adjacency, by the checked local
evil--helper and evil--triangle belt bridges. -/
theorem beltAdjacent_edgeNeighbor_of_not_endpoint_pair
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    {x y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall}
    (hxy : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x y)
    (hnot : ¬ ∃ k l : Fin 2, x = Sum.inr k ∧ y = Sum.inr l) :
    BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall x y := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  rcases x with (e | h) | k
  · rcases y with (e' | h') | l
    · exact False.elim hxy
    · change let ee := (ConcreteStage4BeltStep.evilOppositeBeltEdge
          hred ha hb hd hncol (pick ha hb hncol) LL _ e.1).1.1
        let eh := (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
          hred ha hb hd hncol (pick ha hb hncol) LL _
            (helperEvil_adj hred ha hb hd hncol hAcard hnotFF hHall h')).1.1
        ee = eh ∨
          cyclicEdgeFinish _ _ (vertexCoord (B (P := P))) ee = cyclicEdgeStart eh ∨
          cyclicEdgeFinish _ _ (vertexCoord (B (P := P))) eh = cyclicEdgeStart ee
      exact ConcreteStage4BeltStep.oppositeBeltEdges_eq_or_end_start_of_adj
        hred ha hb hd hncol (pick ha hb hncol) LL
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF) hxy
    · have he : e =
          ⟨(component hred ha hb hd hncol hAcard hnotFF hHall).endpoint l,
            (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint_mem l⟩ :=
        Subtype.ext hxy
      subst e
      exact ConcreteStage4BeltStep.triangleFlankBeltEdge_eq_or_end_start
        hred ha hb hd hncol (pick ha hb hncol) LL
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF)
        ((component hred ha hb hd hncol hAcard hnotFF hHall).endpoint l)
        (ConcreteStage4ContinuationEndpoints.endpointIndex
          hred ha hb hd hncol hAcard hnotFF hHall l)
        (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
          hred ha hb hd hncol hAcard hnotFF hHall l)
        (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
          hred ha hb hd hncol hAcard hnotFF hHall l)
  · rcases y with (e' | h') | l
    · apply beltEdgeNeighbor_symmetric
        hred ha hb hd hncol hAcard hnotFF hHall
      change let ee := (ConcreteStage4BeltStep.evilOppositeBeltEdge
          hred ha hb hd hncol (pick ha hb hncol) LL _ e'.1).1.1
        let eh := (ConcreteStage4BeltStep.helperOppositeBeltEdgeOfAdj
          hred ha hb hd hncol (pick ha hb hncol) LL _
            (helperEvil_adj hred ha hb hd hncol hAcard hnotFF hHall h)).1.1
        ee = eh ∨
          cyclicEdgeFinish _ _ (vertexCoord (B (P := P))) ee = cyclicEdgeStart eh ∨
          cyclicEdgeFinish _ _ (vertexCoord (B (P := P))) eh = cyclicEdgeStart ee
      exact ConcreteStage4BeltStep.oppositeBeltEdges_eq_or_end_start_of_adj
        hred ha hb hd hncol (pick ha hb hncol) LL
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF) hxy
    · exact False.elim hxy
    · exact False.elim hxy
  · rcases y with (e' | h') | l
    · apply beltEdgeNeighbor_symmetric
        hred ha hb hd hncol hAcard hnotFF hHall
      have he : e' =
          ⟨(component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k,
            (component hred ha hb hd hncol hAcard hnotFF hHall).endpoint_mem k⟩ :=
        Subtype.ext hxy
      subst e'
      exact ConcreteStage4BeltStep.triangleFlankBeltEdge_eq_or_end_start
        hred ha hb hd hncol (pick ha hb hncol) LL
        (ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF)
        ((component hred ha hb hd hncol hAcard hnotFF hHall).endpoint k)
        (ConcreteStage4ContinuationEndpoints.endpointIndex
          hred ha hb hd hncol hAcard hnotFF hHall k)
        (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
          hred ha hb hd hncol hAcard hnotFF hHall k)
        (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
          hred ha hb hd hncol hAcard hnotFF hHall k)
    · exact False.elim hxy
    · exfalso
      apply hnot
      exact ⟨k, l, rfl, rfl⟩

/-- Every vertex of the augmented deficient belt has two distinct graph
neighbors.  This is the purely finite-combinatorial part of the cyclic
exhaustion; geometry is only needed to show that the corresponding cyclic
intervals are the two distinct endpoint-sharing intervals. -/
theorem exists_two_distinct_beltNeighbors
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (x : BeltItem hred ha hb hd hncol hAcard hnotFF hHall) :
    ∃ y z : BeltItem hred ha hb hd hncol hAcard hnotFF hHall,
      y ≠ z ∧
      BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x y ∧
      BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x z := by
  let GG := G hred ha hb hd hncol hAcard hnotFF
  let H := component hred ha hb hd hncol hAcard hnotFF hHall
  rcases x with (e | h) | k
  · have hlo := GG.evil_degree_one_le e.1
    have hhi := GG.evil_degree_le_two e.1
    by_cases hone : (GG.evilNeighbors e.1).card = 1
    · obtain ⟨k, hk⟩ := H.every_degree_one_is_endpoint e.1 e.2 hone
      obtain ⟨helper, hhelper⟩ := Finset.card_pos.mp (by omega :
        0 < (GG.evilNeighbors e.1).card)
      have hadj : GG.Adj e.1 helper := (Finset.mem_filter.mp hhelper).2
      let hs : {h // h ∈ GG.neighborsOf H.evils} :=
        ⟨helper, GG.mem_neighborsOf.mpr ⟨e.1, e.2, hadj⟩⟩
      refine ⟨Sum.inl (Sum.inr hs), Sum.inr k, ?_, ?_, ?_⟩
      · simp
      · exact hadj
      · exact hk.symm
    · have htwo : (GG.evilNeighbors e.1).card = 2 := by omega
      obtain ⟨h₀, h₁, hhne, hpair⟩ := Finset.card_eq_two.mp htwo
      have hh₀ : h₀ ∈ GG.evilNeighbors e.1 := by simp [hpair]
      have hh₁ : h₁ ∈ GG.evilNeighbors e.1 := by simp [hpair]
      have hadj₀ : GG.Adj e.1 h₀ := (Finset.mem_filter.mp hh₀).2
      have hadj₁ : GG.Adj e.1 h₁ := (Finset.mem_filter.mp hh₁).2
      let hs₀ : {h // h ∈ GG.neighborsOf H.evils} :=
        ⟨h₀, GG.mem_neighborsOf.mpr ⟨e.1, e.2, hadj₀⟩⟩
      let hs₁ : {h // h ∈ GG.neighborsOf H.evils} :=
        ⟨h₁, GG.mem_neighborsOf.mpr ⟨e.1, e.2, hadj₁⟩⟩
      refine ⟨Sum.inl (Sum.inr hs₀), Sum.inl (Sum.inr hs₁), ?_, ?_, ?_⟩
      · intro heq
        have hsub : hs₀ = hs₁ := Sum.inr.inj (Sum.inl.inj heq)
        exact hhne (congrArg Subtype.val hsub)
      · exact hadj₀
      · exact hadj₁
  · have htwo := H.helper_two_neighbors h.1 h.2
    obtain ⟨e₀, e₁, hene, hpair⟩ := Finset.card_eq_two.mp htwo
    have hmem₀ : e₀ ∈ GG.evilNeighborsIn H.evils h.1 := by
      rw [hpair]
      simp
    have hmem₁ : e₁ ∈ GG.evilNeighborsIn H.evils h.1 := by
      rw [hpair]
      simp
    have he₀ := GG.mem_evilNeighborsIn.mp hmem₀
    have he₁ := GG.mem_evilNeighborsIn.mp hmem₁
    let es₀ : {e // e ∈ H.evils} := ⟨e₀, he₀.1⟩
    let es₁ : {e // e ∈ H.evils} := ⟨e₁, he₁.1⟩
    refine ⟨Sum.inl (Sum.inl es₀), Sum.inl (Sum.inl es₁), ?_, ?_, ?_⟩
    · intro heq
      have hsub : es₀ = es₁ := Sum.inl.inj (Sum.inl.inj heq)
      exact hene (congrArg Subtype.val hsub)
    · exact he₀.2
    · exact he₁.2
  · let e : {e // e ∈ H.evils} := ⟨H.endpoint k, H.endpoint_mem k⟩
    let l : Fin 2 := ⟨1 - k.1, by omega⟩
    have hkl : k ≠ l := by
      intro h
      have hv := congrArg Fin.val h
      simp only [l] at hv
      omega
    refine ⟨Sum.inl (Sum.inl e), Sum.inr l, ?_, ?_, ?_⟩
    · simp
    · rfl
    · exact hkl

/-- Once the two endpoint-triangle intervals are known to close up, every
edge of the augmented belt graph is a literal cyclic-interval neighbor. -/
theorem beltAdjacent_edgeNeighbor_of_endpointClosure
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hend : BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall
      (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2)))
    {x y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall}
    (hxy : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x y) :
    BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall x y := by
  by_cases hep : ∃ k l : Fin 2, x = Sum.inr k ∧ y = Sum.inr l
  · obtain ⟨k, l, rfl, rfl⟩ := hep
    change k ≠ l at hxy
    fin_cases k <;> fin_cases l
    · exact (hxy rfl).elim
    · exact hend
    · exact beltEdgeNeighbor_symmetric
        hred ha hb hd hncol hAcard hnotFF hHall hend
    · exact (hxy rfl).elim
  · exact beltAdjacent_edgeNeighbor_of_not_endpoint_pair
      hred ha hb hd hncol hAcard hnotFF hHall hxy hep

/-- A degree-two augmented belt whose adjacent cyclic intervals do not
collide is successor-complete.  The conclusion is exactly the local
`hcover` input of `occupiedStarts_successor_closed_of_finish_covered`. -/
theorem finish_covered_of_endpointClosure_of_local_noncollision
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hend : BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall
      (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2)))
    (hself : ∀ {x y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall},
      BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x y →
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x ≠
          beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y)
    (hpair : ∀ {x y z : BeltItem hred ha hb hd hncol hAcard hnotFF hHall},
      BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x y →
      BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x z → y ≠ z →
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y ≠
          beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall z) :
    ∀ x : BeltItem hred ha hb hd hncol hAcard hnotFF hHall,
      ∃ y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall,
        cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
            (OnLine (B (P := P))) (vertexCoord (B (P := P)))
            (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x) =
          cyclicEdgeStart
            (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y) := by
  intro x
  obtain ⟨y, z, hyz, hxy, hxz⟩ := exists_two_distinct_beltNeighbors
    hred ha hb hd hncol hAcard hnotFF hHall x
  have hny := beltAdjacent_edgeNeighbor_of_endpointClosure
    hred ha hb hd hncol hAcard hnotFF hHall hend hxy
  have hnz := beltAdjacent_edgeNeighbor_of_endpointClosure
    hred ha hb hd hncol hAcard hnotFF hHall hend hxz
  have hforward := ChartOrder.finish_eq_start_of_two_distinct_neighbors
    (Finset.univ : Finset (Vertex (P := P)))
    (OnLine (B (P := P))) (vertexCoord (B (P := P)))
    (vertexCoord_injective (B (P := P)))
    (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x)
    (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y)
    (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall z)
    ((beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall y).trans
      (beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall x).symm)
    ((beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall z).trans
      (beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall x).symm)
    (hself hxy) (hself hxz) (hpair hxy hxz hyz) hny hnz
  rcases hforward with hy | hz
  · exact ⟨y, hy⟩
  · exact ⟨z, hz⟩

/-- Collision-safe successor coverage.  A pair of distinct graph neighbors
may project to the same cyclic interval (for example through antipodal
lifts).  The `hcollision` callback records the topology-correct conclusion
in that case: the center and the collapsed neighbor form the directed
two-interval cycle.  The final callback handles the one endpoint pattern
not represented by two graph edges from the same center. -/
theorem finish_covered_allow_endpoint_edge_eq
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (hend : BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall
      (Sum.inr (0 : Fin 2)) (Sum.inr (1 : Fin 2)))
    (hself : ∀ {x y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall},
      BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x y →
      (¬ ∃ k l : Fin 2, x = Sum.inr k ∧ y = Sum.inr l) →
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x ≠
          beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y)
    (hcollision : ∀ {x y z : BeltItem hred ha hb hd hncol hAcard hnotFF hHall},
      BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x y →
      BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall x z → y ≠ z →
      (¬ ∃ k l : Fin 2, y = Sum.inr k ∧ z = Sum.inr l) →
      beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y =
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall z →
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P)))
          (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x) =
        cyclicEdgeStart
          (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y))
    (hendpointDouble :
      beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall
          (Sum.inr (0 : Fin 2)) =
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall
          (Sum.inr (1 : Fin 2)) →
      beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall
          (endpointEvilItem hred ha hb hd hncol hAcard hnotFF hHall 0) =
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall
          (endpointEvilItem hred ha hb hd hncol hAcard hnotFF hHall 1) →
      cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
          (OnLine (B (P := P))) (vertexCoord (B (P := P)))
          (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall
            (Sum.inr (0 : Fin 2))) =
        cyclicEdgeStart
          (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall
            (endpointEvilItem hred ha hb hd hncol hAcard hnotFF hHall 0))) :
    ∀ x : BeltItem hred ha hb hd hncol hAcard hnotFF hHall,
      ∃ y : BeltItem hred ha hb hd hncol hAcard hnotFF hHall,
        cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
            (OnLine (B (P := P))) (vertexCoord (B (P := P)))
            (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x) =
          cyclicEdgeStart
            (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y) := by
  have forward (x y z : BeltItem hred ha hb hd hncol hAcard hnotFF hHall)
      (hxy : beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x ≠
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y)
      (hxz : beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x ≠
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall z)
      (hyz : beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y ≠
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall z)
      (hny : BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall x y)
      (hnz : BeltEdgeNeighbor hred ha hb hd hncol hAcard hnotFF hHall x z) :
      ∃ q : BeltItem hred ha hb hd hncol hAcard hnotFF hHall,
        cyclicEdgeFinish (Finset.univ : Finset (Vertex (P := P)))
            (OnLine (B (P := P))) (vertexCoord (B (P := P)))
            (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x) =
          cyclicEdgeStart
            (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall q) := by
    have hf := ChartOrder.finish_eq_start_of_two_distinct_neighbors
      (Finset.univ : Finset (Vertex (P := P)))
      (OnLine (B (P := P))) (vertexCoord (B (P := P)))
      (vertexCoord_injective (B (P := P)))
      (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall x)
      (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y)
      (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall z)
      ((beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall y).trans
        (beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall x).symm)
      ((beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall z).trans
        (beltCyclicEdge_line hred ha hb hd hncol hAcard hnotFF hHall x).symm)
      hxy hxz hyz hny hnz
    rcases hf with h | h
    · exact ⟨y, h⟩
    · exact ⟨z, h⟩
  intro x
  rcases x with x | k
  · obtain ⟨y, z, hyz, hxy, hxz⟩ := exists_two_distinct_beltNeighbors
      hred ha hb hd hncol hAcard hnotFF hHall (Sum.inl x)
    have hnotPair : ¬ ∃ ky kz : Fin 2, y = Sum.inr ky ∧ z = Sum.inr kz := by
      rintro ⟨ky, kz, rfl, rfl⟩
      exact hyz (congrArg Sum.inr
        (endpoint_indices_eq_of_component_adjacent
          hred ha hb hd hncol hAcard hnotFF hHall x hxy hxz))
    by_cases hyzEdge :
        beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall y =
          beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall z
    · exact ⟨y, hcollision hxy hxz hyz hnotPair hyzEdge⟩
    · apply forward (Sum.inl x) y z
      · exact hself hxy (by simp)
      · exact hself hxz (by simp)
      · exact hyzEdge
      · exact beltAdjacent_edgeNeighbor_of_endpointClosure
          hred ha hb hd hncol hAcard hnotFF hHall hend hxy
      · exact beltAdjacent_edgeNeighbor_of_endpointClosure
          hred ha hb hd hncol hAcard hnotFF hHall hend hxz
  · fin_cases k
    · let t0 : BeltItem hred ha hb hd hncol hAcard hnotFF hHall := Sum.inr 0
      let t1 : BeltItem hred ha hb hd hncol hAcard hnotFF hHall := Sum.inr 1
      let e0 := endpointEvilItem hred ha hb hd hncol hAcard hnotFF hHall 0
      let e1 := endpointEvilItem hred ha hb hd hncol hAcard hnotFF hHall 1
      have ht0e0 : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall t0 e0 := rfl
      have ht1e1 : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall t1 e1 := rfl
      have hn0 := beltAdjacent_edgeNeighbor_of_not_endpoint_pair
        hred ha hb hd hncol hAcard hnotFF hHall ht0e0
          (by simp [t0, e0, endpointEvilItem])
      have hn1 := beltAdjacent_edgeNeighbor_of_not_endpoint_pair
        hred ha hb hd hncol hAcard hnotFF hHall ht1e1
          (by simp [t1, e1, endpointEvilItem])
      by_cases heq : beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall t0 =
          beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall t1
      · by_cases hevil : beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall e0 =
            beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall e1
        · exact ⟨e0, hendpointDouble heq hevil⟩
        · apply forward t0 e0 e1
          · exact hself ht0e0 (by simp [t0, e0, endpointEvilItem])
          · intro h
            exact hself ht1e1 (by simp [t1, e1, endpointEvilItem])
              (heq.symm.trans h)
          · exact hevil
          · exact hn0
          · exact beltEdgeNeighbor_congr_left
              hred ha hb hd hncol hAcard hnotFF hHall heq hn1
      · have ht0t1 : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall t0 t1 := by
          simp [t0, t1, BeltAdjacent]
        by_cases hcollisionEdge :
            beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall e0 =
              beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall t1
        · exact ⟨e0, hcollision ht0e0 ht0t1
            (by simp [e0, t1, endpointEvilItem])
            (by simp [e0, t1, endpointEvilItem]) hcollisionEdge⟩
        · apply forward t0 e0 t1
          · exact hself ht0e0 (by simp [t0, e0, endpointEvilItem])
          · exact heq
          · exact hcollisionEdge
          · exact hn0
          · exact hend
    · let t0 : BeltItem hred ha hb hd hncol hAcard hnotFF hHall := Sum.inr 0
      let t1 : BeltItem hred ha hb hd hncol hAcard hnotFF hHall := Sum.inr 1
      let e0 := endpointEvilItem hred ha hb hd hncol hAcard hnotFF hHall 0
      let e1 := endpointEvilItem hred ha hb hd hncol hAcard hnotFF hHall 1
      have ht0e0 : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall t0 e0 := rfl
      have ht1e1 : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall t1 e1 := rfl
      have hn0 := beltAdjacent_edgeNeighbor_of_not_endpoint_pair
        hred ha hb hd hncol hAcard hnotFF hHall ht0e0
          (by simp [t0, e0, endpointEvilItem])
      have hn1 := beltAdjacent_edgeNeighbor_of_not_endpoint_pair
        hred ha hb hd hncol hAcard hnotFF hHall ht1e1
          (by simp [t1, e1, endpointEvilItem])
      by_cases heq : beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall t0 =
          beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall t1
      · by_cases hevil : beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall e0 =
            beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall e1
        · refine ⟨e0, ?_⟩
          change cyclicEdgeFinish _ _ _
              (beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall t1) = _
          rw [← heq]
          exact hendpointDouble heq hevil
        · apply forward t1 e0 e1
          · intro h
            exact hself ht0e0 (by simp [t0, e0, endpointEvilItem])
              (heq.trans h)
          · exact hself ht1e1 (by simp [t1, e1, endpointEvilItem])
          · exact hevil
          · exact beltEdgeNeighbor_congr_left
              hred ha hb hd hncol hAcard hnotFF hHall heq.symm hn0
          · exact hn1
      · have ht1t0 : BeltAdjacent hred ha hb hd hncol hAcard hnotFF hHall t1 t0 := by
          simp [t0, t1, BeltAdjacent]
        by_cases hcollisionEdge :
            beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall e1 =
              beltCyclicEdge hred ha hb hd hncol hAcard hnotFF hHall t0
        · exact ⟨e1, hcollision ht1e1 ht1t0
            (by simp [e1, t0, endpointEvilItem])
            (by simp [e1, t0, endpointEvilItem]) hcollisionEdge⟩
        · apply forward t1 e1 t0
          · exact hself ht1e1 (by simp [t1, e1, endpointEvilItem])
          · exact fun h ↦ heq h.symm
          · exact hcollisionEdge
          · exact hn1
          · exact beltEdgeNeighbor_symmetric
              hred ha hb hd hncol hAcard hnotFF hHall hend

end Erdos735.ConcreteStage4OccupiedBelt
