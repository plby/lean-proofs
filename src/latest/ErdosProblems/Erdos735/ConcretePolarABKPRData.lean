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

import ErdosProblems.Erdos735.ConcretePolarCellulation
import ErdosProblems.Erdos735.PolarRedChordExtraction
import ErdosProblems.Erdos735.DataCombinatorial
import ErdosProblems.Erdos735.ConcreteBadReceiver
import ErdosProblems.Erdos735.PolarGoodQuadrangleWeight

/-!
# Concrete polar ABKPR data

This file reindexes the literal polar boundary cycles by the face degrees of
the concrete blue cellulation and assembles all global and elementary
red-chord fields of `ABKPR.Data`.  Only the two genuinely local weighted
sector statements are parameters of the final constructor.
-/

open Classical
noncomputable section

namespace Erdos735.ConcretePolarABKPRData

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarBoundaryAcross SignVector.PolarBoundaryOrder
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices
open PolarRedChordExtraction

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

abbrev hspan : Submodule.span ℝ
    (Set.range (normals (nonordinaryPoints P))) = ⊤ :=
  span_normalVec_range_eq_top_of_noncollinear_triple
    (nonordinaryPoints P) ha hb hd hncol

variable (vertex_degree :
  ∀ v : OrientedVertex (nonordinaryPoints P),
    (concreteVertexEdges (hspan ha hb hd hncol) v).card =
      2 * lineMultiplicity (OnLine (nonordinaryPoints P)) v.1)

/-- The literal polar blue cellulation. -/
noncomputable def C :
    BlueCellulation (OrientedVertex (nonordinaryPoints P))
      (StrictEdge (normals (nonordinaryPoints P)))
      (StrictFace (normals (nonordinaryPoints P))) :=
  ConcretePolarCellulation.blueCellulationOfVertexDegree
    (nonordinaryPoints P) ha hb hd hncol vertex_degree

theorem faceDegree_eq_boundaryCount
    (f : StrictFace (normals (nonordinaryPoints P))) :
    (C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f =
      Erdos957.hullVertexCount
        (PolarPlaneChart.boundaryPolygon (normals (nonordinaryPoints P)) f.1
          (faceWitness (normals (nonordinaryPoints P)) f)) := by
  simp only [C, ConcretePolarCellulation.blueCellulationOfVertexDegree,
    ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
    BoundaryExtraction.toBlueCellulation, BlueCellulation.faceDegree,
    PolarBoundaryAcross.faceBoundary]
  exact PolarBoundaryOrder.faceBoundary_length f
    (faceWitness_realizes (normals (nonordinaryPoints P)) f)
    normal_cross (hspan ha hb hd hncol)

/-- The face-degree index and the concrete polar boundary index are the same
finite cyclic type, transported through the proved length equality. -/
noncomputable def indexEquiv
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) ≃
      BoundaryIndex (normals (nonordinaryPoints P)) f where
  toFun i := ⟨i.val, by
    rw [← faceDegree_eq_boundaryCount (vertex_degree := vertex_degree)
      ha hb hd hncol f]
    exact i.isLt⟩
  invFun i := ⟨i.val, by
    rw [faceDegree_eq_boundaryCount (vertex_degree := vertex_degree)
      ha hb hd hncol f]
    exact i.isLt⟩
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl

@[simp] theorem indexEquiv_val
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i).val = i.val := by
  rfl

theorem indexEquiv_succ
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f
        (ABKPR.faceSucc (C (vertex_degree := vertex_degree) ha hb hd hncol) f i) =
      Erdos957.cyclicSucc
        (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i) := by
  apply Fin.ext
  change (i.val + 1) %
      (C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f =
    (finRotate _ (indexEquiv (vertex_degree := vertex_degree)
      ha hb hd hncol f i)).val
  rw [finRotate_apply, Fin.val_add, Fin.val_one', indexEquiv_val]
  let m := Erdos957.hullVertexCount
    (PolarPlaneChart.boundaryPolygon (normals (nonordinaryPoints P)) f.1
      (faceWitness (normals (nonordinaryPoints P)) f))
  have hdeg : (C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f = m :=
    faceDegree_eq_boundaryCount (vertex_degree := vertex_degree) ha hb hd hncol f
  have hm : 3 ≤ m := by
    rw [← hdeg]
    exact (C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree_three_le f
  calc
    (i.val + 1) % (C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f =
        (i.val + 1) % m := congrArg (fun k ↦ (i.val + 1) % k) hdeg
    _ = (i.val + 1 % m) % m := by
      rw [Nat.mod_eq_of_lt (by omega : 1 < m)]

noncomputable def boundaryVertex
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    OrientedVertex (nonordinaryPoints P) :=
  boundaryOrientedVertex (hspan ha hb hd hncol) f
    (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i)

noncomputable def boundaryEdge
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    StrictEdge (normals (nonordinaryPoints P)) :=
  PolarBoundaryAcross.boundaryEdge (normals (nonordinaryPoints P)) normal_cross
    (hspan ha hb hd hncol) f
    (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i)

theorem boundaryVertex_injective
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Function.Injective
      (boundaryVertex (vertex_degree := vertex_degree) ha hb hd hncol f) := by
  intro i j hij
  apply (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).injective
  have hp := congrArg (fun v : OrientedVertex (nonordinaryPoints P) ↦ v.1.1) hij
  change PolarBoundaryOrder.boundaryProjectiveVertex f
      (faceWitness_realizes (normals (nonordinaryPoints P)) f) normal_cross
      (hspan ha hb hd hncol)
        ((finRotate _).symm
          (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i)) =
    PolarBoundaryOrder.boundaryProjectiveVertex f
      (faceWitness_realizes (normals (nonordinaryPoints P)) f) normal_cross
      (hspan ha hb hd hncol)
        ((finRotate _).symm
          (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f j)) at hp
  exact (finRotate _).symm.injective
    (PolarBoundaryOrder.boundaryProjectiveVertex_injective f
      (faceWitness_realizes (normals (nonordinaryPoints P)) f) normal_cross
      (hspan ha hb hd hncol) hp)

theorem boundaryEdge_injective
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Function.Injective
      (boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol f) := by
  intro i j hij
  apply (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).injective
  apply (PolarBoundaryAcross.boundaryEdgeEquiv
    (normals (nonordinaryPoints P)) normal_cross (hspan ha hb hd hncol) f).injective
  exact Subtype.ext hij

theorem boundaryEdge_mem
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol f i ∈
      (C (vertex_degree := vertex_degree) ha hb hd hncol).faceBoundary f := by
  change boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol f i ∈
    PolarBoundaryAcross.faceBoundary (normals (nonordinaryPoints P)) normal_cross
      (hspan ha hb hd hncol) f
  rw [← List.mem_toFinset,
    PolarBoundaryAcross.faceBoundary_toFinset (normals (nonordinaryPoints P))
      normal_cross (hspan ha hb hd hncol) f]
  exact PolarBoundaryAcross.boundaryEdge_mem (normals (nonordinaryPoints P))
    normal_cross (hspan ha hb hd hncol) f _

theorem boundaryEdge_vertices
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    (C (vertex_degree := vertex_degree) ha hb hd hncol).edgeVertices
        (boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol f i) =
      {boundaryVertex (vertex_degree := vertex_degree) ha hb hd hncol f i,
        boundaryVertex (vertex_degree := vertex_degree) ha hb hd hncol f
          (ABKPR.faceSucc (C (vertex_degree := vertex_degree) ha hb hd hncol) f i)} := by
  change concreteEdgeVertices (hspan ha hb hd hncol)
      (boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol f i) = _
  unfold boundaryEdge
  rw [ConcretePolarEdgeVertices.concreteEdgeVertices_boundaryEdge]
  unfold orientedEdgeVertices boundaryVertex
  rw [indexEquiv_succ (vertex_degree := vertex_degree) ha hb hd hncol]

abbrev FaceDart := ABKPR.FaceDart
  (C (vertex_degree := vertex_degree) ha hb hd hncol)

noncomputable def dartEquiv :
    FaceDart (vertex_degree := vertex_degree) ha hb hd hncol ≃
      PolarBoundaryAcross.IndexedDart (normals (nonordinaryPoints P)) :=
  Equiv.sigmaCongrRight fun f ↦
    indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f

noncomputable def across
    (q : FaceDart (vertex_degree := vertex_degree) ha hb hd hncol) :
    FaceDart (vertex_degree := vertex_degree) ha hb hd hncol :=
  (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol).symm
    (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
      (normals_ne_zero (nonordinaryPoints P)) normal_cross
      (hspan ha hb hd hncol)
      (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol q))

theorem across_involutive : Function.Involutive
    (across (vertex_degree := vertex_degree) ha hb hd hncol) := by
  intro q
  apply (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol).injective
  simp only [across, Equiv.apply_symm_apply]
  exact PolarBoundaryAcross.across_involutive
    (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
    normal_cross (hspan ha hb hd hncol)
    (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol q)

theorem across_otherFace
    (q : FaceDart (vertex_degree := vertex_degree) ha hb hd hncol) :
    (across (vertex_degree := vertex_degree) ha hb hd hncol q).1 ≠ q.1 := by
  intro h
  have hbad := PolarBoundaryAcross.across_otherFace
    (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
      normal_cross (hspan ha hb hd hncol)
    (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol q)
  apply hbad
  change (across (vertex_degree := vertex_degree) ha hb hd hncol q).1 = q.1
  exact h

theorem across_sameEdge
    (q : FaceDart (vertex_degree := vertex_degree) ha hb hd hncol) :
    boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol q.1 q.2 =
      boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol
        (across (vertex_degree := vertex_degree) ha hb hd hncol q).1
        (across (vertex_degree := vertex_degree) ha hb hd hncol q).2 := by
  have hp := PolarBoundaryAcross.across_sameEdge
    (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
    normal_cross (hspan ha hb hd hncol)
    (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol q)
  have hmap : dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol
      (across (vertex_degree := vertex_degree) ha hb hd hncol q) =
    PolarBoundaryAcross.across (normals (nonordinaryPoints P))
      (normals_ne_zero (nonordinaryPoints P)) normal_cross
      (hspan ha hb hd hncol)
      (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol q) := by
    simp [across]
  have hright :
      boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol
        (across (vertex_degree := vertex_degree) ha hb hd hncol q).1
        (across (vertex_degree := vertex_degree) ha hb hd hncol q).2 =
      PolarBoundaryAcross.boundaryEdge (normals (nonordinaryPoints P)) normal_cross
        (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
          (normals_ne_zero (nonordinaryPoints P)) normal_cross
          (hspan ha hb hd hncol)
          (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol q)).1
        (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
          (normals_ne_zero (nonordinaryPoints P)) normal_cross
          (hspan ha hb hd hncol)
          (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol q)).2 := by
    change PolarBoundaryAcross.boundaryEdge (normals (nonordinaryPoints P)) normal_cross
        (hspan ha hb hd hncol)
        (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol
          (across (vertex_degree := vertex_degree) ha hb hd hncol q)).1
        (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol
          (across (vertex_degree := vertex_degree) ha hb hd hncol q)).2 = _
    rw [hmap]
  rw [hright]
  unfold boundaryEdge
  exact hp

/-- Reindex the literal red-chord pair to the face-degree index. -/
noncomputable def chordPair
    (f : StrictFace (normals (nonordinaryPoints P)))
    (r : PolarRedChordExtraction.ChordLine (P := P) f) :
    Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) ×
      Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) :=
  ((indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).symm
      (PolarRedChordExtraction.chordPair hred (hspan ha hb hd hncol) f r).1,
    (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).symm
      (PolarRedChordExtraction.chordPair hred (hspan ha hb hd hncol) f r).2)

noncomputable def redChords
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Finset (Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) ×
      Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :=
  Finset.univ.image (chordPair hred (vertex_degree := vertex_degree)
    ha hb hd hncol f)

theorem mem_redChords_iff
    (f : StrictFace (normals (nonordinaryPoints P)))
    (p : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) ×
      Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    p ∈ redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f ↔
      ∃ r : PolarRedChordExtraction.ChordLine (P := P) f,
        chordPair hred (vertex_degree := vertex_degree) ha hb hd hncol f r = p := by
  simp [redChords]

theorem chordPair_distinct
    (f : StrictFace (normals (nonordinaryPoints P)))
    (r : PolarRedChordExtraction.ChordLine (P := P) f) :
    (chordPair hred (vertex_degree := vertex_degree) ha hb hd hncol f r).1 ≠
      (chordPair hred (vertex_degree := vertex_degree) ha hb hd hncol f r).2 := by
  intro h
  have hp := congrArg
    (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f) h
  simpa [chordPair] using
    (PolarRedChordExtraction.chordPair_spec hred (hspan ha hb hd hncol) f r).1 hp

theorem chordPair_injective
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Function.Injective
      (chordPair hred (vertex_degree := vertex_degree) ha hb hd hncol f) := by
  intro r s hrs
  apply PolarRedChordExtraction.chordLine_injective hred (hspan ha hb hd hncol) f
  apply Prod.ext
  · apply (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).symm.injective
    exact congrArg Prod.fst hrs
  · apply (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).symm.injective
    exact congrArg Prod.snd hrs

theorem redChord_distinct
    (f : StrictFace (normals (nonordinaryPoints P)))
    (p : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) ×
      Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f))
    (hp : p ∈ redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f) :
    p.1 ≠ p.2 := by
  obtain ⟨r, rfl⟩ := (mem_redChords_iff hred (vertex_degree := vertex_degree)
    ha hb hd hncol f p).mp hp
  exact chordPair_distinct hred (vertex_degree := vertex_degree) ha hb hd hncol f r

def chordEndpoints
    {f : StrictFace (normals (nonordinaryPoints P))}
    (p : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) ×
      Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    Finset (Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :=
  {p.1, p.2}

theorem chordEndpoint_mem_iff
    (f : StrictFace (normals (nonordinaryPoints P)))
    (r : PolarRedChordExtraction.ChordLine (P := P) f)
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    i ∈ chordEndpoints (vertex_degree := vertex_degree) ha hb hd hncol
        (chordPair hred (vertex_degree := vertex_degree) ha hb hd hncol f r) ↔
      indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i ∈
        PolarRedChordExtraction.endpointIndices (hspan ha hb hd hncol) f r.1 := by
  rw [PolarRedChordExtraction.chordPair_spec hred (hspan ha hb hd hncol) f r |>.2]
  simp only [chordEndpoints, chordPair, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (hi | hi)
    · left
      apply (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).injective
      simpa using hi
    · right
      apply (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).injective
      simpa using hi

theorem chordEndpoints_disjoint
    (f : StrictFace (normals (nonordinaryPoints P)))
    {p q : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) ×
      Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)}
    (hp : p ∈ redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f)
    (hq : q ∈ redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f)
    (hpq : p ≠ q) :
    Disjoint (chordEndpoints (vertex_degree := vertex_degree) ha hb hd hncol p)
      (chordEndpoints (vertex_degree := vertex_degree) ha hb hd hncol q) := by
  obtain ⟨r, rfl⟩ := (mem_redChords_iff hred (vertex_degree := vertex_degree)
    ha hb hd hncol f p).mp hp
  obtain ⟨s, rfl⟩ := (mem_redChords_iff hred (vertex_degree := vertex_degree)
    ha hb hd hncol f q).mp hq
  have hrs : r ≠ s := by
    intro h
    exact hpq (congrArg
      (chordPair hred (vertex_degree := vertex_degree) ha hb hd hncol f) h)
  have hdisj := PolarRedChordExtraction.endpointIndices_disjoint hred
    (hspan ha hb hd hncol) f hrs
  rw [Finset.disjoint_left]
  intro i hir his
  exact (Finset.disjoint_left.mp hdisj)
    ((chordEndpoint_mem_iff hred (vertex_degree := vertex_degree)
      ha hb hd hncol f r i).mp hir)
    ((chordEndpoint_mem_iff hred (vertex_degree := vertex_degree)
      ha hb hd hncol f s i).mp his)

theorem redChord_nonadjacent
    (f : StrictFace (normals (nonordinaryPoints P)))
    (p : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) ×
      Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f))
    (hp : p ∈ redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f) :
    p.2 ≠ ABKPR.faceSucc (C (vertex_degree := vertex_degree) ha hb hd hncol) f p.1 ∧
      p.1 ≠ ABKPR.faceSucc (C (vertex_degree := vertex_degree) ha hb hd hncol) f p.2 := by
  obtain ⟨r, rfl⟩ := (mem_redChords_iff hred (vertex_degree := vertex_degree)
    ha hb hd hncol f p).mp hp
  have hnon := PolarRedChordExtraction.redChord_nonadjacent hred
    (hspan ha hb hd hncol) f
    (PolarRedChordExtraction.chordPair hred (hspan ha hb hd hncol) f r)
    (by
      exact (PolarRedChordExtraction.mem_redChords_iff hred
        (hspan ha hb hd hncol) f _).mpr ⟨r, rfl⟩)
  constructor
  · intro h
    apply hnon.1
    have hi := congrArg
      (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f) h
    simpa [chordPair, indexEquiv_succ (vertex_degree := vertex_degree)
      ha hb hd hncol] using hi
  · intro h
    apply hnon.2
    have hi := congrArg
      (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f) h
    simpa [chordPair, indexEquiv_succ (vertex_degree := vertex_degree)
      ha hb hd hncol] using hi

noncomputable def redEndpoints
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Finset (Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :=
  (redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f).biUnion
    (chordEndpoints (vertex_degree := vertex_degree) ha hb hd hncol)

theorem redEndpoint_iff
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    i ∈ redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f ↔
      ∃ p ∈ redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f,
        i = p.1 ∨ i = p.2 := by
  simp [redEndpoints, chordEndpoints]

theorem redEndpoint_reindex_iff
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    i ∈ redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f ↔
      indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i ∈
        PolarRedChordExtraction.redEndpoints hred (hspan ha hb hd hncol) f := by
  constructor
  · intro hi
    obtain ⟨p, hp, hip⟩ := (redEndpoint_iff hred (vertex_degree := vertex_degree)
      ha hb hd hncol f i).mp hi
    obtain ⟨r, rfl⟩ := (mem_redChords_iff hred (vertex_degree := vertex_degree)
      ha hb hd hncol f p).mp hp
    apply (PolarRedChordExtraction.mem_redEndpoints_iff hred
      (hspan ha hb hd hncol) f _).mpr
    refine ⟨PolarRedChordExtraction.chordPair hred (hspan ha hb hd hncol) f r,
      (PolarRedChordExtraction.mem_redChords_iff hred
        (hspan ha hb hd hncol) f _).mpr ⟨r, rfl⟩, ?_⟩
    rcases hip with hip | hip
    · left
      simpa [chordPair] using congrArg
        (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f) hip
    · right
      simpa [chordPair] using congrArg
        (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f) hip
  · intro hi
    obtain ⟨p, hp, hip⟩ := (PolarRedChordExtraction.mem_redEndpoints_iff hred
      (hspan ha hb hd hncol) f _).mp hi
    obtain ⟨r, rfl⟩ := (PolarRedChordExtraction.mem_redChords_iff hred
      (hspan ha hb hd hncol) f p).mp hp
    apply (redEndpoint_iff hred (vertex_degree := vertex_degree)
      ha hb hd hncol f i).mpr
    refine ⟨chordPair hred (vertex_degree := vertex_degree) ha hb hd hncol f r,
      (mem_redChords_iff hred (vertex_degree := vertex_degree)
        ha hb hd hncol f _).mpr ⟨r, rfl⟩, ?_⟩
    rcases hip with hip | hip
    · left
      apply (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).injective
      simpa [chordPair] using hip
    · right
      apply (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).injective
      simpa [chordPair] using hip

theorem redEndpoints_card
    (f : StrictFace (normals (nonordinaryPoints P))) :
    (redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f).card =
      2 * (redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f).card := by
  rw [redEndpoints, Finset.card_biUnion]
  · calc
      (∑ p ∈ redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f,
          (chordEndpoints (vertex_degree := vertex_degree) ha hb hd hncol p).card) =
          ∑ _p ∈ redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f,
            2 := by
              apply Finset.sum_congr rfl
              intro p hp
              exact Finset.card_pair (redChord_distinct hred
                (vertex_degree := vertex_degree) ha hb hd hncol f p hp)
      _ = 2 * (redChords hred (vertex_degree := vertex_degree)
          ha hb hd hncol f).card := by simp [Nat.mul_comm]
  · intro p hp q hq hpq
    exact chordEndpoints_disjoint hred (vertex_degree := vertex_degree)
      ha hb hd hncol f hp hq hpq

noncomputable def stage1Corners
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Finset (Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :=
  (redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f).filter
    (fun i ↦ lineMultiplicity (OnLine (nonordinaryPoints P))
      (boundaryVertex (vertex_degree := vertex_degree) ha hb hd hncol f i).1 = 2)

theorem stage1Corner_iff
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    i ∈ stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol f ↔
      i ∈ redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f ∧
        (C (vertex_degree := vertex_degree) ha hb hd hncol).blueMultiplicity
          (boundaryVertex (vertex_degree := vertex_degree) ha hb hd hncol f i) = 2 := by
  rw [stage1Corners, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hm⟩
    exact ⟨hi, by
      simpa [C, ConcretePolarCellulation.blueCellulationOfVertexDegree,
        ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
        BoundaryExtraction.toBlueCellulation] using hm⟩
  · rintro ⟨hi, hm⟩
    exact ⟨hi, by
      simpa [C, ConcretePolarCellulation.blueCellulationOfVertexDegree,
        ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
        BoundaryExtraction.toBlueCellulation] using hm⟩

theorem stage1Corner_reindex_iff
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f)) :
    i ∈ stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol f ↔
      indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i ∈
        ConcreteBadReceiver.polarStage1Corners hred (hspan ha hb hd hncol) f := by
  rw [stage1Corners, ConcreteBadReceiver.polarStage1Corners,
    Finset.mem_filter, Finset.mem_filter, redEndpoint_reindex_iff]
  rfl

theorem redChords_card_eq_polar
    (f : StrictFace (normals (nonordinaryPoints P))) :
    (redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f).card =
      (PolarRedChordExtraction.redChords hred (hspan ha hb hd hncol) f).card := by
  rw [redChords, Finset.card_image_of_injective _
      (chordPair_injective hred (vertex_degree := vertex_degree) ha hb hd hncol f),
    PolarRedChordExtraction.redChords,
    Finset.card_image_of_injective _
      (PolarRedChordExtraction.chordLine_injective hred (hspan ha hb hd hncol) f)]

theorem redEndpoints_map_indexEquiv
    (f : StrictFace (normals (nonordinaryPoints P))) :
    (redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f).map
        (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).toEmbedding =
      PolarRedChordExtraction.redEndpoints hred (hspan ha hb hd hncol) f := by
  ext j
  simp only [Finset.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (redEndpoint_reindex_iff hred (vertex_degree := vertex_degree)
      ha hb hd hncol f i).mp hi
  · intro hj
    refine ⟨(indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).symm j,
      ?_, by simp⟩
    exact (redEndpoint_reindex_iff hred (vertex_degree := vertex_degree)
      ha hb hd hncol f _).mpr (by simpa using hj)

theorem stage1Corners_map_indexEquiv
    (f : StrictFace (normals (nonordinaryPoints P))) :
    (stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol f).map
        (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).toEmbedding =
      PolarGoodQuadrangleWeight.stage1Corners hred (hspan ha hb hd hncol) f := by
  ext j
  simp only [Finset.mem_map]
  have hpolar (k : BoundaryIndex (normals (nonordinaryPoints P)) f) :
      k ∈ ConcreteBadReceiver.polarStage1Corners hred (hspan ha hb hd hncol) f ↔
        k ∈ PolarGoodQuadrangleWeight.stage1Corners hred
          (hspan ha hb hd hncol) f := by
    rw [ConcreteBadReceiver.polarStage1Corners,
      PolarGoodQuadrangleWeight.stage1Corners,
      Finset.mem_filter, Finset.mem_filter]
    rfl
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact (hpolar _).mp ((stage1Corner_reindex_iff hred
      (vertex_degree := vertex_degree) ha hb hd hncol f i).mp hi)
  · intro hj
    refine ⟨(indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).symm j,
      ?_, by simp⟩
    apply (stage1Corner_reindex_iff hred (vertex_degree := vertex_degree)
      ha hb hd hncol f _).mpr
    exact (hpolar _).mpr (by simpa using hj)

theorem badVertex_receiverCount
    (v : OrientedVertex (nonordinaryPoints P))
    (hmult : (C (vertex_degree := vertex_degree) ha hb hd hncol).blueMultiplicity v = 2) :
    (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
      ∃ i ∈ stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol f,
        boundaryVertex (vertex_degree := vertex_degree) ha hb hd hncol f i = v).card = 2 := by
  have hmult' : lineMultiplicity (OnLine (nonordinaryPoints P)) v.1 = 2 := by
    simpa [C, ConcretePolarCellulation.blueCellulationOfVertexDegree,
      ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
      BoundaryExtraction.toBlueCellulation] using hmult
  have hp := ConcreteBadReceiver.polarStage1Corners_receiverCount
    hred (hspan ha hb hd hncol) v hmult'
  have heq :
      (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
        ∃ i ∈ stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol f,
          boundaryVertex (vertex_degree := vertex_degree) ha hb hd hncol f i = v) =
      (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
        ∃ i ∈ ConcreteBadReceiver.polarStage1Corners hred
            (hspan ha hb hd hncol) f,
          boundaryOrientedVertex (hspan ha hb hd hncol) f i = v) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, hiv⟩
      refine ⟨indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f i,
        (stage1Corner_reindex_iff hred (vertex_degree := vertex_degree)
          ha hb hd hncol f i).mp hi, ?_⟩
      exact hiv
    · rintro ⟨i, hi, hiv⟩
      refine ⟨(indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f).symm i,
        (stage1Corner_reindex_iff hred (vertex_degree := vertex_degree)
          ha hb hd hncol f _).mpr (by simpa using hi), ?_⟩
      simpa [boundaryVertex] using hiv
  rw [heq]
  exact hp

theorem goodTwoQuadrangle_twoGoodCorners
    (f : StrictFace (normals (nonordinaryPoints P)))
    (hdegree : (C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f = 4)
    (hchords : (redChords hred (vertex_degree := vertex_degree)
      ha hb hd hncol f).card = 2)
    (hgood : (redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f \
      stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol f).Nonempty) :
    2 ≤ (redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f \
      stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol f).card := by
  apply PolarGoodQuadrangleWeight.goodTwoQuadrangle_twoGoodCorners_of_indexEquiv
    hred (hspan ha hb hd hncol) f
    (indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol f)
    (redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f)
    (redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol f)
    (stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol f)
  · exact redChords_card_eq_polar hred (vertex_degree := vertex_degree)
      ha hb hd hncol f
  · exact redEndpoints_map_indexEquiv hred (vertex_degree := vertex_degree)
      ha hb hd hncol f
  · exact stage1Corners_map_indexEquiv hred (vertex_degree := vertex_degree)
      ha hb hd hncol f
  · simpa [C, ConcretePolarCellulation.blueCellulationOfVertexDegree,
      ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
      BoundaryExtraction.toBlueCellulation, BlueCellulation.faceDegree] using hdegree
  · exact hchords
  · exact hgood

private theorem fin_three_adjacent
    (i j : Fin 3) (hij : i ≠ j) :
    j = ABKPR.cyclicSucc (by omega : 0 < 3) i ∨
      i = ABKPR.cyclicSucc (by omega : 0 < 3) j := by
  simp only [Fin.ext_iff, ABKPR.cyclicSucc]
  omega

theorem triangle_no_redChord
    (f : StrictFace (normals (nonordinaryPoints P)))
    (hdegree : (C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f = 3) :
    (redChords hred (vertex_degree := vertex_degree) ha hb hd hncol f).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hpne := redChord_distinct hred (vertex_degree := vertex_degree)
    ha hb hd hncol f p hp
  have hnon := redChord_nonadjacent hred (vertex_degree := vertex_degree)
    ha hb hd hncol f p hp
  let castIndex :
      Fin ((C (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f) →
        Fin 3 := fun i ↦ ⟨i.1, by simpa [hdegree] using i.2⟩
  have hcast_inj : Function.Injective castIndex := by
    intro i j hij
    apply Fin.ext
    simpa [castIndex] using congrArg Fin.val hij
  have hne : castIndex p.1 ≠ castIndex p.2 := fun h ↦ hpne (hcast_inj h)
  rcases fin_three_adjacent (castIndex p.1) (castIndex p.2) hne with h | h
  · apply hnon.1
    apply Fin.ext
    have hs :
        (ABKPR.faceSucc (C (vertex_degree := vertex_degree) ha hb hd hncol) f p.1).val =
          (ABKPR.cyclicSucc (by omega : 0 < 3) (castIndex p.1)).val := by
      simp [ABKPR.faceSucc, castIndex, ABKPR.cyclicSucc, hdegree]
    exact (congrArg Fin.val h).trans hs.symm
  · apply hnon.2
    apply Fin.ext
    have hs :
        (ABKPR.faceSucc (C (vertex_degree := vertex_degree) ha hb hd hncol) f p.2).val =
          (ABKPR.cyclicSucc (by omega : 0 < 3) (castIndex p.2)).val := by
      simp [ABKPR.faceSucc, castIndex, ABKPR.cyclicSucc, hdegree]
    exact (congrArg Fin.val h).trans hs.symm

/-- The complete concrete ABKPR discharging data for a reduced magic
configuration, using the literal polar cellulation. -/
noncomputable def toData :
    ABKPR.Data (C (vertex_degree := vertex_degree) ha hb hd hncol) where
  boundaryVertex := boundaryVertex (vertex_degree := vertex_degree) ha hb hd hncol
  boundaryVertex_injective := boundaryVertex_injective
    (vertex_degree := vertex_degree) ha hb hd hncol
  boundaryEdge := boundaryEdge (vertex_degree := vertex_degree) ha hb hd hncol
  boundaryEdge_injective := boundaryEdge_injective
    (vertex_degree := vertex_degree) ha hb hd hncol
  boundaryEdge_mem := boundaryEdge_mem (vertex_degree := vertex_degree)
    ha hb hd hncol
  boundaryEdge_vertices := boundaryEdge_vertices (vertex_degree := vertex_degree)
    ha hb hd hncol
  across := across (vertex_degree := vertex_degree) ha hb hd hncol
  across_involutive := across_involutive (vertex_degree := vertex_degree)
    ha hb hd hncol
  across_otherFace := across_otherFace (vertex_degree := vertex_degree)
    ha hb hd hncol
  across_sameEdge := across_sameEdge (vertex_degree := vertex_degree)
    ha hb hd hncol
  redChords := redChords hred (vertex_degree := vertex_degree) ha hb hd hncol
  redChord_distinct := redChord_distinct hred (vertex_degree := vertex_degree)
    ha hb hd hncol
  redChord_nonadjacent := redChord_nonadjacent hred (vertex_degree := vertex_degree)
    ha hb hd hncol
  redEndpoints := redEndpoints hred (vertex_degree := vertex_degree) ha hb hd hncol
  redEndpoint_iff := redEndpoint_iff hred (vertex_degree := vertex_degree)
    ha hb hd hncol
  redEndpoints_card := redEndpoints_card hred (vertex_degree := vertex_degree)
    ha hb hd hncol
  stage1Corners := stage1Corners hred (vertex_degree := vertex_degree) ha hb hd hncol
  stage1Corner_iff := stage1Corner_iff hred (vertex_degree := vertex_degree)
    ha hb hd hncol
  badVertex_receiverCount := badVertex_receiverCount hred
    (vertex_degree := vertex_degree) ha hb hd hncol
  triangle_no_redChord := triangle_no_redChord hred (vertex_degree := vertex_degree)
    ha hb hd hncol
  goodTwoQuadrangle_twoGoodCorners := goodTwoQuadrangle_twoGoodCorners hred
    (vertex_degree := vertex_degree) ha hb hd hncol

/-- The unconditional concrete data, with the proved literal vertex-degree
identity supplied to the preceding constructor. -/
noncomputable def concreteData :
    ABKPR.Data (ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol) :=
  toData hred
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (nonordinaryPoints P) ha hb hd hncol)
    ha hb hd hncol

end Erdos735.ConcretePolarABKPRData
