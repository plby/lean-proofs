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

import ErdosProblems.Erdos735.ConcreteBadReceiver
import ErdosProblems.Erdos735.ConcretePolarOrientedAcross
import ErdosProblems.Erdos735.ConcretePolarABKPRData

/-!
# Local sectors at a concrete polar corner

Two different faces across two boundary edges of one polar face differ from
the original sign chamber in the two corresponding owner signs.  If those
two opposite faces have a common oriented boundary corner, weak realization
forces that corner to vanish on both owners.  The result below records this
fundamental local-sector fact in a form used by the Stage-3 donation
geometry.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace Erdos735.ConcretePolarLocalSector

open ProjectiveArrangement ProjectiveBoundaryExtraction ChartOrder
open SignVector SignVector.PolarBoundaryAcross SignVector.PolarBoundaryOrder
open SignVector.PolarBoundaryAcrossEndpoints
open SignVector.PolarFace SignVector.PolarPlaneChart
open SignVector.RedChordSector
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := {b // b ∈ B}

variable {B : Finset Point} [Nonempty (Line B)]
variable (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)

private theorem boundaryVertex_mem_edgeVertices_of_onLine
    (f : StrictFace (normals B))
    (i u : BoundaryIndex (normals B) f)
    (hon : OnProjectiveLine
      (normals B (boundaryEdge (normals B) normal_cross hspan f i).1.1)
      (boundaryVertex (normals B) normal_cross hspan f u)) :
    boundaryVertex (normals B) normal_cross hspan f u ∈
      projectiveEdgeVertices (normals B) normal_cross hspan f i := by
  let t : BoundaryIndex (normals B) f := (finRotate _).symm u
  have htu : Erdos957.cyclicSucc t = u := (finRotate _).apply_symm_apply u
  have hon' : OnProjectiveLine
      (normals B (boundaryEdge (normals B) normal_cross hspan f i).1.1)
      (boundaryProjectiveVertex f (faceWitness_realizes (normals B) f)
        normal_cross hspan t) := by
    simpa [t, boundaryVertex] using hon
  have hzero : normals B
      (boundaryEdge (normals B) normal_cross hspan f i).1.1 ⬝ᵥ
      cornerVector f (faceWitness_realizes (normals B) f)
        normal_cross hspan t = 0 := by
    rw [← cornerProjectiveVertex_eq_boundaryProjectiveVertex f
      (faceWitness_realizes (normals B) f) normal_cross hspan t,
      cornerProjectiveVertex, onProjectiveLine_mk_iff] at hon'
    exact hon'
  have hownerMem :
      (boundaryEdge (normals B) normal_cross hspan f i).1.1 ∈
        edgeOwners (normals B) f.1 := by
    change boundaryOwner f (faceWitness_realizes (normals B) f)
      normal_cross hspan i ∈ edgeOwners (normals B) f.1
    exact (boundaryOwnerEquiv f (faceWitness_realizes (normals B) f)
      normal_cross hspan i).2
  have hep := owner_eq_endpoint_of_dot_cornerVector_eq_zero f
    (faceWitness_realizes (normals B) f) normal_cross hspan t
    (boundaryEdge (normals B) normal_cross hspan f i).1.1 hownerMem hzero
  have hinj : Function.Injective
      (boundaryOwner f (faceWitness_realizes (normals B) f)
        normal_cross hspan) := by
    intro x y hxy
    apply (boundaryOwnerEquiv f (faceWitness_realizes (normals B) f)
      normal_cross hspan).injective
    exact Subtype.ext hxy
  have hi : i = t ∨ i = Erdos957.cyclicSucc t := by
    rcases hep with hep | hep
    · exact Or.inl (hinj hep)
    · exact Or.inr (hinj hep)
  simp only [projectiveEdgeVertices, Finset.mem_insert, Finset.mem_singleton]
  rcases hi with rfl | hi
  · right
    rw [htu]
  · left
    rw [hi, htu]

private theorem cyclicAdjacent_of_common_boundaryVertex
    (f : StrictFace (normals B))
    (i j : BoundaryIndex (normals B) f) (hij : i ≠ j)
    {v : ℙ ℝ Vec3}
    (hvi : v ∈ projectiveEdgeVertices (normals B) normal_cross hspan f i)
    (hvj : v ∈ projectiveEdgeVertices (normals B) normal_cross hspan f j) :
    Erdos957.cyclicSucc i = j ∨ Erdos957.cyclicSucc j = i := by
  have hinj : Function.Injective
      (boundaryVertex (normals B) normal_cross hspan f) := by
    intro x y hxy
    apply (finRotate _).symm.injective
    apply boundaryProjectiveVertex_injective f
      (faceWitness_realizes (normals B) f) normal_cross hspan
    simpa only [boundaryVertex] using hxy
  simp only [projectiveEdgeVertices, Finset.mem_insert,
    Finset.mem_singleton] at hvi hvj
  rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
  · exact (hij (hinj (hvi.symm.trans hvj))).elim
  · exact Or.inr (hinj (hvj.symm.trans hvi))
  · exact Or.inl (hinj (hvi.symm.trans hvj))
  · exfalso
    apply hij
    apply (finRotate _).injective
    exact hinj (hvi.symm.trans hvj)

theorem across_sign_ne_at_first_owner
    (d : StrictFace (normals B))
    (i j : BoundaryIndex (normals B) d) (hij : i ≠ j) :
    ((across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1).1
        (boundaryEdge (normals B) normal_cross hspan d i).1.1 ≠
      ((across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, j⟩).1).1
        (boundaryEdge (normals B) normal_cross hspan d i).1.1 := by
  let ei := boundaryEdge (normals B) normal_cross hspan d i
  let ej := boundaryEdge (normals B) normal_cross hspan d j
  have howner : ei.1.1 ≠ ej.1.1 := by
    intro h
    apply hij
    apply (boundaryOwnerEquiv d (faceWitness_realizes (normals B) d)
      normal_cross hspan).injective
    exact Subtype.ext h
  have hdi : ei ∈ faceEdges (normals B) d :=
    boundaryEdge_mem (normals B) normal_cross hspan d i
  have hdj : ej ∈ faceEdges (normals B) d :=
    boundaryEdge_mem (normals B) normal_cross hspan d j
  have hjinc : FaceEdgeIncident (normals B) d ej :=
    (mem_faceEdges_iff (normals B) d ej).mp hdj
  have hiFace := across_face_eq_edgeFace_flip
    (normals B) (normals_ne_zero B) normal_cross hspan
      (⟨d, i⟩ : IndexedDart (normals B))
  have hjFace := across_face_eq_edgeFace_flip
    (normals B) (normals_ne_zero B) normal_cross hspan
      (⟨d, j⟩ : IndexedDart (normals B))
  rw [hiFace, hjFace]
  simp only [edgeFace_sign, extendEdgeSign_support]
  rw [extendEdgeSign_other ej.1 _ howner]
  have hsign := hjinc ⟨ei.1.1, howner⟩
  rw [← hsign]
  cases d.1 ei.1.1 <;> decide

/-- A common corner of the faces across two distinct boundary edges lies on
both supporting projective lines. -/
theorem common_across_corner_on_both_supports
    (d : StrictFace (normals B))
    (i j : BoundaryIndex (normals B) d) (hij : i ≠ j)
    (p : BoundaryIndex (normals B)
      (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1)
    (q : BoundaryIndex (normals B)
      (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, j⟩).1)
    (hpq : boundaryOrientedVertex hspan
        (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1 p =
      boundaryOrientedVertex hspan
        (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, j⟩).1 q) :
    Incident
        (boundaryOrientedVertex hspan
          (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1 p).1.1
        (boundaryEdge (normals B) normal_cross hspan d i).1.1.1 ∧
      Incident
        (boundaryOrientedVertex hspan
          (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1 p).1.1
        (boundaryEdge (normals B) normal_cross hspan d j).1.1.1 := by
  let fi :=
    (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1
  let fj :=
    (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, j⟩).1
  let v := boundaryOrientedVertex hspan fi p
  let y := orientedRep v
  have hwi : WeaklyRealizes (normals B) fi.1 y :=
    orientedRep_boundaryOrientedVertex_weaklyRealizes hspan fi p
  have hwj : WeaklyRealizes (normals B) fj.1 y := by
    have h := orientedRep_boundaryOrientedVertex_weaklyRealizes hspan fj q
    simpa [v, y, fi, fj, hpq] using h
  have hsign_i : fi.1
      (boundaryEdge (normals B) normal_cross hspan d i).1.1 ≠
      fj.1 (boundaryEdge (normals B) normal_cross hspan d i).1.1 := by
    exact across_sign_ne_at_first_owner hspan d i j hij
  have hzero_i : normals B
      (boundaryEdge (normals B) normal_cross hspan d i).1.1 ⬝ᵥ y = 0 := by
    by_contra hne
    exact hsign_i (SignVector.LocalReceiver.sign_eq_of_weak_of_dot_ne_zero
      hwi hwj hne)
  have hsign_j : fi.1
      (boundaryEdge (normals B) normal_cross hspan d j).1.1 ≠
      fj.1 (boundaryEdge (normals B) normal_cross hspan d j).1.1 := by
    exact (across_sign_ne_at_first_owner hspan d j i hij.symm).symm
  have hzero_j : normals B
      (boundaryEdge (normals B) normal_cross hspan d j).1.1 ⬝ᵥ y = 0 := by
    by_contra hne
    exact hsign_j (SignVector.LocalReceiver.sign_eq_of_weak_of_dot_ne_zero
      hwi hwj hne)
  constructor
  · change Incident v.1.1 _
    rw [← orientedRep_projectivization v]
    exact (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).2 hzero_i
  · change Incident v.1.1 _
    rw [← orientedRep_projectivization v]
    exact (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).2 hzero_j

/-- The common corner is also a boundary corner of the original face.  In
particular, local data attached to that original corner (such as blue
multiplicity on a bad quadrangle) transports to the shared corner. -/
theorem exists_boundaryOrientedVertex_eq_common_across_corner
    (d : StrictFace (normals B))
    (i j : BoundaryIndex (normals B) d) (hij : i ≠ j)
    (p : BoundaryIndex (normals B)
      (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1)
    (q : BoundaryIndex (normals B)
      (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, j⟩).1)
    (hpq : boundaryOrientedVertex hspan
        (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1 p =
      boundaryOrientedVertex hspan
        (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, j⟩).1 q) :
    ∃ u : BoundaryIndex (normals B) d,
      boundaryOrientedVertex hspan d u =
        boundaryOrientedVertex hspan
          (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1 p := by
  let di : IndexedDart (normals B) := ⟨d, i⟩
  let fi := (across (normals B) (normals_ne_zero B) normal_cross hspan di).1
  let v := boundaryOrientedVertex hspan fi p
  let y := orientedRep v
  let ei := boundaryEdge (normals B) normal_cross hspan d i
  have hsupp := common_across_corner_on_both_supports hspan d i j hij p q hpq
  have hwi : WeaklyRealizes (normals B) fi.1 y :=
    orientedRep_boundaryOrientedVertex_weaklyRealizes hspan fi p
  have hzero : normals B ei.1.1 ⬝ᵥ y = 0 := by
    have hs := hsupp.1
    change OnProjectiveLine (normals B ei.1.1) v.1.1 at hs
    rw [← orientedRep_projectivization v,
      onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)] at hs
    exact hs
  have heid : ei ∈ faceEdges (normals B) d :=
    boundaryEdge_mem (normals B) normal_cross hspan d i
  have heifi : ei ∈ faceEdges (normals B) fi := by
    have heq := across_sameEdge (normals B) (normals_ne_zero B)
      normal_cross hspan di
    change boundaryEdge (normals B) normal_cross hspan d i ∈
      faceEdges (normals B) fi
    rw [heq]
    exact boundaryEdge_mem (normals B) normal_cross hspan
      (across (normals B) (normals_ne_zero B) normal_cross hspan di).1
      (across (normals B) (normals_ne_zero B) normal_cross hspan di).2
  have hwd : WeaklyRealizes (normals B) d.1 y :=
    weaklyRealizes_transfer_incident heifi heid hwi hzero
  exact (ConcreteBadReceiver.exists_boundaryOrientedVertex_eq_iff_weaklyRealizes
    hspan d v).2 hwd

/-- Consequently the two edges of the original face are cyclically
adjacent.  This is the precise local-planarity statement needed to turn a
shared donation corner into a flank of a bad quadrangle. -/
theorem adjacent_edges_of_common_across_corner
    (d : StrictFace (normals B))
    (i j : BoundaryIndex (normals B) d) (hij : i ≠ j)
    (p : BoundaryIndex (normals B)
      (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1)
    (q : BoundaryIndex (normals B)
      (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, j⟩).1)
    (hpq : boundaryOrientedVertex hspan
        (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, i⟩).1 p =
      boundaryOrientedVertex hspan
        (across (normals B) (normals_ne_zero B) normal_cross hspan ⟨d, j⟩).1 q) :
    Erdos957.cyclicSucc i = j ∨ Erdos957.cyclicSucc j = i := by
  let di : IndexedDart (normals B) := ⟨d, i⟩
  let fi := (across (normals B) (normals_ne_zero B) normal_cross hspan di).1
  let v := boundaryOrientedVertex hspan fi p
  let y := orientedRep v
  let ei := boundaryEdge (normals B) normal_cross hspan d i
  have hsupp := common_across_corner_on_both_supports hspan d i j hij p q hpq
  have hwi : WeaklyRealizes (normals B) fi.1 y :=
    orientedRep_boundaryOrientedVertex_weaklyRealizes hspan fi p
  have hzero : normals B ei.1.1 ⬝ᵥ y = 0 := by
    have hs := hsupp.1
    change OnProjectiveLine (normals B ei.1.1) v.1.1 at hs
    rw [← orientedRep_projectivization v,
      onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)] at hs
    exact hs
  have heid : ei ∈ faceEdges (normals B) d :=
    boundaryEdge_mem (normals B) normal_cross hspan d i
  have heifi : ei ∈ faceEdges (normals B) fi := by
    have heq := across_sameEdge (normals B) (normals_ne_zero B)
      normal_cross hspan di
    change boundaryEdge (normals B) normal_cross hspan d i ∈
      faceEdges (normals B) fi
    rw [heq]
    exact boundaryEdge_mem (normals B) normal_cross hspan
      (across (normals B) (normals_ne_zero B) normal_cross hspan di).1
      (across (normals B) (normals_ne_zero B) normal_cross hspan di).2
  have hwd : WeaklyRealizes (normals B) d.1 y :=
    weaklyRealizes_transfer_incident heifi heid hwi hzero
  obtain ⟨u, hu⟩ :=
    (ConcreteBadReceiver.exists_boundaryOrientedVertex_eq_iff_weaklyRealizes
      hspan d v).2 hwd
  have hproj : boundaryVertex (normals B) normal_cross hspan d u = v.1.1 := by
    exact congrArg (fun z : OrientedVertex B ↦ z.1.1) hu
  have hui : boundaryVertex (normals B) normal_cross hspan d u ∈
      projectiveEdgeVertices (normals B) normal_cross hspan d i := by
    apply boundaryVertex_mem_edgeVertices_of_onLine
    rw [hproj]
    exact hsupp.1
  have huj : boundaryVertex (normals B) normal_cross hspan d u ∈
      projectiveEdgeVertices (normals B) normal_cross hspan d j := by
    apply boundaryVertex_mem_edgeVertices_of_onLine
    rw [hproj]
    exact hsupp.2
  exact cyclicAdjacent_of_common_boundaryVertex hspan d i j hij hui huj

end Erdos735.ConcretePolarLocalSector

namespace Erdos735.ConcretePolarABKPRData

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarBoundaryAcross SignVector.PolarBoundaryOrder
open ConcretePolarOrientedVertex

abbrev LocalSectorPoint := ProjectiveArrangement.Point

variable {P : Finset LocalSectorPoint} {w : LocalSectorPoint → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : LocalSectorPoint}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]
variable (vertex_degree :
  ∀ v : OrientedVertex (nonordinaryPoints P),
    (ConcretePolarEdgeVertices.concreteVertexEdges (hspan ha hb hd hncol) v).card =
      2 * lineMultiplicity (OnLine (nonordinaryPoints P)) v.1)

private abbrev LC := C (vertex_degree := vertex_degree) ha hb hd hncol
private abbrev LD := toData hred (vertex_degree := vertex_degree) ha hb hd hncol

/-- Reindexed form of the literal local-sector theorem, directly usable by
the concrete `ABKPR.Data`. -/
theorem adjacent_edges_of_common_across_corner
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i j : Fin ((LC (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree f))
    (hij : i ≠ j)
    (p : Fin ((LC (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree
      ((LD hred (vertex_degree := vertex_degree) ha hb hd hncol).across ⟨f, i⟩).1))
    (q : Fin ((LC (vertex_degree := vertex_degree) ha hb hd hncol).faceDegree
      ((LD hred (vertex_degree := vertex_degree) ha hb hd hncol).across ⟨f, j⟩).1))
    (hpq : (LD hred (vertex_degree := vertex_degree) ha hb hd hncol).boundaryVertex
        ((LD hred (vertex_degree := vertex_degree) ha hb hd hncol).across ⟨f, i⟩).1 p =
      (LD hred (vertex_degree := vertex_degree) ha hb hd hncol).boundaryVertex
        ((LD hred (vertex_degree := vertex_degree) ha hb hd hncol).across ⟨f, j⟩).1 q) :
    ABKPR.faceSucc (LC (vertex_degree := vertex_degree) ha hb hd hncol) f i = j ∨
      ABKPR.faceSucc (LC (vertex_degree := vertex_degree) ha hb hd hncol) f j = i := by
  let E := indexEquiv (vertex_degree := vertex_degree) ha hb hd hncol
  have hmap (r : FaceDart (vertex_degree := vertex_degree) ha hb hd hncol) :
      dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol
        ((LD hred (vertex_degree := vertex_degree) ha hb hd hncol).across r) =
      PolarBoundaryAcross.across (normals (nonordinaryPoints P))
        (normals_ne_zero (nonordinaryPoints P)) normal_cross
        (hspan ha hb hd hncol)
        (dartEquiv (vertex_degree := vertex_degree) ha hb hd hncol r) := by
    simp [LD, toData, ConcretePolarABKPRData.across]
  have hface_i :
      ((LD hred (vertex_degree := vertex_degree) ha hb hd hncol).across ⟨f, i⟩).1 =
      (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
        (normals_ne_zero (nonordinaryPoints P)) normal_cross
        (hspan ha hb hd hncol) ⟨f, E f i⟩).1 :=
    congrArg Sigma.fst (hmap ⟨f, i⟩)
  have hface_j :
      ((LD hred (vertex_degree := vertex_degree) ha hb hd hncol).across ⟨f, j⟩).1 =
      (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
        (normals_ne_zero (nonordinaryPoints P)) normal_cross
        (hspan ha hb hd hncol) ⟨f, E f j⟩).1 :=
    congrArg Sigma.fst (hmap ⟨f, j⟩)
  let pi : BoundaryIndex (normals (nonordinaryPoints P))
      (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
        (normals_ne_zero (nonordinaryPoints P)) normal_cross
        (hspan ha hb hd hncol) ⟨f, E f i⟩).1 :=
    hface_i ▸ E _ p
  let qj : BoundaryIndex (normals (nonordinaryPoints P))
      (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
        (normals_ne_zero (nonordinaryPoints P)) normal_cross
        (hspan ha hb hd hncol) ⟨f, E f j⟩).1 :=
    hface_j ▸ E _ q
  have hpq' : boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
          (normals_ne_zero (nonordinaryPoints P)) normal_cross
          (hspan ha hb hd hncol) ⟨f, E f i⟩).1 pi =
      boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (nonordinaryPoints P))
          (normals_ne_zero (nonordinaryPoints P)) normal_cross
          (hspan ha hb hd hncol) ⟨f, E f j⟩).1 qj := by
    cases hface_i
    cases hface_j
    exact hpq
  have hlit := ConcretePolarLocalSector.adjacent_edges_of_common_across_corner
    (hspan ha hb hd hncol) f (E f i) (E f j)
    (fun h ↦ hij ((E f).injective h)) pi qj hpq'
  rcases hlit with h | h
  · left
    apply (E f).injective
    rw [indexEquiv_succ (vertex_degree := vertex_degree)]
    exact h
  · right
    apply (E f).injective
    rw [indexEquiv_succ (vertex_degree := vertex_degree)]
    exact h

/-- Unconditional specialization using the proved literal vertex-degree
identity. -/
theorem concreteData_adjacent_edges_of_common_across_corner
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i j : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree f))
    (hij : i ≠ j)
    (p : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree
        ((concreteData hred ha hb hd hncol).across ⟨f, i⟩).1))
    (q : Fin ((ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol).faceDegree
        ((concreteData hred ha hb hd hncol).across ⟨f, j⟩).1))
    (hpq : (concreteData hred ha hb hd hncol).boundaryVertex
        ((concreteData hred ha hb hd hncol).across ⟨f, i⟩).1 p =
      (concreteData hred ha hb hd hncol).boundaryVertex
        ((concreteData hred ha hb hd hncol).across ⟨f, j⟩).1 q) :
    ABKPR.faceSucc (ConcretePolarCellulation.blueCellulation
      (nonordinaryPoints P) ha hb hd hncol) f i = j ∨
      ABKPR.faceSucc (ConcretePolarCellulation.blueCellulation
        (nonordinaryPoints P) ha hb hd hncol) f j = i := by
  exact adjacent_edges_of_common_across_corner hred
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (nonordinaryPoints P) ha hb hd hncol)
    ha hb hd hncol f i j hij p q hpq

end Erdos735.ConcretePolarABKPRData
