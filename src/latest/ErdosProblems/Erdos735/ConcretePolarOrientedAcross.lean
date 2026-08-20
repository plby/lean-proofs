/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.ConcretePolarOrientedVertex
import ErdosProblems.Erdos735.RedChordSector
import ErdosProblems.Erdos735.PolarBoundaryAcrossEndpoints

/-!
# Oriented endpoint compatibility across polar face boundaries

Projectively equal corner covectors on the two sides of an arrangement edge
are positive, rather than negative, scalar multiples: both weakly realize a
common incident face.  Thus a generic chart assigns them the same sheet.
This upgrades the projective endpoint pairing to a literal equality of the
global oriented endpoints in `projectiveVertices B × Bool`.
-/

open Classical
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization BigOperators
open Matrix

namespace Erdos735.ConcretePolarOrientedVertex

open ProjectiveArrangement SignVector
open SignVector.PolarFace SignVector.PolarBoundaryOrder
open SignVector.PolarBoundaryAcross SignVector.PolarPlaneChart
open SignVector.RedChordSector
open SignVector.PolarBoundaryAcrossEndpoints
open ProjectiveBoundaryExtraction ChartOrder

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- A nonzero weak realization evaluates positively on the sum of the
oriented normals when the normals span three-space. -/
theorem orientedSum_dot_pos_of_weak_of_span
    {n : I → Vec3} {s : I → Bool} {x y : Vec3}
    (hx : Realizes n s x)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (hy0 : y ≠ 0) (hy : WeaklyRealizes n s y) :
    0 < orientedSum n s ⬝ᵥ y := by
  have hex : ∃ i, 0 < signed (s i) (n i ⬝ᵥ y) := by
    by_contra hnot
    push Not at hnot
    have hallSigned : ∀ i, signed (s i) (n i ⬝ᵥ y) = 0 := by
      intro i
      exact le_antisymm (hnot i) (hy i)
    have hall : ∀ i, n i ⬝ᵥ y = 0 := by
      intro i
      have hi := hallSigned i
      cases hsi : s i <;> simpa [signed, hsi] using hi
    let L : Vec3 →ₗ[ℝ] ℝ :=
      { toFun := fun z ↦ z ⬝ᵥ y
        map_add' := by intro u v; simp [add_dotProduct]
        map_smul' := by intro c z; simp [smul_dotProduct] }
    have hrange : Set.range n ⊆ L.ker := by
      rintro z ⟨i, rfl⟩
      exact hall i
    have hle : Submodule.span ℝ (Set.range n) ≤ L.ker :=
      (Submodule.span_le).2 hrange
    rw [hspan] at hle
    have hself : y ⬝ᵥ y = 0 := hle (by simp)
    exact hy0 (dotProduct_self_eq_zero.mp hself)
  rw [orientedSum, sum_dotProduct]
  apply Finset.sum_pos' (fun i _ ↦ by
    simpa [orientedNormal_dot] using hy i)
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Finset.mem_univ i, by simpa [orientedNormal_dot] using hi⟩

/-- A weak covector vanishing on an edge support weakly realizes every
strict face incident with that edge. -/
theorem weaklyRealizes_transfer_incident
    {n : I → Vec3} {f g : StrictFace n} {e : StrictEdge n} {y : Vec3}
    (hef : e ∈ faceEdges n f) (heg : e ∈ faceEdges n g)
    (hy : WeaklyRealizes n f.1 y) (hzero : n e.1.1 ⬝ᵥ y = 0) :
    WeaklyRealizes n g.1 y := by
  intro j
  by_cases hj : j = e.1.1
  · subst j
    rw [hzero]
    cases g.1 e.1.1 <;> simp [signed]
  · have hf := (mem_faceEdges_iff n f e).mp hef ⟨j, hj⟩
    have hg := (mem_faceEdges_iff n g e).mp heg ⟨j, hj⟩
    rw [hg, ← hf]
    exact hy j

variable {B : Finset Point} [Nonempty (Line B)]
variable (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)

/-- Either endpoint corner of an indexed edge vanishes on the edge's
supporting normal. -/
theorem boundaryCornerVector_on_edge
    (f : StrictFace (normals B))
    (k i : BoundaryIndex (normals B) f)
    (hi : i = k ∨ i = Erdos957.cyclicSucc k) :
    normals B (boundaryEdge (normals B) normal_cross hspan f k).1.1 ⬝ᵥ
      boundaryCornerVector hspan f i = 0 := by
  have hinc : OnProjectiveLine
      (normals B (boundaryEdge (normals B) normal_cross hspan f k).1.1)
      (boundaryVertex (normals B) normal_cross hspan f i) := by
    rcases hi with hi | hi
    · simpa only [hi] using
        boundaryVertex_on_edge_start (normals B) normal_cross hspan f k
    · simpa only [hi] using
        boundaryVertex_on_edge_finish (normals B) normal_cross hspan f k
  apply (onProjectiveLine_mk_iff _ _
    (boundaryCornerVector_ne_zero hspan f i)).mp
  rwa [boundaryCorner_projectivization hspan f i]

/-- Projectively equal endpoint corners on two occurrences of the same
strict edge have the same chart sheet and hence are equal as global oriented
vertices. -/
theorem boundaryOrientedVertex_eq_of_projective_eq_of_sameEdge
    {f g : StrictFace (normals B)}
    {kf : BoundaryIndex (normals B) f}
    {kg : BoundaryIndex (normals B) g}
    {i : BoundaryIndex (normals B) f}
    {j : BoundaryIndex (normals B) g}
    (hi : i = kf ∨ i = Erdos957.cyclicSucc kf)
    (hj : j = kg ∨ j = Erdos957.cyclicSucc kg)
    (hedge : boundaryEdge (normals B) normal_cross hspan f kf =
      boundaryEdge (normals B) normal_cross hspan g kg)
    (hproj : boundaryVertex (normals B) normal_cross hspan f i =
      boundaryVertex (normals B) normal_cross hspan g j) :
    boundaryOrientedVertex hspan f i = boundaryOrientedVertex hspan g j := by
  let ef := boundaryEdge (normals B) normal_cross hspan f kf
  let eg := boundaryEdge (normals B) normal_cross hspan g kg
  let y := boundaryCornerVector hspan f i
  let z := boundaryCornerVector hspan g j
  have hy0 : y ≠ 0 := boundaryCornerVector_ne_zero hspan f i
  have hz0 : z ≠ 0 := boundaryCornerVector_ne_zero hspan g j
  have hyweak : WeaklyRealizes (normals B) f.1 y :=
    cornerVector_weaklyRealizes f (faceWitness_realizes (normals B) f)
      normal_cross hspan ((finRotate _).symm i)
  have hzweak : WeaklyRealizes (normals B) g.1 z :=
    cornerVector_weaklyRealizes g (faceWitness_realizes (normals B) g)
      normal_cross hspan ((finRotate _).symm j)
  have hyzero : normals B ef.1.1 ⬝ᵥ y = 0 :=
    boundaryCornerVector_on_edge hspan f kf i hi
  have hzzero : normals B eg.1.1 ⬝ᵥ z = 0 :=
    boundaryCornerVector_on_edge hspan g kg j hj
  have hef : ef ∈ faceEdges (normals B) f :=
    boundaryEdge_mem (normals B) normal_cross hspan f kf
  have heg : eg ∈ faceEdges (normals B) g :=
    boundaryEdge_mem (normals B) normal_cross hspan g kg
  have hefg : ef = eg := hedge
  have hegf : eg ∈ faceEdges (normals B) f := by
    rw [← hefg]
    exact hef
  have hzweakf : WeaklyRealizes (normals B) f.1 z := by
    exact weaklyRealizes_transfer_incident heg hegf hzweak hzzero
  have hypos : 0 < orientedSum (normals B) f.1 ⬝ᵥ y :=
    orientedSum_dot_pos_of_weak_of_span
      (faceWitness_realizes (normals B) f) hspan hy0 hyweak
  have hzpos : 0 < orientedSum (normals B) f.1 ⬝ᵥ z :=
    orientedSum_dot_pos_of_weak_of_span
      (faceWitness_realizes (normals B) f) hspan hz0 hzweakf
  have hmk : Projectivization.mk ℝ y hy0 = Projectivization.mk ℝ z hz0 := by
    rw [boundaryCorner_projectivization hspan f i,
      boundaryCorner_projectivization hspan g j]
    exact hproj
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ y z hy0 hz0).mp hmk
  have hdot := congrArg (fun u : Vec3 ↦ orientedSum (normals B) f.1 ⬝ᵥ u) ha
  simp only [dotProduct_smul, smul_eq_mul] at hdot
  have ha_pos : 0 < a := by nlinarith
  have hchart := congrArg (chartF B) ha
  simp only [map_smul, smul_eq_mul] at hchart
  apply Prod.ext
  · apply Subtype.ext
    exact hproj
  · apply Bool.decide_congr
    rw [← hchart]
    exact mul_pos_iff_of_pos_left ha_pos

/-- The canonical homogeneous representative of a boundary vertex weakly
realizes the sign chamber whose polar boundary contains it. -/
theorem orientedRep_boundaryOrientedVertex_weaklyRealizes
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    WeaklyRealizes (normals B) f.1
      (orientedRep (boundaryOrientedVertex hspan f i)) := by
  let y := boundaryCornerVector hspan f i
  let v := boundaryOrientedVertex hspan f i
  let z := orientedRep v
  have hy0 : y ≠ 0 := boundaryCornerVector_ne_zero hspan f i
  have hz0 : z ≠ 0 := orientedRep_ne_zero v
  have hmk : Projectivization.mk ℝ y hy0 = Projectivization.mk ℝ z hz0 := by
    rw [boundaryCorner_projectivization hspan f i,
      orientedRep_projectivization v]
    rfl
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℝ y z hy0 hz0).mp hmk
  have hchart := congrArg (chartF B) ha
  simp only [map_smul, smul_eq_mul] at hchart
  have hzchart : chartF B z = if v.2 then 1 else -1 :=
    chartF_orientedRep v
  have hychart0 : chartF B y ≠ 0 := chart_boundaryCornerVector_ne_zero hspan f i
  have ha_pos : 0 < a := by
    by_cases hypos : 0 < chartF B y
    · have hvtrue : v.2 = true := by
        change decide (0 < chartF B y) = true
        exact decide_eq_true hypos
      rw [hzchart, hvtrue] at hchart
      norm_num at hchart
      linarith
    · have hyneg : chartF B y < 0 := lt_of_le_of_ne
        (le_of_not_gt hypos) hychart0
      have hvfalse : v.2 = false := by
        change decide (0 < chartF B y) = false
        exact decide_eq_false hypos
      rw [hzchart, hvfalse] at hchart
      norm_num at hchart
      linarith
  have hyweak : WeaklyRealizes (normals B) f.1 y :=
    cornerVector_weaklyRealizes f (faceWitness_realizes (normals B) f)
      normal_cross hspan ((finRotate _).symm i)
  intro k
  have hk := hyweak k
  rw [← ha, dotProduct_smul, smul_eq_mul, signed_mul] at hk
  nlinarith

/-- The initial oriented endpoint of a dart is one of the two oriented
endpoints of the same edge on the opposite face. -/
theorem boundaryOrientedVertex_start_is_across_endpoint
    (d : IndexedDart (normals B)) :
    boundaryOrientedVertex hspan d.1 d.2 =
        boundaryOrientedVertex hspan
          (across (normals B) (normals_ne_zero B) normal_cross hspan d).1
          (across (normals B) (normals_ne_zero B) normal_cross hspan d).2 ∨
      boundaryOrientedVertex hspan d.1 d.2 =
        boundaryOrientedVertex hspan
          (across (normals B) (normals_ne_zero B) normal_cross hspan d).1
          (Erdos957.cyclicSucc
            (across (normals B) (normals_ne_zero B) normal_cross hspan d).2) := by
  have hedge := across_sameEdge (normals B) (normals_ne_zero B) normal_cross hspan d
  rcases PolarBoundaryAcrossEndpoints.boundaryVertex_start_is_across_endpoint
      (normals B) (normals_ne_zero B) normal_cross hspan d with h | h
  · left
    exact boundaryOrientedVertex_eq_of_projective_eq_of_sameEdge hspan
      (Or.inl rfl) (Or.inl rfl) hedge h
  · right
    exact boundaryOrientedVertex_eq_of_projective_eq_of_sameEdge hspan
      (Or.inl rfl) (Or.inr rfl) hedge h

/-- The terminal oriented endpoint of a dart is one of the two oriented
endpoints of the same edge on the opposite face. -/
theorem boundaryOrientedVertex_finish_is_across_endpoint
    (d : IndexedDart (normals B)) :
    boundaryOrientedVertex hspan d.1 (Erdos957.cyclicSucc d.2) =
        boundaryOrientedVertex hspan
          (across (normals B) (normals_ne_zero B) normal_cross hspan d).1
          (across (normals B) (normals_ne_zero B) normal_cross hspan d).2 ∨
      boundaryOrientedVertex hspan d.1 (Erdos957.cyclicSucc d.2) =
        boundaryOrientedVertex hspan
          (across (normals B) (normals_ne_zero B) normal_cross hspan d).1
          (Erdos957.cyclicSucc
            (across (normals B) (normals_ne_zero B) normal_cross hspan d).2) := by
  have hedge := across_sameEdge (normals B) (normals_ne_zero B) normal_cross hspan d
  rcases PolarBoundaryAcrossEndpoints.boundaryVertex_finish_is_across_endpoint
      (normals B) (normals_ne_zero B) normal_cross hspan d with h | h
  · left
    exact boundaryOrientedVertex_eq_of_projective_eq_of_sameEdge hspan
      (Or.inr rfl) (Or.inl rfl) hedge h
  · right
    exact boundaryOrientedVertex_eq_of_projective_eq_of_sameEdge hspan
      (Or.inr rfl) (Or.inr rfl) hedge h

/-- The two global oriented endpoints of an indexed boundary edge. -/
def orientedEdgeVertices (f : StrictFace (normals B))
    (i : BoundaryIndex (normals B) f) : Finset (OrientedVertex B) :=
  {boundaryOrientedVertex hspan f i,
    boundaryOrientedVertex hspan f (Erdos957.cyclicSucc i)}

@[simp] theorem orientedEdgeVertices_card
    (f : StrictFace (normals B)) (i : BoundaryIndex (normals B) f) :
    (orientedEdgeVertices hspan f i).card = 2 := by
  exact Finset.card_pair (boundaryOrientedVertex_ne_succ hspan f i)

/-- Across-edge pairing preserves the exact unordered pair of global
oriented endpoints. -/
theorem orientedEdgeVertices_across (d : IndexedDart (normals B)) :
    orientedEdgeVertices hspan d.1 d.2 =
      orientedEdgeVertices hspan
        (across (normals B) (normals_ne_zero B) normal_cross hspan d).1
        (across (normals B) (normals_ne_zero B) normal_cross hspan d).2 := by
  apply Finset.Subset.antisymm
  · intro v hv
    simp only [orientedEdgeVertices, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    rcases hv with rfl | rfl
    · exact boundaryOrientedVertex_start_is_across_endpoint hspan d
    · exact boundaryOrientedVertex_finish_is_across_endpoint hspan d
  · intro v hv
    let d' := across (normals B) (normals_ne_zero B) normal_cross hspan d
    have hinv := across_involutive (normals B) (normals_ne_zero B) normal_cross hspan d
    have hstart := boundaryOrientedVertex_start_is_across_endpoint hspan d'
    have hfinish := boundaryOrientedVertex_finish_is_across_endpoint hspan d'
    simp only [orientedEdgeVertices, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    change across (normals B) (normals_ne_zero B) normal_cross hspan d' = d at hinv
    rw [hinv] at hstart hfinish
    rcases hv with rfl | rfl
    · exact hstart
    · exact hfinish

/-- Two occurrences of the same strict edge are either the same indexed
dart or the unique dart on the opposite face. -/
theorem indexedDart_eq_or_across_of_sameEdge
    (d q : IndexedDart (normals B))
    (hedge : boundaryEdge (normals B) normal_cross hspan d.1 d.2 =
      boundaryEdge (normals B) normal_cross hspan q.1 q.2) :
    q = d ∨ q = across (normals B) (normals_ne_zero B) normal_cross hspan d := by
  let e := boundaryEdge (normals B) normal_cross hspan d.1 d.2
  let d' := across (normals B) (normals_ne_zero B) normal_cross hspan d
  have hed : e ∈ faceEdges (normals B) d.1 :=
    boundaryEdge_mem (normals B) normal_cross hspan d.1 d.2
  have heq : e ∈ faceEdges (normals B) q.1 := by
    change boundaryEdge (normals B) normal_cross hspan d.1 d.2 ∈
      faceEdges (normals B) q.1
    rw [hedge]
    exact boundaryEdge_mem (normals B) normal_cross hspan q.1 q.2
  by_cases hface : q.1 = d.1
  · left
    apply (indexedDartEquiv (normals B) normal_cross hspan).injective
    exact Sigma.subtype_ext hface hedge.symm
  · right
    have hqface := face_eq_edgeFace_of_mem (normals B) (normals_ne_zero B) q.1 e heq
    have hdface := face_eq_edgeFace_of_mem (normals B) (normals_ne_zero B) d.1 e hed
    have hsignNe : q.1.1 e.1.1 ≠ d.1.1 e.1.1 := by
      intro hs
      apply hface
      rw [hqface, hdface, hs]
    have hsignFlip : q.1.1 e.1.1 = !(d.1.1 e.1.1) := by
      cases hq : q.1.1 e.1.1 <;> cases hd : d.1.1 e.1.1
      · exact (hsignNe (hq.trans hd.symm)).elim
      · simp only [Bool.not_true]
      · simp only [Bool.not_false]
      · exact (hsignNe (hq.trans hd.symm)).elim
    have hqopp : q.1 = oppositeFace (normals B) (normals_ne_zero B) d.1 e := by
      rw [hqface, oppositeFace, hsignFlip]
    have hd'opp : d'.1 = oppositeFace (normals B) (normals_ne_zero B) d.1 e := by
      exact across_face_eq_edgeFace_flip (normals B) (normals_ne_zero B)
        normal_cross hspan d
    apply (indexedDartEquiv (normals B) normal_cross hspan).injective
    apply Sigma.subtype_ext (hqopp.trans hd'opp.symm)
    have hdedge := across_sameEdge (normals B) (normals_ne_zero B) normal_cross hspan d
    exact hedge.symm.trans hdedge

/-- The global endpoint pair depends only on the strict edge, not on the
incident face or its boundary index. -/
theorem orientedEdgeVertices_eq_of_sameEdge
    (d q : IndexedDart (normals B))
    (hedge : boundaryEdge (normals B) normal_cross hspan d.1 d.2 =
      boundaryEdge (normals B) normal_cross hspan q.1 q.2) :
    orientedEdgeVertices hspan d.1 d.2 = orientedEdgeVertices hspan q.1 q.2 := by
  rcases indexedDart_eq_or_across_of_sameEdge hspan d q hedge with h | h
  · rw [h]
  · rw [h]
    exact orientedEdgeVertices_across hspan d

end Erdos735.ConcretePolarOrientedVertex
