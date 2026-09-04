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

import ErdosProblems.Erdos735.LiftedCyclicSkeleton
import ErdosProblems.Erdos735.SignVectorIncidence
import ErdosProblems.Erdos735.SignVectorProjectiveEdges

/-!
# Lifted cyclic skeletons as sign-vector boundary extractions

This file packages the spherical double cover of a projective cyclic line skeleton. Once strict
sign-vector edges are identified with lifted projective intervals, all endpoint and vertex-degree
fields of `BoundaryExtraction` follow. Face lists require no extra ordering data: the extraction
interface only asks for a nodup list with the prescribed finset, so `Finset.toList` is canonical.
-/

open Classical
noncomputable section

namespace Erdos735.SignVector

open ChartOrder

universe u v

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {V : Type v} [Fintype V] [DecidableEq V]

/-- Cardinality of the line-labelled projective cyclic skeleton. The explicit instance comparison
is needed because `CyclicSkeletonEdge` intentionally uses `Fintype.ofFinite`. -/
theorem card_cyclicSkeletonEdge_eq_sum
    (vertices : Finset V) (onLine : V → I → Prop) [DecidableRel onLine] :
    Fintype.card (CyclicSkeletonEdge vertices onLine) =
      ∑ i : I, (verticesOn vertices onLine i).card := by
  let oldInst : Fintype (CyclicSkeletonEdge vertices onLine) :=
    cyclicSkeletonEdgeFintype vertices onLine
  let sigmaInst : Fintype (Σ i : I, {v // v ∈ verticesOn vertices onLine i}) :=
    Sigma.instFintype
  have hchange : @Fintype.card _ oldInst = @Fintype.card _ sigmaInst :=
    @Fintype.card_congr _ _ oldInst sigmaInst (Equiv.refl _)
  have hsigma : @Fintype.card _ sigmaInst =
      ∑ i : I, (verticesOn vertices onLine i).card := by
    simpa only [sigmaInst, Fintype.card_coe] using
      (@Fintype.card_sigma I (fun i ↦ {v // v ∈ verticesOn vertices onLine i})
        inferInstance (fun _ ↦ inferInstance))
  simpa only [oldInst] using hchange.trans hsigma

/-- The one-dimensional restriction count on every line implies that projective strict sign edges
and projective cyclic intervals have the same finite cardinality. -/
theorem card_projectiveStrictEdge_eq_cyclic_of_restrictedFaceCount
    (pick : OtherLineChoice I) (n : I → Vec3)
    (vertices : Finset V) (onLine : V → I → Prop) [DecidableRel onLine]
    (hrestricted : ∀ i,
      restrictedFaceCount (otherNormals n i) (n i) =
        2 * (verticesOn vertices onLine i).card) :
    Fintype.card (ProjectiveStrictEdge pick n) =
      Fintype.card (CyclicSkeletonEdge vertices onLine) := by
  have hstrict := card_strictEdge n
  have hpair := card_strictEdge_eq_two_mul_projective pick n
  have hcyclic := card_cyclicSkeletonEdge_eq_sum vertices onLine
  have hsum :
      (∑ i : I, restrictedFaceCount (otherNormals n i) (n i)) =
        2 * ∑ i : I, (verticesOn vertices onLine i).card := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hrestricted i
  omega

/-- The antipodal edge pairing followed by a projective cyclic-interval equivalence gives the
required equivalence with the spherical double cover. -/
noncomputable def strictEdgeEquivLiftedCyclic
    (pick : OtherLineChoice I) (n : I → Vec3)
    {vertices : Finset V} {onLine : V → I → Prop} [DecidableRel onLine]
    (baseEquiv : ProjectiveStrictEdge pick n ≃ CyclicSkeletonEdge vertices onLine) :
    StrictEdge n ≃ LiftedCyclicSkeletonEdge vertices onLine :=
  (strictEdgeEquivProjectiveTimesBool pick n).trans
    (Equiv.prodCongr baseEquiv (Equiv.refl Bool))

/-- A geometric realization of every spherical strict edge as one of the two lifts of a cyclic
projective interval. The Boolean transition allows the chosen projective chart to reverse sheet at
a wrap edge. -/
structure LiftedCyclicEdgeRealization
    (n : I → Vec3) (onLine : V → I → Prop) [DecidableRel onLine] where
  vertices : Finset V
  coord : V → ℝ
  all_vertices : vertices = Finset.univ
  coord_injective : Set.InjOn coord (vertices : Set V)
  two_vertices_on_line : ∀ i, 2 ≤ (verticesOn vertices onLine i).card
  transition : CyclicSkeletonEdge vertices onLine → Bool
  edgeEquiv : StrictEdge n ≃ LiftedCyclicSkeletonEdge vertices onLine
  multiplicity_two_le : ∀ v, 2 ≤ lineMultiplicity onLine v

namespace LiftedCyclicEdgeRealization

variable {n : I → Vec3} {onLine : V → I → Prop} [DecidableRel onLine]
variable (X : LiftedCyclicEdgeRealization n onLine)

/-- Build the lifted edge realization from the one remaining one-dimensional geometric bridge:
projective feasible sign intervals are the cyclic successor intervals on their projective lines.
The constant-false transition is sufficient for all endpoint and degree counts. -/
noncomputable def ofProjective
    (pick : OtherLineChoice I)
    (vertices : Finset V) (coord : V → ℝ)
    (all_vertices : vertices = Finset.univ)
    (coord_injective : Set.InjOn coord (vertices : Set V))
    (two_vertices_on_line : ∀ i, 2 ≤ (verticesOn vertices onLine i).card)
    (baseEquiv : ProjectiveStrictEdge pick n ≃ CyclicSkeletonEdge vertices onLine)
    (multiplicity_two_le : ∀ v, 2 ≤ lineMultiplicity onLine v) :
    LiftedCyclicEdgeRealization n onLine where
  vertices := vertices
  coord := coord
  all_vertices := all_vertices
  coord_injective := coord_injective
  two_vertices_on_line := two_vertices_on_line
  transition := fun _ ↦ false
  edgeEquiv := strictEdgeEquivLiftedCyclic pick n baseEquiv
  multiplicity_two_le := multiplicity_two_le

/-- For the endpoint and degree data used by `BoundaryExtraction`, only the finite cardinality of
the projective edge type is needed: an equivalence is obtained canonically from equal cards. -/
noncomputable def ofProjectiveCardEq
    (pick : OtherLineChoice I)
    (vertices : Finset V) (coord : V → ℝ)
    (all_vertices : vertices = Finset.univ)
    (coord_injective : Set.InjOn coord (vertices : Set V))
    (two_vertices_on_line : ∀ i, 2 ≤ (verticesOn vertices onLine i).card)
    (projectiveEdge_card :
      Fintype.card (ProjectiveStrictEdge pick n) =
        Fintype.card (CyclicSkeletonEdge vertices onLine))
    (multiplicity_two_le : ∀ v, 2 ≤ lineMultiplicity onLine v) :
    LiftedCyclicEdgeRealization n onLine :=
  ofProjective pick vertices coord all_vertices coord_injective two_vertices_on_line
    (Fintype.equivOfCardEq projectiveEdge_card) multiplicity_two_le

/-- The lifted projective endpoints assigned to a strict sign-vector edge. -/
def edgeVertices (e : StrictEdge n) : Finset (V × Bool) :=
  liftedCyclicEdgeVertices X.vertices onLine X.coord X.transition (X.edgeEquiv e)

/-- The strict edges assigned to a lifted projective vertex. -/
def vertexEdges (v : V × Bool) : Finset (StrictEdge n) :=
  Finset.univ.filter fun e ↦ v ∈ X.edgeVertices e

theorem vertexEdge_iff (v : V × Bool) (e : StrictEdge n) :
    e ∈ X.vertexEdges v ↔ v ∈ X.edgeVertices e := by
  simp [vertexEdges]

theorem edgeVertices_card (e : StrictEdge n) :
    (X.edgeVertices e).card = 2 := by
  exact liftedCyclicEdgeVertices_card X.vertices onLine X.coord X.coord_injective
    X.two_vertices_on_line X.transition (X.edgeEquiv e)

theorem vertexEdges_card_eq_lifted (v : V × Bool) :
    (X.vertexEdges v).card =
      (liftedCyclicVertexEdges X.vertices onLine X.coord X.transition v).card := by
  apply Finset.card_bij (fun e _ ↦ X.edgeEquiv e)
  · intro e he
    rw [mem_liftedCyclicVertexEdges_iff]
    exact (X.vertexEdge_iff v e).mp he
  · intro e he f hf hef
    exact X.edgeEquiv.injective hef
  · intro e he
    refine ⟨X.edgeEquiv.symm e, ?_, X.edgeEquiv.apply_symm_apply e⟩
    apply (X.vertexEdge_iff v (X.edgeEquiv.symm e)).mpr
    change v ∈ liftedCyclicEdgeVertices X.vertices onLine X.coord X.transition
      (X.edgeEquiv (X.edgeEquiv.symm e))
    rw [X.edgeEquiv.apply_symm_apply]
    exact (mem_liftedCyclicVertexEdges_iff
      X.vertices onLine X.coord X.transition v e).mp he

theorem vertexEdges_card (v : V × Bool) :
    (X.vertexEdges v).card = 2 * lineMultiplicity onLine v.1 := by
  rw [X.vertexEdges_card_eq_lifted v]
  apply liftedCyclicVertexEdges_card X.vertices onLine X.coord X.coord_injective
    X.two_vertices_on_line X.transition v
  rw [X.all_vertices]
  exact Finset.mem_univ v.1

/-- The number of projective cyclic intervals is the sum of the numbers of vertices on all
projective lines. -/
theorem card_cyclicSkeletonEdge :
    Fintype.card (CyclicSkeletonEdge X.vertices onLine) =
      ∑ i : I, (verticesOn X.vertices onLine i).card := by
  exact card_cyclicSkeletonEdge_eq_sum X.vertices onLine

/-- Double-counting projective vertex--line incidences. -/
theorem sum_verticesOn_card_eq_sum_lineMultiplicity :
    (∑ i : I, (verticesOn X.vertices onLine i).card) =
      ∑ v : V, lineMultiplicity onLine v := by
  classical
  simp only [verticesOn, lineMultiplicity, Finset.card_filter]
  rw [← X.all_vertices]
  exact Finset.sum_comm

/-- The lifted interval equivalence fixes the exact spherical edge count. -/
theorem card_strictEdge_eq_two_mul_sum_multiplicity
    (X : LiftedCyclicEdgeRealization n onLine) :
    Fintype.card (StrictEdge n) =
      2 * ∑ v : V, lineMultiplicity onLine v := by
  rw [Fintype.card_congr X.edgeEquiv, Fintype.card_prod, Fintype.card_bool,
    X.card_cyclicSkeletonEdge, X.sum_verticesOn_card_eq_sum_lineMultiplicity]
  omega

/-- Once deletion--restriction supplies the standard face-count formula, Euler's identity follows
purely from the lifted cyclic edge count and incidence double-counting. -/
theorem euler_sphere_of_face_card_formula
    (X : LiftedCyclicEdgeRealization n onLine)
    (hface : (Fintype.card (StrictFace n) : ℤ) =
      2 + ∑ v : V, 2 * ((lineMultiplicity onLine v : ℤ) - 1)) :
    (Fintype.card (V × Bool) : ℤ) - (Fintype.card (StrictEdge n) : ℤ) +
      (Fintype.card (StrictFace n) : ℤ) = 2 := by
  rw [hface, X.card_strictEdge_eq_two_mul_sum_multiplicity,
    Fintype.card_prod, Fintype.card_bool]
  push_cast
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Int.nsmul_eq_mul]
  rw [← Finset.mul_sum]
  abel

/-- The final three numerical/geometric facts which, together with a lifted cyclic edge
realization, imply the complete boundary extraction. -/
structure LiftedBoundaryCardRealization
    (n : I → Vec3) (onLine : V → I → Prop) [DecidableRel onLine]
    extends LiftedCyclicEdgeRealization n onLine where
  faceEdges_card_three_le : ∀ f, 3 ≤ (faceEdges n f).card
  euler_sphere :
    (Fintype.card (V × Bool) : ℤ) - (Fintype.card (StrictEdge n) : ℤ) +
      (Fintype.card (StrictFace n) : ℤ) = 2

namespace LiftedBoundaryCardRealization

variable {hn : ∀ i, n i ≠ 0}
variable (X : LiftedBoundaryCardRealization n onLine)

/-- Build the last certificate from the lifted one-skeleton, degree at least three for each strict
face, and the deletion--restriction face-count formula. Euler is then a theorem, not an extra
geometric assumption. -/
noncomputable def ofFaceCardFormula
    (edge : LiftedCyclicEdgeRealization n onLine)
    (faceEdges_card_three_le : ∀ f, 3 ≤ (faceEdges n f).card)
    (face_card_formula : (Fintype.card (StrictFace n) : ℤ) =
      2 + ∑ v : V, 2 * ((lineMultiplicity onLine v : ℤ) - 1)) :
    LiftedBoundaryCardRealization n onLine where
  toLiftedCyclicEdgeRealization := edge
  faceEdges_card_three_le := faceEdges_card_three_le
  euler_sphere := edge.euler_sphere_of_face_card_formula face_card_formula

/-- A lifted cyclic edge realization plus the exact face-degree and Euler counts supplies every
field of `BoundaryExtraction`. -/
def toBoundaryExtraction : BoundaryExtraction n hn where
  Vertex := V × Bool
  instFintypeVertex := inferInstance
  instDecidableEqVertex := inferInstance
  blueMultiplicity := fun v ↦ lineMultiplicity onLine v.1
  edgeVertices := X.toLiftedCyclicEdgeRealization.edgeVertices
  vertexEdges := X.toLiftedCyclicEdgeRealization.vertexEdges
  vertexEdge_iff := X.toLiftedCyclicEdgeRealization.vertexEdge_iff
  edgeVertices_card := X.toLiftedCyclicEdgeRealization.edgeVertices_card
  vertexEdges_card := X.toLiftedCyclicEdgeRealization.vertexEdges_card
  blueMultiplicity_two_le := fun v ↦ X.multiplicity_two_le v.1
  faceBoundary := fun f ↦ (faceEdges n f).toList
  faceBoundary_nodup := fun f ↦ (faceEdges n f).nodup_toList
  faceBoundary_toFinset := fun f ↦ by simp
  faceDegree_three_le := fun f ↦ by
    simpa using X.faceEdges_card_three_le f
  euler_sphere := X.euler_sphere

/-- The resulting sign-vector cellulation. -/
def toBlueCellulation :
    BlueCellulation (V × Bool) (StrictEdge n) (StrictFace n) :=
  (X.toBoundaryExtraction (hn := hn)).toBlueCellulation n hn

end LiftedBoundaryCardRealization
end LiftedCyclicEdgeRealization
end Erdos735.SignVector
