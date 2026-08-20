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

import ErdosProblems.Erdos735.OwnerPreservingEdgeRealization
import ErdosProblems.Erdos735.ProjectiveArrangement

/-!
# Boundary extraction for the concrete projective dual arrangement

This file instantiates the lifted cyclic skeleton on the finite projective intersections of a
finite affine point configuration. A noncollinear triple discharges every local chart, endpoint,
and multiplicity condition. The public constructor leaves only the exact edge-region cardinality
and face-region formulas of the one-dimensional deletion--restriction argument.
-/

open Classical
noncomputable section

open scoped LinearAlgebra.Projectivization

namespace Erdos735.ProjectiveBoundaryExtraction

open ChartOrder SignVector ProjectiveArrangement
open SignVector.LiftedCyclicEdgeRealization

abbrev Point := ProjectiveArrangement.Point

/-- Arrangement lines are the points of the original affine configuration. -/
abbrev Line (B : Finset Point) := {p // p ∈ B}

/-- Arrangement vertices are the projective intersections determined by pairs of lines. -/
abbrev Vertex (B : Finset Point) := {v // v ∈ projectiveVertices B}

/-- Incidence restricted to the finite line and vertex types. -/
def OnLine (B : Finset Point) (v : Vertex B) (p : Line B) : Prop :=
  Incident v.1 p.1

noncomputable instance (B : Finset Point) : DecidableRel (OnLine B) :=
  fun _ _ ↦ Classical.propDecidable _

/-- Concrete sign-vector normals indexed by the finite configuration. -/
def normals (B : Finset Point) : Line B → Vec3 :=
  fun p ↦ normalVec p.1

theorem normals_ne_zero (B : Finset Point) : ∀ p, normals B p ≠ 0 :=
  fun p ↦ normalVec_ne_zero p.1

/-- Two fixed distinct lines select one member of every antipodal strict-edge pair. -/
def otherLineChoiceOfPair {B : Finset Point} (a b : Line B) (hab : a ≠ b) :
    OtherLineChoice (Line B) := fun p ↦
  if hpa : p ≠ a then ⟨a, hpa.symm⟩
  else ⟨b, fun hbp ↦ hab ((not_ne_iff.mp hpa).symm.trans hbp.symm)⟩

/-- The first functional in a chosen chart avoiding every projective vertex. -/
noncomputable def chartF (B : Finset Point) : Module.Dual ℝ Vec3 :=
  Classical.choose (exists_chart_and_separating_coordinate B)

/-- The separating coordinate functional in the chosen chart. -/
noncomputable def chartG (B : Finset Point) : Module.Dual ℝ Vec3 :=
  Classical.choose (Classical.choose_spec (exists_chart_and_separating_coordinate B))

theorem chart_spec (B : Finset Point) :
    (∀ v ∈ projectiveVertices B, chartF B v.rep ≠ 0) ∧
      Set.InjOn (chartCoord (chartF B) (chartG B))
        (projectiveVertices B : Set (ℙ ℝ Vec3)) :=
  Classical.choose_spec (Classical.choose_spec (exists_chart_and_separating_coordinate B))

noncomputable def vertexCoord (B : Finset Point) : Vertex B → ℝ :=
  fun v ↦ chartCoord (chartF B) (chartG B) v.1

theorem vertexCoord_injective (B : Finset Point) :
    Set.InjOn (vertexCoord B) ((Finset.univ : Finset (Vertex B)) : Set (Vertex B)) := by
  intro v hv w hw hvw
  apply Subtype.ext
  exact (chart_spec B).2 v.2 w.2 hvw

/-- Passing from the ambient projective finset to its subtype preserves the set of vertices on a
fixed line. -/
theorem card_verticesOn_subtype (B : Finset Point) (p : Line B) :
    (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) p).card =
      (verticesOn (projectiveVertices B) Incident p.1).card := by
  classical
  apply Finset.card_bij (fun v _ ↦ v.1)
  · intro v hv
    have hv' := (mem_verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B)).mp hv
    exact (mem_verticesOn (projectiveVertices B) Incident).mpr ⟨v.2, hv'.2⟩
  · intro v hv w hw hvw
    exact Subtype.ext hvw
  · intro v hv
    have hv' := (mem_verticesOn (projectiveVertices B) Incident).mp hv
    let w : Vertex B := ⟨v, hv'.1⟩
    refine ⟨w, ?_, rfl⟩
    exact (mem_verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B)).mpr
      ⟨Finset.mem_univ w, hv'.2⟩

theorem two_vertices_on_every_line
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c) :
    ∀ p : Line B,
      2 ≤ (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) p).card := by
  intro p
  rw [card_verticesOn_subtype]
  exact two_le_verticesOn_card_of_noncollinear_config B ha hb hc hncol p.1 p.2

/-- Every projective vertex comes from a pair of distinct lines, hence has line multiplicity at
least two. -/
theorem two_le_lineMultiplicity (B : Finset Point) :
    ∀ v : Vertex B, 2 ≤ lineMultiplicity (OnLine B) v := by
  intro v
  have hv := v.2
  unfold projectiveVertices at hv
  obtain ⟨pq, hpq_univ, hpqv⟩ := Finset.mem_image.mp hv
  let p : Line B := pq.1.1
  let q : Line B := pq.1.2
  apply Finset.one_lt_card.mpr
  refine ⟨p, ?_, q, ?_, ?_⟩
  · simp only [lineMultiplicity, Finset.mem_filter, Finset.mem_univ, true_and]
    change Incident v.1 pq.1.1.1
    rw [← hpqv]
    exact indexedIntersection_incident_left B pq
  · simp only [lineMultiplicity, Finset.mem_filter, Finset.mem_univ, true_and]
    change Incident v.1 pq.1.2.1
    rw [← hpqv]
    exact indexedIntersection_incident_right B pq
  · simpa [p, q] using pq.2

/-- Besides any chosen incident supporting line, a projective arrangement
vertex lies on a second, distinct blue line. -/
theorem exists_other_incident_line (B : Finset Point) (v : Vertex B)
    (p : Line B) : ∃ q : Line B, q ≠ p ∧ OnLine B v q := by
  have hv := v.2
  unfold projectiveVertices at hv
  obtain ⟨pq, -, hpqv⟩ := Finset.mem_image.mp hv
  let q₀ : Line B := pq.1.1
  let q₁ : Line B := pq.1.2
  have hq₀ : OnLine B v q₀ := by
    change Incident v.1 pq.1.1.1
    rw [← hpqv]
    exact indexedIntersection_incident_left B pq
  have hq₁ : OnLine B v q₁ := by
    change Incident v.1 pq.1.2.1
    rw [← hpqv]
    exact indexedIntersection_incident_right B pq
  by_cases h : q₀ = p
  · exact ⟨q₁, fun h₁ ↦ pq.2 (h.trans h₁.symm), hq₁⟩
  · exact ⟨q₀, h, hq₀⟩

/-- Complete concrete boundary extraction from the two remaining region-count statements. -/
noncomputable def boundaryExtractionOfCardFormulas
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (edge_card :
      Fintype.card (ProjectiveStrictEdge
        (otherLineChoiceOfPair ⟨a, ha⟩ ⟨b, hb⟩ (by
          intro hab'
          apply hncol
          have hab : a = b := congrArg Subtype.val hab'
          subst b
          simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet])) (normals B)) =
        Fintype.card (CyclicSkeletonEdge (Finset.univ : Finset (Vertex B)) (OnLine B)))
    (face_degree : ∀ f : StrictFace (normals B), 3 ≤ (faceEdges (normals B) f).card)
    (face_card : (Fintype.card (StrictFace (normals B)) : ℤ) =
      2 + ∑ v : Vertex B, 2 * ((lineMultiplicity (OnLine B) v : ℤ) - 1)) :
    BoundaryExtraction (normals B) (normals_ne_zero B) := by
  let pick : OtherLineChoice (Line B) :=
    otherLineChoiceOfPair ⟨a, ha⟩ ⟨b, hb⟩ (by
      intro hab'
      apply hncol
      have hab : a = b := congrArg Subtype.val hab'
      subst b
      simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet])
  let edge : LiftedCyclicEdgeRealization (normals B) (OnLine B) :=
    LiftedCyclicEdgeRealization.ofProjectiveCardEq
      (n := normals B) (onLine := OnLine B) pick Finset.univ (vertexCoord B) rfl
      (vertexCoord_injective B) (two_vertices_on_every_line B ha hb hc hncol)
      edge_card (two_le_lineMultiplicity B)
  let full : LiftedBoundaryCardRealization (normals B) (OnLine B) :=
    LiftedBoundaryCardRealization.ofFaceCardFormula edge face_degree face_card
  exact full.toBoundaryExtraction

/-- The full lifted projective realization obtained by choosing the edge equivalence separately
in every supporting-line fiber.  Unlike the cardinality-only construction, its edge equivalence
remembers which projective line supports each strict sign edge. -/
noncomputable def boundaryCardRealizationOfRestrictedFaceCounts
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (restricted_count : ∀ p : Line B,
      restrictedFaceCount (otherNormals (normals B) p) (normals B p) =
        2 * (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) p).card)
    (face_degree : ∀ f : StrictFace (normals B), 3 ≤ (faceEdges (normals B) f).card)
    (face_card : (Fintype.card (StrictFace (normals B)) : ℤ) =
      2 + ∑ v : Vertex B, 2 * ((lineMultiplicity (OnLine B) v : ℤ) - 1)) :
    LiftedBoundaryCardRealization (normals B) (OnLine B) := by
  let hab : (⟨a, ha⟩ : Line B) ≠ ⟨b, hb⟩ := by
    intro hab'
    apply hncol
    have hab : a = b := congrArg Subtype.val hab'
    subst b
    simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]
  let pick : OtherLineChoice (Line B) :=
    otherLineChoiceOfPair ⟨a, ha⟩ ⟨b, hb⟩ hab
  let edge : LiftedCyclicEdgeRealization (normals B) (OnLine B) :=
    LiftedCyclicEdgeRealization.ofRestrictedFaceCountsOwnerPreserving
      (n := normals B) (onLine := OnLine B) pick Finset.univ (vertexCoord B) rfl
      (vertexCoord_injective B) (two_vertices_on_every_line B ha hb hc hncol)
      restricted_count (two_le_lineMultiplicity B)
  exact LiftedBoundaryCardRealization.ofFaceCardFormula edge face_degree face_card

/-- A more geometric form of `boundaryExtractionOfCardFormulas`: the edge cardinality is
discharged by the standard one-dimensional statement saying that the restriction to each line has
twice as many strict regions as projective intersection vertices.  The construction is fiberwise,
so it additionally preserves every strict edge's supporting line. -/
noncomputable def boundaryExtractionOfRestrictedFaceCounts
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (restricted_count : ∀ p : Line B,
      restrictedFaceCount (otherNormals (normals B) p) (normals B p) =
        2 * (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) p).card)
    (face_degree : ∀ f : StrictFace (normals B), 3 ≤ (faceEdges (normals B) f).card)
    (face_card : (Fintype.card (StrictFace (normals B)) : ℤ) =
      2 + ∑ v : Vertex B, 2 * ((lineMultiplicity (OnLine B) v : ℤ) - 1)) :
    BoundaryExtraction (normals B) (normals_ne_zero B) :=
  (boundaryCardRealizationOfRestrictedFaceCounts B ha hb hc hncol
    restricted_count face_degree face_card).toBoundaryExtraction

/-- Every endpoint assigned by the owner-preserving realization is incident with the concrete
projective line named by the strict edge support. -/
theorem boundaryCardRealization_edgeEndpoint_incident_support
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (restricted_count : ∀ p : Line B,
      restrictedFaceCount (otherNormals (normals B) p) (normals B p) =
        2 * (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) p).card)
    (face_degree : ∀ f : StrictFace (normals B), 3 ≤ (faceEdges (normals B) f).card)
    (face_card : (Fintype.card (StrictFace (normals B)) : ℤ) =
      2 + ∑ v : Vertex B, 2 * ((lineMultiplicity (OnLine B) v : ℤ) - 1))
    (e : StrictEdge (normals B)) (v : Vertex B × Bool)
    (hv : v ∈
      (boundaryCardRealizationOfRestrictedFaceCounts B ha hb hc hncol
        restricted_count face_degree face_card).toLiftedCyclicEdgeRealization.edgeVertices e) :
    Incident v.1.1 e.1.1.1 := by
  let hab : (⟨a, ha⟩ : Line B) ≠ ⟨b, hb⟩ := by
    intro hab'
    apply hncol
    have hab : a = b := congrArg Subtype.val hab'
    subst b
    simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet]
  let pick : OtherLineChoice (Line B) :=
    otherLineChoiceOfPair ⟨a, ha⟩ ⟨b, hb⟩ hab
  have h := LiftedCyclicEdgeRealization.edgeVertex_on_support
    (n := normals B) (onLine := OnLine B) pick Finset.univ (vertexCoord B) rfl
    (vertexCoord_injective B) (two_vertices_on_every_line B ha hb hc hncol)
    restricted_count (two_le_lineMultiplicity B) e v
  apply h
  simpa only [boundaryCardRealizationOfRestrictedFaceCounts,
    LiftedBoundaryCardRealization.ofFaceCardFormula] using hv

end Erdos735.ProjectiveBoundaryExtraction
