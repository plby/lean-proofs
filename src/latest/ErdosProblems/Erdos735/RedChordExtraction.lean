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

import ErdosProblems.Erdos735.SignVectorRotation
import ErdosProblems.Erdos735.ProjectiveArrangement

/-!
# Red chords of strict blue faces

This file extracts the red diagonals in a blue sign chamber from projective
incidence data.  The geometric input records that a feasible red line has
exactly two boundary vertices, that boundary edges lie on their support
lines, and that two distinct red lines do not share a blue vertex.  From
these facts it proves endpoint disjointness and nonadjacency of every red
chord.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace Erdos735.RedChordExtraction

open ProjectiveArrangement SignVector
open SignVector.RotationRealization

abbrev Point := ProjectiveArrangement.Point
abbrev BlueLine (B : Finset Point) := {p // p ∈ B}
abbrev RedLine (A : Finset Point) := {p // p ∈ A}
abbrev BlueVertex (B : Finset Point) := {v // v ∈ projectiveVertices B}

def blueNormals (B : Finset Point) : BlueLine B → Vec3 :=
  fun p ↦ normalVec p.1

theorem blueNormals_ne_zero (B : Finset Point) : ∀ p, blueNormals B p ≠ 0 :=
  fun p ↦ normalVec_ne_zero p.1

/-- A red line cuts the interior of the strict blue face. -/
def RedChordFeasible {A B : Finset Point}
    (f : StrictFace (blueNormals B)) (a : RedLine A) : Prop :=
  RestrictedRealizable (blueNormals B) (normalVec a.1) f.1

noncomputable def redChordLines {A B : Finset Point}
    (f : StrictFace (blueNormals B)) : Finset (RedLine A) :=
  Finset.univ.filter (RedChordFeasible f)

theorem mem_redChordLines_iff {A B : Finset Point}
    (f : StrictFace (blueNormals B)) (a : RedLine A) :
    a ∈ redChordLines f ↔ RedChordFeasible f a := by
  simp [redChordLines]

variable {A B : Finset Point}
variable {G : SimpleGraph (BlueVertex B)} [DecidableRel G.Adj] [Fintype G.edgeSet]
variable (X : RotationRealization (G := G) (blueNormals B) (blueNormals_ne_zero B))

/-- Boundary indices at which the red projective line meets the blue face. -/
noncomputable def redEndpointIndices
    (f : StrictFace (blueNormals B)) (a : RedLine A) :
    Finset (Fin (X.strictC.faceDegree f)) :=
  Finset.univ.filter fun i ↦ Incident (X.boundaryVertex f i).1 a.1

theorem mem_redEndpointIndices_iff
    (f : StrictFace (blueNormals B)) (a : RedLine A)
    (i : Fin (X.strictC.faceDegree f)) :
    i ∈ redEndpointIndices X f a ↔
      Incident (X.boundaryVertex f i).1 a.1 := by
  simp [redEndpointIndices]

/-- The concrete geometric facts required to extract red chords from a
rotation realization. -/
structure Geometry where
  endpoint_card : ∀ (f : StrictFace (blueNormals B)) (a : RedLine A),
    a ∈ redChordLines (A := A) f →
    (redEndpointIndices (A := A) X f a).card = 2
  boundary_start_on_owner : ∀ (f : StrictFace (blueNormals B))
      (i : Fin (X.strictC.faceDegree f)),
    Incident (X.boundaryVertex f i).1
      (strictEdgeOwner (X.boundaryEdge f i)).1
  boundary_finish_on_owner : ∀ (f : StrictFace (blueNormals B))
      (i : Fin (X.strictC.faceDegree f)),
    Incident (X.boundaryVertex f (X.strictFaceSucc f i)).1
      (strictEdgeOwner (X.boundaryEdge f i)).1
  no_two_red_at_blueVertex : ∀ (a b : RedLine A), a ≠ b → ∀ v : BlueVertex B,
    ¬ (Incident v.1 a.1 ∧ Incident v.1 b.1)

namespace Geometry

variable (H : Geometry (A := A) (B := B) X)

abbrev ChordLine (f : StrictFace (blueNormals B)) :=
  {a : RedLine A // a ∈ redChordLines (A := A) f}

noncomputable def chordPair (f : StrictFace (blueNormals B))
    (a : ChordLine (A := A) (B := B) f) :
    Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f) :=
  let h := Finset.card_eq_two.mp (H.endpoint_card f a.1 a.2)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

theorem chordPair_spec (f : StrictFace (blueNormals B))
    (a : ChordLine (A := A) (B := B) f) :
    (chordPair (A := A) (B := B) X H f a).1 ≠
      (chordPair (A := A) (B := B) X H f a).2 ∧
      redEndpointIndices (A := A) X f a.1 =
        {(chordPair (A := A) (B := B) X H f a).1,
          (chordPair (A := A) (B := B) X H f a).2} := by
  unfold chordPair
  dsimp only
  exact Classical.choose_spec (Classical.choose_spec
    (Finset.card_eq_two.mp (H.endpoint_card f a.1 a.2)))

include H in
theorem redEndpointIndices_disjoint (f : StrictFace (blueNormals B))
    {a b : ChordLine (A := A) (B := B) f} (hab : a ≠ b) :
    Disjoint (redEndpointIndices (A := A) X f a.1)
      (redEndpointIndices (A := A) X f b.1) := by
  rw [Finset.disjoint_left]
  intro i hia hib
  have hline : a.1 ≠ b.1 := by
    intro h
    exact hab (Subtype.ext h)
  exact (H.no_two_red_at_blueVertex a.1 b.1 hline (X.boundaryVertex f i))
    ⟨(mem_redEndpointIndices_iff (A := A) (B := B) X f a.1 i).mp hia,
      (mem_redEndpointIndices_iff (A := A) (B := B) X f b.1 i).mp hib⟩

theorem chordPair_endpoints_disjoint (f : StrictFace (blueNormals B))
    {a b : ChordLine (A := A) (B := B) f} (hab : a ≠ b) :
    Disjoint ({(chordPair (A := A) (B := B) X H f a).1,
        (chordPair (A := A) (B := B) X H f a).2} :
          Finset (Fin (X.strictC.faceDegree f)))
      {(chordPair (A := A) (B := B) X H f b).1,
        (chordPair (A := A) (B := B) X H f b).2} := by
  rw [← (chordPair_spec (A := A) (B := B) X H f a).2,
    ← (chordPair_spec (A := A) (B := B) X H f b).2]
  exact redEndpointIndices_disjoint (A := A) (B := B) X H f hab

theorem chordLine_injective (f : StrictFace (blueNormals B)) :
    Function.Injective (chordPair (A := A) (B := B) X H f) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  have hpaira := chordPair_spec (A := A) (B := B) X H f a
  have hpairb := chordPair_spec (A := A) (B := B) X H f b
  have hai : (chordPair (A := A) (B := B) X H f a).1 ∈
      redEndpointIndices X f a.1 := by
    rw [hpaira.2]
    simp
  have hbi : (chordPair (A := A) (B := B) X H f b).1 ∈
      redEndpointIndices X f b.1 := by
    rw [hpairb.2]
    simp
  have hfirst := congrArg Prod.fst hab
  have hinca := (mem_redEndpointIndices_iff (A := A) (B := B) X f a.1 _).mp hai
  have hincb := (mem_redEndpointIndices_iff (A := A) (B := B) X f b.1 _).mp hbi
  apply H.no_two_red_at_blueVertex a.1 b.1 hne
    (X.boundaryVertex f (chordPair (A := A) (B := B) X H f a).1)
  exact ⟨hinca, hfirst ▸ hincb⟩

noncomputable def redChords (f : StrictFace (blueNormals B)) :
    Finset (Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f)) :=
  Finset.univ.image (chordPair (A := A) (B := B) X H f)

theorem mem_redChords_iff (f : StrictFace (blueNormals B))
    (p : Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f)) :
    p ∈ redChords (A := A) (B := B) X H f ↔
      ∃ a : ChordLine (A := A) (B := B) f,
        chordPair (A := A) (B := B) X H f a = p := by
  simp [redChords]

theorem redChord_distinct (f : StrictFace (blueNormals B))
    (p : Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f))
    (hp : p ∈ redChords (A := A) (B := B) X H f) : p.1 ≠ p.2 := by
  obtain ⟨a, rfl⟩ := (mem_redChords_iff (A := A) (B := B) X H f p).mp hp
  exact (chordPair_spec (A := A) (B := B) X H f a).1

/-- The two boundary vertices used by a red chord. -/
def chordEndpoints {f : StrictFace (blueNormals B)}
    (p : Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f)) :
    Finset (Fin (X.strictC.faceDegree f)) :=
  {p.1, p.2}

@[simp] theorem mem_chordEndpoints {f : StrictFace (blueNormals B)}
    {p : Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f)}
    {i : Fin (X.strictC.faceDegree f)} :
    i ∈ chordEndpoints X p ↔ i = p.1 ∨ i = p.2 := by
  simp [chordEndpoints]

theorem chordEndpoints_card (f : StrictFace (blueNormals B))
    (p : Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f))
    (hp : p ∈ redChords (A := A) (B := B) X H f) :
    (chordEndpoints X p).card = 2 := by
  exact Finset.card_pair (redChord_distinct (A := A) (B := B) X H f p hp)

theorem chordEndpoints_disjoint (f : StrictFace (blueNormals B))
    {p q : Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f)}
    (hp : p ∈ redChords (A := A) (B := B) X H f)
    (hq : q ∈ redChords (A := A) (B := B) X H f) (hpq : p ≠ q) :
    Disjoint (chordEndpoints X p) (chordEndpoints X q) := by
  obtain ⟨a, rfl⟩ := (mem_redChords_iff (A := A) (B := B) X H f p).mp hp
  obtain ⟨b, rfl⟩ := (mem_redChords_iff (A := A) (B := B) X H f q).mp hq
  apply chordPair_endpoints_disjoint (A := A) (B := B) X H f
  intro hab
  exact hpq (congrArg (chordPair (A := A) (B := B) X H f) hab)

/-- All blue boundary vertices that are endpoints of red chords in `f`. -/
noncomputable def redEndpoints (f : StrictFace (blueNormals B)) :
    Finset (Fin (X.strictC.faceDegree f)) :=
  (redChords (A := A) (B := B) X H f).biUnion (chordEndpoints X)

theorem mem_redEndpoints_iff (f : StrictFace (blueNormals B))
    (i : Fin (X.strictC.faceDegree f)) :
    i ∈ redEndpoints (A := A) (B := B) X H f ↔
      ∃ p ∈ redChords (A := A) (B := B) X H f, i = p.1 ∨ i = p.2 := by
  simp [redEndpoints]

theorem redEndpoints_card (f : StrictFace (blueNormals B)) :
    (redEndpoints (A := A) (B := B) X H f).card =
      2 * (redChords (A := A) (B := B) X H f).card := by
  rw [redEndpoints, Finset.card_biUnion]
  · have hsum :
        (∑ p ∈ redChords (A := A) (B := B) X H f,
          (chordEndpoints X p).card) =
          ∑ _p ∈ redChords (A := A) (B := B) X H f, 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact chordEndpoints_card (A := A) (B := B) X H f p hp
    rw [hsum]
    simp [Nat.mul_comm]
  · intro p hp q hq hpq
    exact chordEndpoints_disjoint (A := A) (B := B) X H f hp hq hpq

include H in
theorem not_red_incident_to_boundary_edge (hdisjoint : Disjoint A B)
    (f : StrictFace (blueNormals B)) (a : RedLine A)
    (i : Fin (X.strictC.faceDegree f))
    (hi : i ≠ X.strictFaceSucc f i)
    (hstart : Incident (X.boundaryVertex f i).1 a.1)
    (hfinish : Incident (X.boundaryVertex f (X.strictFaceSucc f i)).1 a.1) : False := by
  let b := strictEdgeOwner (X.boundaryEdge f i)
  have hab : a.1 ≠ b.1 := by
    intro heq
    have haB : a.1 ∈ B := by rw [heq]; exact b.2
    exact (Finset.disjoint_left.mp hdisjoint) a.2 haB
  have hblueStart := H.boundary_start_on_owner f i
  have hblueFinish := H.boundary_finish_on_owner f i
  have hv0 : (X.boundaryVertex f i).1 =
      (X.boundaryVertex f (X.strictFaceSucc f i)).1 :=
    ProjectiveArrangement.eq_of_two_common_lines hab
      hstart hblueStart hfinish hblueFinish
  have hv : X.boundaryVertex f i =
      X.boundaryVertex f (X.strictFaceSucc f i) := Subtype.ext hv0
  exact hi (X.boundaryVertex_injective f hv)

theorem redChord_nonadjacent (hdisjoint : Disjoint A B)
    (f : StrictFace (blueNormals B))
    (p : Fin (X.strictC.faceDegree f) × Fin (X.strictC.faceDegree f))
    (hp : p ∈ redChords (A := A) (B := B) X H f) :
    p.2 ≠ X.strictFaceSucc f p.1 ∧ p.1 ≠ X.strictFaceSucc f p.2 := by
  obtain ⟨a, rfl⟩ :=
    (mem_redChords_iff (A := A) (B := B) X H f p).mp hp
  have hspec := chordPair_spec (A := A) (B := B) X H f a
  have hinc1 : Incident
      (X.boundaryVertex f (chordPair (A := A) (B := B) X H f a).1).1 a.1.1 :=
    (mem_redEndpointIndices_iff (A := A) (B := B) X f a.1 _).mp
      (by rw [hspec.2]; simp)
  have hinc2 : Incident
      (X.boundaryVertex f (chordPair (A := A) (B := B) X H f a).2).1 a.1.1 :=
    (mem_redEndpointIndices_iff (A := A) (B := B) X f a.1 _).mp
      (by rw [hspec.2]; simp)
  constructor
  · intro hadj
    apply not_red_incident_to_boundary_edge (A := A) (B := B) X H hdisjoint f
      a.1 (chordPair (A := A) (B := B) X H f a).1
    · intro hi
      exact hspec.1 (hi.trans hadj.symm)
    · exact hinc1
    · exact hadj ▸ hinc2
  · intro hadj
    apply not_red_incident_to_boundary_edge (A := A) (B := B) X H hdisjoint f
      a.1 (chordPair (A := A) (B := B) X H f a).2
    · intro hj
      exact hspec.1 (hadj.trans hj.symm)
    · exact hinc2
    · exact hadj ▸ hinc1

end Geometry
end Erdos735.RedChordExtraction
