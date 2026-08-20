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

import ErdosProblems.Erdos735.RedChordExtraction
import ErdosProblems.Erdos735.RedChordPolarBoundaryIndices
import ErdosProblems.Erdos735.ConcretePolarOrientedVertex
import ErdosProblems.Erdos735.RedChordIncidence

/-!
# Red chords on the literal polar boundary

This is the red-chord extraction specialized directly to the genuine polar
boundary cycle.  It avoids any cardinality-chosen edge equivalence: endpoint
indices are the concrete cyclic polar corners, and every incidence assertion
is projectively literal.
-/

open Classical
noncomputable section

namespace Erdos735.PolarRedChordExtraction

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector
open SignVector.PolarBoundaryAcross
open RedChordExtraction RedChordPolarBoundaryIndices
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point
abbrev BlueLine (P : Finset Point) := {b // b ∈ nonordinaryPoints P}
abbrev RedLine (P : Finset Point) := {a // a ∈ ordinaryPoints P}

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable [Nonempty (BlueLine P)]
variable (hspan : Submodule.span ℝ
  (Set.range (normals (nonordinaryPoints P))) = ⊤)

abbrev ChordLine (f : StrictFace (normals (nonordinaryPoints P))) :=
  {a : RedLine P // RedChordFeasible f a}

noncomputable def endpointIndices
    (f : StrictFace (normals (nonordinaryPoints P))) (a : RedLine P) :
    Finset (BoundaryIndex (normals (nonordinaryPoints P)) f) :=
  faceRedEndpointIndices f hspan a.1

include hred in
theorem endpointIndices_card
    (f : StrictFace (normals (nonordinaryPoints P)))
    (a : ChordLine f) : (endpointIndices hspan f a.1).card = 2 := by
  exact faceRedEndpointIndices_card_of_restricted
    hred a.1.2 f hspan a.2

noncomputable def chordPair
    (f : StrictFace (normals (nonordinaryPoints P))) (a : ChordLine f) :
    BoundaryIndex (normals (nonordinaryPoints P)) f ×
      BoundaryIndex (normals (nonordinaryPoints P)) f :=
  let h := Finset.card_eq_two.mp (endpointIndices_card hred hspan f a)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

theorem chordPair_spec
    (f : StrictFace (normals (nonordinaryPoints P))) (a : ChordLine f) :
    (chordPair hred hspan f a).1 ≠ (chordPair hred hspan f a).2 ∧
      endpointIndices hspan f a.1 =
        {(chordPair hred hspan f a).1, (chordPair hred hspan f a).2} := by
  unfold chordPair
  dsimp only
  exact Classical.choose_spec (Classical.choose_spec
    (Finset.card_eq_two.mp (endpointIndices_card hred hspan f a)))

include hred in
theorem endpointIndices_disjoint
    (f : StrictFace (normals (nonordinaryPoints P)))
    {a b : ChordLine f} (hab : a ≠ b) :
    Disjoint (endpointIndices hspan f a.1) (endpointIndices hspan f b.1) := by
  rw [Finset.disjoint_left]
  intro i hai hbi
  have haInc : Incident
      (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i) a.1.1 :=
    (Finset.mem_filter.mp hai).2
  have hbInc : Incident
      (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i) b.1.1 :=
    (Finset.mem_filter.mp hbi).2
  let v : ProjectiveBoundaryExtraction.Vertex (nonordinaryPoints P) :=
    ⟨boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i,
      boundaryVertex_mem_projectiveVertices hspan f i⟩
  exact RedChordIncidence.no_common_blueVertex_of_distinct_red hred
    a.1.2 b.1.2 (fun h ↦ hab (Subtype.ext (Subtype.ext h))) v haInc hbInc

theorem chordLine_injective
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Function.Injective (chordPair hred hspan f) := by
  intro a b hp
  by_contra hab
  have hdisj := endpointIndices_disjoint hred hspan f hab
  have ha := chordPair_spec hred hspan f a
  have hmem : (chordPair hred hspan f a).1 ∈ endpointIndices hspan f a.1 := by
    rw [ha.2]
    simp
  have hbmem : (chordPair hred hspan f a).1 ∈ endpointIndices hspan f b.1 := by
    rw [chordPair_spec hred hspan f b |>.2, ← hp]
    simp
  exact (Finset.disjoint_left.mp hdisj) hmem hbmem

noncomputable def redChords
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Finset (BoundaryIndex (normals (nonordinaryPoints P)) f ×
      BoundaryIndex (normals (nonordinaryPoints P)) f) :=
  Finset.univ.image (chordPair hred hspan f)

theorem mem_redChords_iff
    (f : StrictFace (normals (nonordinaryPoints P))) (p :
      BoundaryIndex (normals (nonordinaryPoints P)) f ×
        BoundaryIndex (normals (nonordinaryPoints P)) f) :
    p ∈ redChords hred hspan f ↔
      ∃ a : ChordLine f, chordPair hred hspan f a = p := by
  simp [redChords]

theorem redChord_distinct
    (f : StrictFace (normals (nonordinaryPoints P))) (p :
      BoundaryIndex (normals (nonordinaryPoints P)) f ×
        BoundaryIndex (normals (nonordinaryPoints P)) f)
    (hp : p ∈ redChords hred hspan f) : p.1 ≠ p.2 := by
  obtain ⟨a, rfl⟩ := (mem_redChords_iff hred hspan f p).mp hp
  exact (chordPair_spec hred hspan f a).1

def chordEndpoints {f : StrictFace (normals (nonordinaryPoints P))}
    (p : BoundaryIndex (normals (nonordinaryPoints P)) f ×
      BoundaryIndex (normals (nonordinaryPoints P)) f) :
    Finset (BoundaryIndex (normals (nonordinaryPoints P)) f) := {p.1, p.2}

theorem chordEndpoints_disjoint
    (f : StrictFace (normals (nonordinaryPoints P)))
    {p q : BoundaryIndex (normals (nonordinaryPoints P)) f ×
      BoundaryIndex (normals (nonordinaryPoints P)) f}
    (hp : p ∈ redChords hred hspan f) (hq : q ∈ redChords hred hspan f)
    (hpq : p ≠ q) : Disjoint (chordEndpoints p) (chordEndpoints q) := by
  obtain ⟨a, rfl⟩ := (mem_redChords_iff hred hspan f p).mp hp
  obtain ⟨b, rfl⟩ := (mem_redChords_iff hred hspan f q).mp hq
  change Disjoint
    ({(chordPair hred hspan f a).1, (chordPair hred hspan f a).2} :
      Finset (BoundaryIndex (normals (nonordinaryPoints P)) f))
    ({(chordPair hred hspan f b).1, (chordPair hred hspan f b).2} :
      Finset (BoundaryIndex (normals (nonordinaryPoints P)) f))
  rw [← chordPair_spec hred hspan f a |>.2,
    ← chordPair_spec hred hspan f b |>.2]
  apply endpointIndices_disjoint hred hspan f
  intro hab
  exact hpq (congrArg (chordPair hred hspan f) hab)

noncomputable def redEndpoints
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Finset (BoundaryIndex (normals (nonordinaryPoints P)) f) :=
  (redChords hred hspan f).biUnion chordEndpoints

theorem mem_redEndpoints_iff
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
    i ∈ redEndpoints hred hspan f ↔
      ∃ p ∈ redChords hred hspan f, i = p.1 ∨ i = p.2 := by
  simp [redEndpoints, chordEndpoints]

theorem redEndpoints_card
    (f : StrictFace (normals (nonordinaryPoints P))) :
    (redEndpoints hred hspan f).card = 2 * (redChords hred hspan f).card := by
  rw [redEndpoints, Finset.card_biUnion]
  · calc
      (∑ p ∈ redChords hred hspan f, (chordEndpoints p).card) =
          ∑ _p ∈ redChords hred hspan f, 2 := by
            apply Finset.sum_congr rfl
            intro p hp
            exact Finset.card_pair (redChord_distinct hred hspan f p hp)
      _ = 2 * (redChords hred hspan f).card := by simp [Nat.mul_comm]
  · intro p hp q hq hpq
    exact chordEndpoints_disjoint hred hspan f hp hq hpq

theorem redChord_nonadjacent
    (f : StrictFace (normals (nonordinaryPoints P)))
    (p : BoundaryIndex (normals (nonordinaryPoints P)) f ×
      BoundaryIndex (normals (nonordinaryPoints P)) f)
    (hp : p ∈ redChords hred hspan f) :
    p.2 ≠ Erdos957.cyclicSucc p.1 ∧
      p.1 ≠ Erdos957.cyclicSucc p.2 := by
  obtain ⟨a, rfl⟩ := (mem_redChords_iff hred hspan f p).mp hp
  have hs := chordPair_spec hred hspan f a
  have hinc1 : Incident
      (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f
        (chordPair hred hspan f a).1) a.1.1 := by
    have hm : (chordPair hred hspan f a).1 ∈ endpointIndices hspan f a.1 := by
      rw [hs.2]
      simp
    exact (Finset.mem_filter.mp hm).2
  have hinc2 : Incident
      (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f
        (chordPair hred hspan f a).2) a.1.1 := by
    have hm : (chordPair hred hspan f a).2 ∈ endpointIndices hspan f a.1 := by
      rw [hs.2]
      simp
    exact (Finset.mem_filter.mp hm).2
  have not_adjacent (i j : BoundaryIndex (normals (nonordinaryPoints P)) f)
      (hi : Incident
        (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i) a.1.1)
      (hj : Incident
        (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f j) a.1.1) :
      j ≠ Erdos957.cyclicSucc i := by
    intro hadj
    let e := boundaryEdge (normals (nonordinaryPoints P)) normal_cross hspan f i
    have hae : a.1.1 ≠ e.1.1.1 := by
      exact RedChordIncidence.red_ne_blue a.1.2 e.1.1.2
    have hvi := boundaryVertex_on_edge_start
      (normals (nonordinaryPoints P)) normal_cross hspan f i
    have hvj := boundaryVertex_on_edge_finish
      (normals (nonordinaryPoints P)) normal_cross hspan f i
    have heq : boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i =
        boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f j := by
      apply ProjectiveArrangement.eq_of_two_common_lines hae
      · exact hi
      · exact hvi
      · exact hj
      · simpa [hadj, Incident, normals] using hvj
    exact (boundaryVertex_ne_succ hspan f i) (by simpa [hadj] using heq)
  exact ⟨not_adjacent _ _ hinc1 hinc2,
    not_adjacent _ _ hinc2 hinc1⟩

end Erdos735.PolarRedChordExtraction
