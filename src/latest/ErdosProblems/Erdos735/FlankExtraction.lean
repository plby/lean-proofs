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

import ErdosProblems.Erdos735.Discharging4Concrete

/-!
# Extracting the Stage-4 flank lookup system

Finite neighbor sets of cardinality at most two can be enumerated by two optional slots.  Applying
this to the actual geometric-flank relation removes both lookup maps and their coherence equation
as independent inputs to `FlankSystem`.
-/

open Classical
noncomputable section

namespace Erdos735

universe u

/-- Embed any finite set of cardinality at most two into `Fin 2`. -/
noncomputable def boundedTwoEmbedding {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (hcard : S.card ≤ 2) : S ↪ Fin 2 :=
  (Fintype.equivFin S).toEmbedding.trans
    ⟨Fin.castLE (by simpa only [Fintype.card_coe] using hcard),
      Fin.castLE_injective _⟩

/-- Enumerate a finite set of cardinality at most two by two optional slots. -/
noncomputable def boundedTwoLookup {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (hcard : S.card ≤ 2) (side : Fin 2) : Option α :=
  if h : ∃ x : S, boundedTwoEmbedding S hcard x = side then
    some (Classical.choose h).1
  else none

theorem boundedTwoLookup_at_embedding {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (hcard : S.card ≤ 2) (x : S) :
    boundedTwoLookup S hcard (boundedTwoEmbedding S hcard x) = some x.1 := by
  unfold boundedTwoLookup
  split
  · rename_i h
    congr 1
    have heq : Classical.choose h = x :=
      (boundedTwoEmbedding S hcard).injective (Classical.choose_spec h)
    exact congrArg Subtype.val heq
  · rename_i h
    exact (h ⟨x, rfl⟩).elim

theorem boundedTwoLookup_eq_some_mem {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (hcard : S.card ≤ 2) (side : Fin 2) (x : α)
    (hlookup : boundedTwoLookup S hcard side = some x) : x ∈ S := by
  unfold boundedTwoLookup at hlookup
  split at hlookup
  · rename_i h
    have hx : (Classical.choose h).1 = x := Option.some.inj hlookup
    exact hx ▸ (Classical.choose h).2
  · simp at hlookup

theorem exists_boundedTwoLookup_eq_some_iff_mem
    {α : Type u} [Fintype α] [DecidableEq α]
    (S : Finset α) (hcard : S.card ≤ 2) (x : α) :
    (∃ side, boundedTwoLookup S hcard side = some x) ↔ x ∈ S := by
  constructor
  · rintro ⟨side, hside⟩
    exact boundedTwoLookup_eq_some_mem S hcard side x hside
  · intro hx
    let y : S := ⟨x, hx⟩
    exact ⟨boundedTwoEmbedding S hcard y,
      boundedTwoLookup_at_embedding S hcard y⟩

namespace ABKPR.Data

universe uV uEd uF uL

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable {A : ABKPR.Data C}
variable {Line : Type uL} [Fintype Line] [DecidableEq Line]

def geometricFlanks (edgeLine : Edge → Line) (e : A.EvilFace) :
    Finset A.HelpingPair :=
  Finset.univ.filter fun h ↦ A.IsGeometricFlank edgeLine e h

def geometricEvilEndpoints (edgeLine : Edge → Line) (h : A.HelpingPair) :
    Finset A.EvilFace :=
  Finset.univ.filter fun e ↦ A.IsGeometricFlank edgeLine e h

/-- Minimal relation-level geometric input for Stage 4.  The lookup maps of
`FlankSystem` are extracted from the actual geometric flank relation. -/
structure GeometricFlankBounds (Line : Type uL) [Fintype Line] [DecidableEq Line] where
  edgeLine : Edge → Line
  evil_has_geometric_flank : ∀ e, (A.geometricFlanks edgeLine e).Nonempty
  evil_geometricFlanks_card_le_two : ∀ e,
    (A.geometricFlanks edgeLine e).card ≤ 2
  helper_geometricEndpoints_card_le_two : ∀ h,
    (A.geometricEvilEndpoints edgeLine h).card ≤ 2

namespace GeometricFlankBounds

variable (K : A.GeometricFlankBounds Line)

noncomputable def evilFlank (e : A.EvilFace) (side : Fin 2) : Option A.HelpingPair :=
  boundedTwoLookup (A.geometricFlanks K.edgeLine e)
    (K.evil_geometricFlanks_card_le_two e) side

noncomputable def helperEndpoint (h : A.HelpingPair) (endpoint : Fin 2) : Option A.EvilFace :=
  boundedTwoLookup (A.geometricEvilEndpoints K.edgeLine h)
    (K.helper_geometricEndpoints_card_le_two h) endpoint

theorem exists_evilFlank_iff (e : A.EvilFace) (h : A.HelpingPair) :
    (∃ side, K.evilFlank e side = some h) ↔
      A.IsGeometricFlank K.edgeLine e h := by
  unfold evilFlank
  rw [exists_boundedTwoLookup_eq_some_iff_mem]
  simp [geometricFlanks]

theorem exists_helperEndpoint_iff (e : A.EvilFace) (h : A.HelpingPair) :
    (∃ endpoint, K.helperEndpoint h endpoint = some e) ↔
      A.IsGeometricFlank K.edgeLine e h := by
  unfold helperEndpoint
  rw [exists_boundedTwoLookup_eq_some_iff_mem]
  simp [geometricEvilEndpoints]

/-- Construct the complete two-sided lookup system from the geometric
relation and its two degree bounds. -/
noncomputable def toFlankSystem : A.FlankSystem Line where
  edgeLine := K.edgeLine
  evilFlank := K.evilFlank
  helperEndpoint := K.helperEndpoint
  lookup_coherent := by
    intro e h
    rw [K.exists_evilFlank_iff e h, K.exists_helperEndpoint_iff e h]
  evil_has_flank := by
    intro e
    obtain ⟨h, hh⟩ := K.evil_has_geometric_flank e
    have hgeom : A.IsGeometricFlank K.edgeLine e h := by
      simpa [geometricFlanks] using hh
    obtain ⟨side, hside⟩ := (K.exists_evilFlank_iff e h).2 hgeom
    exact ⟨side, h, hside⟩
  evilFlank_geometric := by
    intro e side h hside
    exact (K.exists_evilFlank_iff e h).1 ⟨side, hside⟩

end GeometricFlankBounds
end ABKPR.Data
end Erdos735
