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

import ErdosProblems.Erdos735.Discharging4

/-!
# Concrete helping pairs for the fourth ABKPR discharging step

A helping pair is represented by a boundary dart of a zero-diagonal
quadrangle whose face across the dart is not a bad two-diagonal quadrangle.
This file proves directly that the Stage-3 charge of a face pays for all of
its helping pairs.  It also packages the two-flank/two-endpoint local
geometry as mutually coherent `Fin 2` lookup maps; the degree bounds of the
helping/evil graph then follow by finite counting.
-/

namespace Erdos735

open scoped BigOperators
noncomputable section

universe uV uEd uF

namespace ABKPR.Data

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C : BlueCellulation Vertex Edge Face}
variable {A : ABKPR.Data C}

/-- A quadrangular face with no red diagonal. -/
def IsZeroDiagonalQuadrangle (f : Face) : Prop :=
  C.faceDegree f = 4 ∧ (A.redChords f).card = 0

instance (f : Face) : Decidable (A.IsZeroDiagonalQuadrangle f) := by
  unfold IsZeroDiagonalQuadrangle
  infer_instance

/-- The boundary indices of a zero-diagonal quadrangle which do not border a
bad two-diagonal quadrangle. -/
def helpingIndices (f : Face) : Finset (Fin (C.faceDegree f)) :=
  Finset.univ.filter fun i =>
    A.IsZeroDiagonalQuadrangle f ∧
      ¬ A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1

/-- The concrete helping pairs `(supporting line, quadrangle)`.  The
supporting line is recoverable from the boundary edge once line labels are
added; at the cellulation level the boundary dart is the canonical data. -/
abbrev HelpingPair := (f : Face) × {i : Fin (C.faceDegree f) // i ∈ A.helpingIndices f}

def HelpingPair.face (h : A.HelpingPair) : Face := h.1

def HelpingPair.index (h : A.HelpingPair) : Fin (C.faceDegree h.face) := h.2.1

def HelpingPair.dart (h : A.HelpingPair) : FaceDart C := ⟨h.face, h.index⟩

lemma HelpingPair.isZeroDiagonal (h : A.HelpingPair) :
    A.IsZeroDiagonalQuadrangle h.face := by
  exact (Finset.mem_filter.mp h.2.2).2.1

lemma HelpingPair.across_not_bad (h : A.HelpingPair) :
    ¬ A.IsBadTwoQuadrangle (A.across h.dart).1 := by
  exact (Finset.mem_filter.mp h.2.2).2.2

lemma redEndpoints_eq_empty_of_zeroDiagonal {f : Face}
    (hf : A.IsZeroDiagonalQuadrangle f) : A.redEndpoints f = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [A.redEndpoints_card, hf.2]

lemma stage1Corners_eq_empty_of_zeroDiagonal {f : Face}
    (hf : A.IsZeroDiagonalQuadrangle f) : A.stage1Corners f = ∅ := by
  have hsub := A.stage1Corners_subset f
  rw [A.redEndpoints_eq_empty_of_zeroDiagonal hf] at hsub
  exact Finset.Subset.antisymm hsub (Finset.empty_subset _)

lemma not_isBadTwoQuadrangle_of_zeroDiagonal {f : Face}
    (hf : A.IsZeroDiagonalQuadrangle f) : ¬ A.IsBadTwoQuadrangle f := by
  intro hbad
  have hzero := hf.2
  have htwo := hbad.1.2
  omega

lemma not_isBadTriangle_of_zeroDiagonal {f : Face}
    (hf : A.IsZeroDiagonalQuadrangle f) : ¬ A.IsBadTriangle f := by
  intro hbad
  have hfour := hf.1
  have hthree := hbad.1
  omega

/-- The exact Stage-3 charge of a zero-diagonal quadrangle, in quarter-units. -/
lemma step3FaceCharge4_zeroDiagonal {f : Face}
    (hf : A.IsZeroDiagonalQuadrangle f) :
    A.step3FaceCharge4 f = 4 - A.badNeighborCount f := by
  have hcorners := A.stage1Corners_eq_empty_of_zeroDiagonal hf
  have hout := A.donationRecipients_eq_empty_of_degree_lt_five
    (f := f) (by have hfour := hf.1; omega)
  have hin := A.donationDonors_eq_empty_of_not_badTriangle
    (A.not_isBadTriangle_of_zeroDiagonal hf)
  have hnotbad := A.not_isBadTwoQuadrangle_of_zeroDiagonal hf
  simp [step3FaceCharge4, step2FaceCharge4, step1FaceCharge4,
    initialFaceCharge4, BlueCellulation.faceCharge, hf.1, hcorners, hout,
    hin, hnotbad]

/-- Helpful and bad-neighbor indices partition the four boundary indices of
a zero-diagonal quadrangle. -/
lemma badNeighborCount_add_helpingIndices_card {f : Face}
    (hf : A.IsZeroDiagonalQuadrangle f) :
    A.badNeighborCount f + (A.helpingIndices f).card = 4 := by
  let p : Fin (C.faceDegree f) → Prop := fun i =>
    A.IsBadTwoQuadrangle (A.across ⟨f, i⟩).1
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (C.faceDegree f)))) p
  simpa [p, badNeighborCount, badNeighborIndices, helpingIndices, hf,
    Fintype.card_fin, hf.1] using hpartition

/-- A zero-diagonal face has exactly one quarter-unit for every concrete
helping pair which it owns. -/
lemma helpingIndices_card_eq_step3FaceCharge4 {f : Face}
    (hf : A.IsZeroDiagonalQuadrangle f) :
    ((A.helpingIndices f).card : ℤ) = A.step3FaceCharge4 f := by
  have hpartition := A.badNeighborCount_add_helpingIndices_card hf
  rw [A.step3FaceCharge4_zeroDiagonal hf]
  omega

private noncomputable def helpingOwnerFiberEquiv (f : Face) :
    {h : A.HelpingPair // h.face = f} ≃ A.helpingIndices f where
  toFun h := by
    rcases h with ⟨⟨g, i⟩, hgf⟩
    change g = f at hgf
    subst g
    exact i
  invFun i := ⟨⟨f, i⟩, rfl⟩
  left_inv h := by
    rcases h with ⟨⟨g, i⟩, hgf⟩
    change g = f at hgf
    subst g
    rfl
  right_inv i := rfl

lemma helpingPair_ownerFiber_card (f : Face) :
    (Finset.univ.filter fun h : A.HelpingPair => h.face = f).card =
      (A.helpingIndices f).card := by
  classical
  calc
    (Finset.univ.filter fun h : A.HelpingPair => h.face = f).card =
        Fintype.card {h : A.HelpingPair // h.face = f} := by
          rw [Fintype.card_subtype]
    _ = Fintype.card (A.helpingIndices f) :=
      Fintype.card_congr (A.helpingOwnerFiberEquiv f)
    _ = (A.helpingIndices f).card := Fintype.card_coe _

/-- Concrete owner capacity, with no capacity condition imposed on negative
evil triangles. -/
lemma helpingPair_ownerCapacity (f : Face) (hcharge : 0 ≤ A.step3FaceCharge4 f) :
    ((Finset.univ.filter fun h : A.HelpingPair => h.face = f).card : ℤ) ≤
      A.step3FaceCharge4 f := by
  rw [A.helpingPair_ownerFiber_card f]
  by_cases hf : A.IsZeroDiagonalQuadrangle f
  · exact le_of_eq (A.helpingIndices_card_eq_step3FaceCharge4 hf)
  · simpa [helpingIndices, hf] using hcharge

lemma helpingPair_face_ne_evilFace (h : A.HelpingPair) (e : A.EvilFace) :
    h.face ≠ e.1 := by
  intro heq
  have h4 := h.isZeroDiagonal.1
  have h3 := e.2.1.1
  rw [heq] at h4
  omega

/-- The unique boundary dart by which an evil triangle meets its bad
two-diagonal quadrangle. -/
noncomputable def evilIndex (e : A.EvilFace) : Fin (C.faceDegree e.1) :=
  Classical.choose (Finset.card_eq_one.mp (by
    simpa [badNeighborCount] using e.2.1.2))

lemma badNeighborIndices_eq_singleton (e : A.EvilFace) :
    A.badNeighborIndices e.1 = {A.evilIndex e} := by
  exact Classical.choose_spec (Finset.card_eq_one.mp (by
    simpa [badNeighborCount] using e.2.1.2))

noncomputable def evilDart (e : A.EvilFace) : FaceDart C :=
  ⟨e.1, A.evilIndex e⟩

lemma evilDart_across_bad (e : A.EvilFace) :
    A.IsBadTwoQuadrangle (A.across (A.evilDart e)).1 := by
  have hmem : A.evilIndex e ∈ A.badNeighborIndices e.1 := by
    rw [A.badNeighborIndices_eq_singleton e]
    simp
  exact (Finset.mem_filter.mp hmem).2

section FlankGraph

universe uL

variable {Line : Type uL} [Fintype Line] [DecidableEq Line]

/-- Two indices on the same face are cyclically adjacent. -/
def CyclicAdjacentIndex {f : Face} (i j : Fin (C.faceDegree f)) : Prop :=
  faceSucc C f i = j ∨ faceSucc C f j = i

/-- `h` is one of the two flank helpers beside the bad quadrangle belonging
to `e`.  Besides face adjacency, its designated edge has the same supporting
arrangement line as the evil triangle's bad-neighbor edge. -/
def IsGeometricFlank (edgeLine : Edge → Line)
    (e : A.EvilFace) (h : A.HelpingPair) : Prop :=
  let badDart := A.across (A.evilDart e)
  (∃ j : Fin (C.faceDegree badDart.1),
      CyclicAdjacentIndex (C := C) badDart.2 j ∧
        (A.across ⟨badDart.1, j⟩).1 = h.face) ∧
    edgeLine (A.boundaryEdge h.face h.index) =
      edgeLine (A.boundaryEdge e.1 (A.evilIndex e))

/-- Exact local input for the helping graph.  `evilFlank` looks to the two
sides of an evil pair; `helperEndpoint` looks at the two endpoints of a
helping edge.  Their coherence says that these are the same adjacency
relation.  Consequently all graph degree bounds are theorems, rather than
additional cardinal assumptions. -/
structure FlankSystem (Line : Type uL) [Fintype Line] [DecidableEq Line] where
  edgeLine : Edge → Line
  evilFlank : A.EvilFace → Fin 2 → Option A.HelpingPair
  helperEndpoint : A.HelpingPair → Fin 2 → Option A.EvilFace
  lookup_coherent : ∀ e h,
    (∃ side, evilFlank e side = some h) ↔
      ∃ endpoint, helperEndpoint h endpoint = some e
  evil_has_flank : ∀ e, ∃ side h, evilFlank e side = some h
  evilFlank_geometric : ∀ e side h, evilFlank e side = some h →
    A.IsGeometricFlank edgeLine e h

namespace FlankSystem

variable (L : A.FlankSystem Line)

/-- The concrete flank adjacency relation. -/
def Adj (e : A.EvilFace) (h : A.HelpingPair) : Prop :=
  ∃ side, L.evilFlank e side = some h

@[instance_reducible] def adjDecidable : DecidableRel L.Adj :=
  fun e h => Classical.propDecidable (L.Adj e h)

local instance : DecidableRel L.Adj := L.adjDecidable

lemma evilDegree_one_le (e : A.EvilFace) :
    1 ≤ (Finset.univ.filter fun h => L.Adj e h).card := by
  obtain ⟨side, h, hh⟩ := L.evil_has_flank e
  apply Finset.one_le_card.mpr
  exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨side, hh⟩⟩⟩

lemma evilDegree_le_two (e : A.EvilFace) :
    (Finset.univ.filter fun h => L.Adj e h).card ≤ 2 := by
  classical
  rw [← Fintype.card_subtype]
  let pick : {h : A.HelpingPair // L.Adj e h} → Fin 2 :=
    fun h => Classical.choose h.2
  have hpick (h : {h : A.HelpingPair // L.Adj e h}) :
      L.evilFlank e (pick h) = some h.1 := Classical.choose_spec h.2
  have hinjective : Function.Injective pick := by
    intro h k hpk
    apply Subtype.ext
    have hh := hpick h
    have hk := hpick k
    rw [hpk] at hh
    exact Option.some.inj (hh.symm.trans hk)
  simpa only [Fintype.card_fin] using
    (Fintype.card_le_of_injective pick hinjective)

lemma helpingDegree_le_two (h : A.HelpingPair) :
    (Finset.univ.filter fun e => L.Adj e h).card ≤ 2 := by
  classical
  rw [← Fintype.card_subtype]
  let pick : {e : A.EvilFace // L.Adj e h} → Fin 2 := fun e =>
    Classical.choose ((L.lookup_coherent e.1 h).mp e.2)
  have hpick (e : {e : A.EvilFace // L.Adj e h}) :
      L.helperEndpoint h (pick e) = some e.1 :=
    Classical.choose_spec ((L.lookup_coherent e.1 h).mp e.2)
  have hinjective : Function.Injective pick := by
    intro e d hed
    apply Subtype.ext
    have he := hpick e
    have hd := hpick d
    rw [hed] at he
    exact Option.some.inj (he.symm.trans hd)
  simpa only [Fintype.card_fin] using
    (Fintype.card_le_of_injective pick hinjective)

noncomputable def toHelpingGraph : HelpingGraph A.HelpingPair A.EvilFace where
  Adj := L.Adj
  adjDecidable := L.adjDecidable
  evilDegree_one_le := L.evilDegree_one_le
  evilDegree_le_two := L.evilDegree_le_two
  helpingDegree_le_two := L.helpingDegree_le_two

noncomputable def toStage4FaceGeometry :
    A.Stage4FaceGeometry A.HelpingPair where
  graph := toHelpingGraph L
  helpFace := HelpingPair.face
  helpFace_ne_evilFace := A.helpingPair_face_ne_evilFace
  helpFace_capacity := A.helpingPair_ownerCapacity

/-- Once the Levi/no-evil-path input is supplied, all remaining Stage-4
bookkeeping is now discharged by the concrete helper construction. -/
theorem contradiction
    (H : A.Stage3Hypotheses) (hrest : A.EndpointRestriction)
    (hpack : A.NeighborPacking)
    (hpath : (toHelpingGraph L).NoEvilEvilPath) : False :=
  (toStage4FaceGeometry L).contradiction H hrest hpack hpath

end FlankSystem

end FlankGraph

end ABKPR.Data

end

end Erdos735
