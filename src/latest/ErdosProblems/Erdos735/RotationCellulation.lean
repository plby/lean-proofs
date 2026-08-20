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

import ErdosProblems.Erdos735.BlueCellulation
import ErdosProblems.Erdos735.ChartOrder
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Cellulations extracted from spherical rotation systems

A rotation of the darts of a finite simple graph determines its facial
permutation by first reversing a dart and then taking the next dart around
the new source. This file packages the finite hypotheses satisfied by a
nondegenerate great-circle arrangement and extracts the blue sphere
cellulation and the indexed boundary/across-edge data used by the ABKPR
discharging argument.
-/

open Classical
open scoped BigOperators
noncomputable section

namespace Erdos735.RotationCellulation

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype G.edgeSet]


noncomputable def dartFlip : Equiv.Perm G.Dart where
  toFun := SimpleGraph.Dart.symm
  invFun := SimpleGraph.Dart.symm
  left_inv := SimpleGraph.Dart.symm_symm
  right_inv := SimpleGraph.Dart.symm_symm

noncomputable def facePerm (rotation : Equiv.Perm G.Dart) : Equiv.Perm G.Dart :=
  rotation * dartFlip G

/-- The finite rotation-system certificate which remains to be constructed
from a concrete family of great circles.  Everything after this interface is
pure finite combinatorics. -/
structure SphericalRotationData where
  rotation : Equiv.Perm G.Dart
  rotation_source : ∀ d, (rotation d).fst = d.fst
  blueMultiplicity : V → ℕ
  degree_eq : ∀ v, G.degree v = 2 * blueMultiplicity v
  multiplicity_two_le : ∀ v, 2 ≤ blueMultiplicity v
  face_support : (facePerm G rotation).support = Finset.univ
  face_edge_injective :
    ∀ c ∈ (facePerm G rotation).cycleFactorsFinset,
      Set.InjOn SimpleGraph.Dart.edge (c.support : Set G.Dart)
  face_vertex_injective :
    ∀ c ∈ (facePerm G rotation).cycleFactorsFinset,
      Set.InjOn (fun d : G.Dart => d.fst) (c.support : Set G.Dart)
  opposite_faces :
    ∀ d, (facePerm G rotation).cycleOf d ≠
      (facePerm G rotation).cycleOf d.symm
  face_three :
    ∀ c ∈ (facePerm G rotation).cycleFactorsFinset, 3 ≤ c.support.card
  euler :
    (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) +
      ((facePerm G rotation).cycleFactorsFinset.card : ℤ) = 2

namespace SphericalRotationData

variable {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]
variable (R : SphericalRotationData G)

abbrev Edge (_R : SphericalRotationData G) := G.edgeFinset
abbrev Face := (facePerm G R.rotation).cycleFactorsFinset

instance : DecidableEq (R.Face) := inferInstance

def dartEdge (R : SphericalRotationData G) (d : G.Dart) : R.Edge :=
  ⟨d.edge, by simpa [SimpleGraph.mem_edgeFinset] using d.edge_mem⟩

@[simp] theorem dartEdge_val (d : G.Dart) : (R.dartEdge d).1 = d.edge := rfl

@[simp] theorem dartEdge_symm (d : G.Dart) : R.dartEdge d.symm = R.dartEdge d := by
  apply Subtype.ext
  exact d.edge_symm

def vertexEdges (v : V) : Finset R.Edge :=
  Finset.univ.filter fun e => v ∈ (e.1 : Sym2 V)

def edgeVertices (e : R.Edge) : Finset V := e.1.toFinset

theorem vertexEdge_iff (v : V) (e : R.Edge) :
    e ∈ R.vertexEdges v ↔ v ∈ R.edgeVertices e := by
  simp [vertexEdges, edgeVertices, Sym2.mem_toFinset]

theorem edgeVertices_card (e : R.Edge) : (R.edgeVertices e).card = 2 := by
  exact SimpleGraph.card_toFinset_mem_edgeFinset e

theorem vertexEdges_card (v : V) :
    (R.vertexEdges v).card = 2 * R.blueMultiplicity v := by
  calc
    (R.vertexEdges v).card = (G.incidenceFinset v).card := by
      rw [G.incidenceFinset_eq_filter]
      apply Finset.card_bij (fun e _ => e.1)
      · intro e he
        have hev : v ∈ (e.1 : Sym2 V) := (Finset.mem_filter.mp he).2
        exact Finset.mem_filter.mpr ⟨e.2, hev⟩
      · intro e he f hf h
        exact Subtype.ext h
      · intro e he
        have heG : e ∈ G.edgeFinset := (Finset.mem_filter.mp he).1
        refine ⟨⟨e, heG⟩, ?_, rfl⟩
        simp only [vertexEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (Finset.mem_filter.mp he).2
    _ = G.degree v := G.card_incidenceFinset_eq_degree v
    _ = 2 * R.blueMultiplicity v := R.degree_eq v

abbrev perm := facePerm G R.rotation

def faceBase (f : R.Face) : G.Dart :=
  Classical.choose ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp f.2).1.nonempty_support)

theorem faceBase_mem (f : R.Face) : R.faceBase f ∈ f.1.support :=
  Classical.choose_spec ((Equiv.Perm.mem_cycleFactorsFinset_iff.mp f.2).1.nonempty_support)

theorem face_cycleOf_base (f : R.Face) :
    (R.perm).cycleOf (R.faceBase f) = f.1 := by
  exact (Equiv.Perm.cycle_is_cycleOf (R.faceBase_mem f) f.2).symm

def faceDarts (f : R.Face) : List G.Dart :=
  (R.perm).toList (R.faceBase f)

theorem faceDarts_nodup (f : R.Face) : (R.faceDarts f).Nodup :=
  Equiv.Perm.nodup_toList _ _

theorem faceBase_mem_perm_support (f : R.Face) :
    R.faceBase f ∈ R.perm.support := by
  rw [R.face_support]
  exact Finset.mem_univ _

theorem mem_faceDarts_iff (f : R.Face) (d : G.Dart) :
    d ∈ R.faceDarts f ↔ d ∈ f.1.support := by
  rw [faceDarts, Equiv.Perm.mem_toList_iff]
  rw [← R.face_cycleOf_base f, Equiv.Perm.mem_support_cycleOf_iff]

theorem faceOf_mem_factors (d : G.Dart) :
    R.perm.cycleOf d ∈ R.perm.cycleFactorsFinset := by
  rw [Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff, R.face_support]
  exact Finset.mem_univ d

def faceOf (d : G.Dart) : R.Face := ⟨R.perm.cycleOf d, R.faceOf_mem_factors d⟩

theorem faceOf_eq_iff_mem (f : R.Face) (d : G.Dart) :
    R.faceOf d = f ↔ d ∈ R.faceDarts f := by
  rw [R.mem_faceDarts_iff]
  constructor
  · intro h
    have hcycle : R.perm.cycleOf d = f.1 := congrArg Subtype.val h
    rw [← hcycle, Equiv.Perm.mem_support_cycleOf_iff]
    constructor
    · exact Equiv.Perm.SameCycle.refl R.perm d
    · rw [R.face_support]
      exact Finset.mem_univ d
  · intro hd
    apply Subtype.ext
    exact (R.perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff f.1 f.2 d).mpr hd |>.symm

theorem faceOf_faceBase (f : R.Face) : R.faceOf (R.faceBase f) = f := by
  apply Subtype.ext
  exact R.face_cycleOf_base f

theorem faceOf_perm (d : G.Dart) : R.faceOf (R.perm d) = R.faceOf d := by
  apply Subtype.ext
  exact Equiv.Perm.cycleOf_self_apply R.perm d

theorem faceOf_symm_ne (d : G.Dart) : R.faceOf d.symm ≠ R.faceOf d := by
  intro h
  apply R.opposite_faces d
  exact congrArg Subtype.val h.symm

def faceBoundary (f : R.Face) : List R.Edge :=
  (R.faceDarts f).map R.dartEdge

theorem faceBoundary_nodup (f : R.Face) : (R.faceBoundary f).Nodup := by
  rw [faceBoundary, List.nodup_map_iff_inj_on (R.faceDarts_nodup f)]
  intro d hd e he hde
  apply R.face_edge_injective f.1 f.2
  · exact (R.mem_faceDarts_iff f d).mp hd
  · exact (R.mem_faceDarts_iff f e).mp he
  · exact congrArg Subtype.val hde

theorem faceBoundary_length (f : R.Face) :
    (R.faceBoundary f).length = f.1.support.card := by
  rw [faceBoundary, List.length_map, faceDarts, Equiv.Perm.length_toList,
    R.face_cycleOf_base f]

theorem faceDegree_three_le (f : R.Face) : 3 ≤ (R.faceBoundary f).length := by
  rw [R.faceBoundary_length f]
  exact R.face_three f.1 f.2

theorem exists_dart_of_edge (e : R.Edge) : ∃ d : G.Dart, d.edge = e.1 := by
  have hc : ({d : G.Dart | d.edge = e.1} : Finset G.Dart).card = 2 :=
    G.dart_edge_fiber_card e.1 (SimpleGraph.mem_edgeFinset.mp e.2)
  have hne : ({d : G.Dart | d.edge = e.1} : Finset G.Dart).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.card_empty] at hc
    omega
  obtain ⟨d, hd⟩ := hne
  exact ⟨d, by simpa using hd⟩

def edgeDart (R : SphericalRotationData G) (e : R.Edge) : G.Dart :=
  Classical.choose (R.exists_dart_of_edge e)

@[simp] theorem edgeDart_edge (e : R.Edge) : (R.edgeDart e).edge = e.1 := by
  exact Classical.choose_spec (R.exists_dart_of_edge e)

@[simp] theorem dartEdge_edgeDart (e : R.Edge) : R.dartEdge (R.edgeDart e) = e := by
  apply Subtype.ext
  exact R.edgeDart_edge e

def edgeFaces (e : R.Edge) : Finset R.Face :=
  {R.faceOf (R.edgeDart e), R.faceOf (R.edgeDart e).symm}

theorem edgeFaces_card (e : R.Edge) : (R.edgeFaces e).card = 2 := by
  apply Finset.card_pair
  exact (R.faceOf_symm_ne (R.edgeDart e)).symm

theorem dart_edge_eq_edgeDart (d : G.Dart) :
    d = R.edgeDart (R.dartEdge d) ∨ d = (R.edgeDart (R.dartEdge d)).symm := by
  rw [← SimpleGraph.dart_edge_eq_iff]
  exact (R.edgeDart_edge (R.dartEdge d)).symm

theorem faceEdge_iff (f : R.Face) (e : R.Edge) :
    e ∈ R.faceBoundary f ↔ f ∈ R.edgeFaces e := by
  rw [faceBoundary, List.mem_map, edgeFaces, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨d, hd, hde⟩
    have hdcase := R.dart_edge_eq_edgeDart d
    have hface : R.faceOf d = f := (R.faceOf_eq_iff_mem f d).mpr hd
    rcases hdcase with h | h
    · left
      rw [← hde, ← h]
      exact hface.symm
    · right
      rw [← hde, ← h]
      exact hface.symm
  · intro hf
    have hf' : f = R.faceOf (R.edgeDart e) ∨
        f = R.faceOf (R.edgeDart e).symm := by simpa using hf
    rcases hf' with hf' | hf'
    · refine ⟨R.edgeDart e, ?_, ?_⟩
      · exact (R.faceOf_eq_iff_mem f _).mp hf'.symm
      · exact R.dartEdge_edgeDart e
    · refine ⟨(R.edgeDart e).symm, ?_, ?_⟩
      · exact (R.faceOf_eq_iff_mem f _).mp hf'.symm
      · rw [R.dartEdge_symm, R.dartEdge_edgeDart]

def toBlueCellulation : BlueCellulation V R.Edge R.Face where
  blueMultiplicity := R.blueMultiplicity
  vertexEdges := R.vertexEdges
  edgeVertices := R.edgeVertices
  vertexEdge_iff := R.vertexEdge_iff
  edgeVertices_card := R.edgeVertices_card
  vertexEdges_card := R.vertexEdges_card
  blueMultiplicity_two_le := R.multiplicity_two_le
  faceBoundary := R.faceBoundary
  faceBoundary_nodup := R.faceBoundary_nodup
  edgeFaces := R.edgeFaces
  faceEdge_iff := R.faceEdge_iff
  edgeFaces_card := R.edgeFaces_card
  faceDegree_three_le := R.faceDegree_three_le
  euler_sphere := by simpa only [Fintype.card_coe] using R.euler

abbrev C := R.toBlueCellulation

/-- Boundary and across-edge information extracted canonically from the face
permutation.  The remaining red-chord fields of `ABKPR.Data` are geometric. -/
structure BoundaryAcrossData where
  boundaryVertex : ∀ f, Fin (R.C.faceDegree f) → V
  boundaryEdge : ∀ f, Fin (R.C.faceDegree f) → R.Edge
  boundaryVertex_injective : ∀ f, Function.Injective (boundaryVertex f)
  boundaryEdge_injective : ∀ f, Function.Injective (boundaryEdge f)
  boundaryEdge_mem : ∀ f i, boundaryEdge f i ∈ R.C.faceBoundary f
  boundaryEdge_vertices : ∀ f i,
    R.C.edgeVertices (boundaryEdge f i) =
      {boundaryVertex f i,
        boundaryVertex f ⟨(i.val + 1) % R.C.faceDegree f,
          Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 3)
            (R.C.faceDegree_three_le f))⟩}
  across : ((f : R.Face) × Fin (R.C.faceDegree f)) →
    ((f : R.Face) × Fin (R.C.faceDegree f))
  across_involutive : Function.Involutive across
  across_otherFace : ∀ d, (across d).1 ≠ d.1
  across_sameEdge : ∀ d,
    boundaryEdge d.1 d.2 = boundaryEdge (across d).1 (across d).2

abbrev FaceDart := (f : R.Face) × Fin (R.C.faceDegree f)

def faceIndex (f : R.Face) (i : Fin (R.C.faceDegree f)) :
    Fin (R.faceDarts f).length :=
  ⟨i.val, by
    simpa [C, toBlueCellulation, BlueCellulation.faceDegree, faceBoundary] using i.isLt⟩

def boundaryDart (d : R.FaceDart) : G.Dart :=
  (R.faceDarts d.1).get (R.faceIndex d.1 d.2)

theorem boundaryDart_mem (d : R.FaceDart) :
    R.boundaryDart d ∈ R.faceDarts d.1 := by
  exact List.get_mem _ _

theorem faceOf_boundaryDart (d : R.FaceDart) :
    R.faceOf (R.boundaryDart d) = d.1 :=
  (R.faceOf_eq_iff_mem d.1 _).mpr (R.boundaryDart_mem d)

theorem boundaryDart_injective : Function.Injective R.boundaryDart := by
  rintro ⟨f, i⟩ ⟨g, j⟩ h
  have hfg : f = g := by
    have := congrArg R.faceOf h
    simpa only [R.faceOf_boundaryDart] using this
  subst g
  have hij : R.faceIndex f i = R.faceIndex f j :=
    (R.faceDarts_nodup f).injective_get h
  have hv : i.val = j.val := by
    simpa [faceIndex] using congrArg Fin.val hij
  cases i with
  | mk iv ih =>
    cases j with
    | mk jv jh =>
      cases hv
      rfl

theorem boundaryDart_surjective : Function.Surjective R.boundaryDart := by
  intro d
  have hd : d ∈ R.faceDarts (R.faceOf d) :=
    (R.faceOf_eq_iff_mem (R.faceOf d) d).mp rfl
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  let j : Fin (R.C.faceDegree (R.faceOf d)) :=
    ⟨i.val, by
      simpa [C, toBlueCellulation, BlueCellulation.faceDegree, faceBoundary] using i.isLt⟩
  refine ⟨⟨R.faceOf d, j⟩, ?_⟩
  simpa [boundaryDart, faceIndex, j] using hi

noncomputable def boundaryDartEquiv : R.FaceDart ≃ G.Dart :=
  Equiv.ofBijective R.boundaryDart
    ⟨R.boundaryDart_injective, R.boundaryDart_surjective⟩

@[simp] theorem boundaryDartEquiv_apply (d : R.FaceDart) :
    R.boundaryDartEquiv d = R.boundaryDart d := rfl

def boundaryVertex (f : R.Face) (i : Fin (R.C.faceDegree f)) : V :=
  (R.boundaryDart ⟨f, i⟩).fst

def boundaryEdge (f : R.Face) (i : Fin (R.C.faceDegree f)) : R.Edge :=
  R.dartEdge (R.boundaryDart ⟨f, i⟩)

theorem boundaryVertex_injective (f : R.Face) :
    Function.Injective (R.boundaryVertex f) := by
  intro i j h
  have hd : R.boundaryDart ⟨f, i⟩ = R.boundaryDart ⟨f, j⟩ := by
    apply R.face_vertex_injective f.1 f.2
    · exact (R.mem_faceDarts_iff f _).mp (R.boundaryDart_mem ⟨f, i⟩)
    · exact (R.mem_faceDarts_iff f _).mp (R.boundaryDart_mem ⟨f, j⟩)
    · exact h
  have hij : R.faceIndex f i = R.faceIndex f j :=
    (R.faceDarts_nodup f).injective_get hd
  apply Fin.ext
  simpa [faceIndex] using congrArg Fin.val hij

theorem boundaryEdge_injective (f : R.Face) :
    Function.Injective (R.boundaryEdge f) := by
  intro i j h
  have hd : R.boundaryDart ⟨f, i⟩ = R.boundaryDart ⟨f, j⟩ := by
    apply R.face_edge_injective f.1 f.2
    · exact (R.mem_faceDarts_iff f _).mp (R.boundaryDart_mem ⟨f, i⟩)
    · exact (R.mem_faceDarts_iff f _).mp (R.boundaryDart_mem ⟨f, j⟩)
    · exact congrArg Subtype.val h
  have hij : R.faceIndex f i = R.faceIndex f j :=
    (R.faceDarts_nodup f).injective_get hd
  apply Fin.ext
  simpa [faceIndex] using congrArg Fin.val hij

theorem boundaryEdge_mem (f : R.Face) (i : Fin (R.C.faceDegree f)) :
    R.boundaryEdge f i ∈ R.C.faceBoundary f := by
  change R.dartEdge (R.boundaryDart ⟨f, i⟩) ∈
    (R.faceDarts f).map R.dartEdge
  exact List.mem_map.mpr ⟨_, R.boundaryDart_mem ⟨f, i⟩, rfl⟩

theorem edgeVertices_dartEdge (d : G.Dart) :
    R.edgeVertices (R.dartEdge d) = {d.fst, d.snd} := by
  exact Sym2.toFinset_mk_eq

theorem perm_fst (d : G.Dart) : (R.perm d).fst = d.snd := by
  change (R.rotation (d.symm)).fst = d.snd
  rw [R.rotation_source]
  rfl

def faceSucc (f : R.Face) (i : Fin (R.C.faceDegree f)) :
    Fin (R.C.faceDegree f) :=
  ⟨(i.val + 1) % R.C.faceDegree f,
    Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 3)
      (R.C.faceDegree_three_le f))⟩

theorem boundaryDart_faceSucc (f : R.Face) (i : Fin (R.C.faceDegree f)) :
    R.boundaryDart ⟨f, R.faceSucc f i⟩ =
      R.perm (R.boundaryDart ⟨f, i⟩) := by
  have hdegree : R.C.faceDegree f = (R.faceDarts f).length := by
    simp [C, toBlueCellulation, BlueCellulation.faceDegree, faceBoundary]
  have hnext := List.next_getElem (R.faceDarts f) (R.faceDarts_nodup f)
    i.val (by simpa [hdegree] using i.isLt)
  have hmem : R.boundaryDart ⟨f, i⟩ ∈ R.faceDarts f :=
    R.boundaryDart_mem ⟨f, i⟩
  have happ := Equiv.Perm.next_toList_eq_apply R.perm (R.faceBase f)
    (R.boundaryDart ⟨f, i⟩) hmem
  calc
    R.boundaryDart ⟨f, R.faceSucc f i⟩ =
        (R.faceDarts f).next (R.boundaryDart ⟨f, i⟩) hmem := by
      simpa [boundaryDart, faceIndex, faceSucc, hdegree] using hnext.symm
    _ = R.perm (R.boundaryDart ⟨f, i⟩) := happ

theorem boundaryEdge_vertices (f : R.Face) (i : Fin (R.C.faceDegree f)) :
    R.C.edgeVertices (R.boundaryEdge f i) =
      {R.boundaryVertex f i, R.boundaryVertex f (R.faceSucc f i)} := by
  rw [show R.C.edgeVertices = R.edgeVertices from rfl]
  rw [boundaryEdge, R.edgeVertices_dartEdge]
  congr 1
  rw [boundaryVertex, R.boundaryDart_faceSucc, R.perm_fst]

noncomputable def across (d : R.FaceDart) : R.FaceDart :=
  R.boundaryDartEquiv.symm ((R.boundaryDartEquiv d).symm)

@[simp] theorem boundaryDart_across (d : R.FaceDart) :
    R.boundaryDart (R.across d) = (R.boundaryDart d).symm := by
  change R.boundaryDartEquiv (R.boundaryDartEquiv.symm
    ((R.boundaryDartEquiv d).symm)) = (R.boundaryDartEquiv d).symm
  exact R.boundaryDartEquiv.apply_symm_apply _

theorem across_involutive : Function.Involutive R.across := by
  intro d
  apply R.boundaryDart_injective
  rw [R.boundaryDart_across, R.boundaryDart_across]
  exact SimpleGraph.Dart.symm_symm _

theorem across_otherFace (d : R.FaceDart) : (R.across d).1 ≠ d.1 := by
  intro h
  apply R.faceOf_symm_ne (R.boundaryDart d)
  calc
    R.faceOf (R.boundaryDart d).symm =
        R.faceOf (R.boundaryDart (R.across d)) := by
          rw [R.boundaryDart_across]
    _ = (R.across d).1 := R.faceOf_boundaryDart _
    _ = d.1 := h
    _ = R.faceOf (R.boundaryDart d) := (R.faceOf_boundaryDart d).symm

theorem across_sameEdge (d : R.FaceDart) :
    R.boundaryEdge d.1 d.2 =
      R.boundaryEdge (R.across d).1 (R.across d).2 := by
  change R.dartEdge (R.boundaryDart d) =
    R.dartEdge (R.boundaryDart (R.across d))
  rw [R.boundaryDart_across, R.dartEdge_symm]

noncomputable def toBoundaryAcrossData : BoundaryAcrossData R where
  boundaryVertex := R.boundaryVertex
  boundaryEdge := R.boundaryEdge
  boundaryVertex_injective := R.boundaryVertex_injective
  boundaryEdge_injective := R.boundaryEdge_injective
  boundaryEdge_mem := R.boundaryEdge_mem
  boundaryEdge_vertices := by
    intro f i
    exact R.boundaryEdge_vertices f i
  across := R.across
  across_involutive := R.across_involutive
  across_otherFace := R.across_otherFace
  across_sameEdge := R.across_sameEdge

/-- Purely finite extraction: a spherical rotation certificate determines both
the blue cellulation and the indexed boundary/across-edge data used by the
discharging argument. -/
theorem exists_blueCellulation_boundaryAcross :
    ∃ C : BlueCellulation V R.Edge R.Face,
      C = R.C ∧ Nonempty (BoundaryAcrossData R) := by
  exact ⟨R.C, rfl, ⟨R.toBoundaryAcrossData⟩⟩

end SphericalRotationData


/-! ## The consecutive-edge graph of a charted projective arrangement -/

namespace CyclicArrangementGraph

variable {Vertex Line : Type*} [Fintype Vertex] [DecidableEq Vertex]
variable [Fintype Line] [DecidableEq Line]

/-- The unoriented endpoint pairs obtained from cyclically consecutive
vertices on one of the arrangement lines. -/
def edgeSet (vertices : Finset Vertex) (onLine : Vertex → Line → Prop)
    [DecidableRel onLine] (coord : Vertex → ℝ) : Set (Sym2 Vertex) :=
  {e | ∃ l a b, ChartOrder.CyclicConsecutive coord
      (ChartOrder.verticesOn vertices onLine l) a b ∧ e = s(a, b)}

/-- The finite simple graph whose edges are the consecutive pieces of the
charted projective lines. `fromEdgeSet` discards a degenerate loop; for a
non-pencil line arrangement the endpoint-distinctness condition in
`exists_cyclic_successor_edge` shows that no intended edge is discarded. -/
def graph (vertices : Finset Vertex) (onLine : Vertex → Line → Prop)
    [DecidableRel onLine] (coord : Vertex → ℝ) : SimpleGraph Vertex :=
  SimpleGraph.fromEdgeSet (edgeSet vertices onLine coord)

instance (vertices : Finset Vertex) (onLine : Vertex → Line → Prop)
    [DecidableRel onLine] (coord : Vertex → ℝ) :
    DecidableRel (graph vertices onLine coord).Adj := by
  classical
  infer_instance

instance (vertices : Finset Vertex) (onLine : Vertex → Line → Prop)
    [DecidableRel onLine] (coord : Vertex → ℝ) :
    Fintype (graph vertices onLine coord).edgeSet := by
  classical
  infer_instance

theorem adj_of_cyclicConsecutive
    (vertices : Finset Vertex) (onLine : Vertex → Line → Prop)
    [DecidableRel onLine] (coord : Vertex → ℝ)
    {l : Line} {a b : Vertex}
    (hab : ChartOrder.CyclicConsecutive coord
      (ChartOrder.verticesOn vertices onLine l) a b) (hne : a ≠ b) :
    (graph vertices onLine coord).Adj a b := by
  rw [graph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨l, a, b, hab, rfl⟩, hne⟩

theorem cyclicConsecutive_ne_of_two_le_card
    (vertices : Finset Vertex) (onLine : Vertex → Line → Prop)
    [DecidableRel onLine] (coord : Vertex → ℝ)
    (hinj : Set.InjOn coord (vertices : Set Vertex))
    {l : Line} {a b : Vertex}
    (hcard : 2 ≤ (ChartOrder.verticesOn vertices onLine l).card)
    (hab : ChartOrder.CyclicConsecutive coord
      (ChartOrder.verticesOn vertices onLine l) a b) : a ≠ b := by
  rcases hab with hab | ⟨ha, hb, hamax, hbmin⟩
  · exact hab.ne
  · intro hab
    subst b
    have hsub : ChartOrder.verticesOn vertices onLine l ⊆ {a} := by
      intro x hx
      have hcoord : coord x = coord a :=
        le_antisymm (hamax x hx) (hbmin x hx)
      have hxv : x ∈ vertices :=
        (ChartOrder.mem_verticesOn vertices onLine).mp hx |>.1
      have hav : a ∈ vertices :=
        (ChartOrder.mem_verticesOn vertices onLine).mp ha |>.1
      simpa only [Finset.mem_singleton] using hinj hxv hav hcoord
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hc
    omega

/-- Chart order constructs a graph edge starting at every incident vertex,
provided the cyclic successor is never the vertex itself. This is the exact
finite consequence of the non-pencil condition used before the local
rotation at a vertex is introduced. -/
theorem exists_cyclic_successor_edge
    (vertices : Finset Vertex) (onLine : Vertex → Line → Prop)
    [DecidableRel onLine] (coord : Vertex → ℝ)
    {l : Line} {a : Vertex}
    (ha : a ∈ ChartOrder.verticesOn vertices onLine l)
    (hnonsingleton : ∀ b,
      ChartOrder.CyclicConsecutive coord
        (ChartOrder.verticesOn vertices onLine l) a b → a ≠ b) :
    ∃ b, (graph vertices onLine coord).Adj a b ∧
      ChartOrder.CyclicConsecutive coord
        (ChartOrder.verticesOn vertices onLine l) a b := by
  obtain ⟨b, hab⟩ :=
    ChartOrder.exists_cyclicConsecutive_successor coord
      (ChartOrder.verticesOn vertices onLine l) a ha
  exact ⟨b, adj_of_cyclicConsecutive vertices onLine coord hab
    (hnonsingleton b hab), hab⟩

/-- If every represented line contains at least two arrangement vertices,
the separating chart coordinate produces an honest graph edge out of every
incident vertex. This is the graph-extraction statement to which the
homogeneous non-pencil lemma reduces. -/
theorem exists_cyclic_successor_edge_of_two_vertices
    (vertices : Finset Vertex) (onLine : Vertex → Line → Prop)
    [DecidableRel onLine] (coord : Vertex → ℝ)
    (hinj : Set.InjOn coord (vertices : Set Vertex))
    {l : Line} {a : Vertex}
    (ha : a ∈ ChartOrder.verticesOn vertices onLine l)
    (hcard : 2 ≤ (ChartOrder.verticesOn vertices onLine l).card) :
    ∃ b, (graph vertices onLine coord).Adj a b ∧
      ChartOrder.CyclicConsecutive coord
        (ChartOrder.verticesOn vertices onLine l) a b := by
  apply exists_cyclic_successor_edge vertices onLine coord ha
  intro b hab
  exact cyclicConsecutive_ne_of_two_le_card vertices onLine coord
    hinj hcard hab

end CyclicArrangementGraph

end Erdos735.RotationCellulation
