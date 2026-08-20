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

import ErdosProblems.Erdos735.RotationCellulation
import ErdosProblems.Erdos735.SignVectorIncidence

/-!
# Sign-vector boundaries from spherical rotations

This file is the exact bridge between a finite spherical rotation system and
the algebraic sign-vector incidence model. Once graph edges and facial cycles
are identified with `StrictEdge` and `StrictFace`, it transports every field
of `SignVector.BoundaryExtraction`, including the Euler identity.
-/

open Classical
noncomputable section

namespace Erdos735.SignVector

open RotationCellulation

universe u

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [Fintype G.edgeSet]

/-- The exact compatibility between a topological rotation realization and
the algebraic sign-vector faces and edges. The geometric construction only
has to identify supporting open edges and chambers; all cellulation fields
are then transported without further topology. -/
structure RotationRealization (n : I → Vec3) (hn : ∀ i, n i ≠ 0) where
  rotation : SphericalRotationData G
  edgeEquiv : rotation.Edge ≃ StrictEdge n
  faceEquiv : rotation.Face ≃ StrictFace n
  faceEdge_iff : ∀ f e,
    e ∈ faceEdges n f ↔
      edgeEquiv.symm e ∈ rotation.C.faceBoundary (faceEquiv.symm f)

namespace RotationRealization

variable {n : I → Vec3} {hn : ∀ i, n i ≠ 0}
variable (X : RotationRealization (G := G) n hn)

/-- The arrangement line supporting an open sign-vector edge. -/
def strictEdgeOwner (e : StrictEdge n) : I := e.1.1

/-- A strict face has at most one open edge on each arrangement line.  Indeed,
the signs on every other line are forced by the face sign vector. -/
theorem strictEdgeOwner_injective_on_faceEdges (f : StrictFace n) :
    Set.InjOn strictEdgeOwner (faceEdges n f : Set (StrictEdge n)) := by
  rintro ⟨⟨i, s⟩, hs⟩ hi ⟨⟨j, t⟩, ht⟩ hj hij
  dsimp [strictEdgeOwner] at hij
  subst j
  apply Subtype.ext
  change (⟨i, s⟩ : EdgeCode I) = ⟨i, t⟩
  congr 1
  funext k
  have his := (mem_faceEdges_iff n f ⟨⟨i, s⟩, hs⟩).mp hi k
  have hit := (mem_faceEdges_iff n f ⟨⟨i, t⟩, ht⟩).mp hj k
  exact his.symm.trans hit

def edgeVertices (e : StrictEdge n) : Finset V :=
  X.rotation.C.edgeVertices (X.edgeEquiv.symm e)

def vertexEdges (v : V) : Finset (StrictEdge n) :=
  (X.rotation.C.vertexEdges v).map X.edgeEquiv.toEmbedding

def faceBoundary (f : StrictFace n) : List (StrictEdge n) :=
  (X.rotation.C.faceBoundary (X.faceEquiv.symm f)).map X.edgeEquiv

theorem vertexEdge_iff (v : V) (e : StrictEdge n) :
    e ∈ X.vertexEdges v ↔ v ∈ X.edgeVertices e := by
  simp only [vertexEdges, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨e', he', heq⟩
    subst e
    simpa [edgeVertices] using
      (X.rotation.C.vertexEdge_iff v e').mp he'
  · intro he
    refine ⟨X.edgeEquiv.symm e, ?_, X.edgeEquiv.apply_symm_apply e⟩
    simpa [edgeVertices] using X.rotation.C.vertexEdge_iff v (X.edgeEquiv.symm e) |>.mpr he

theorem faceBoundary_nodup (f : StrictFace n) :
    (X.faceBoundary f).Nodup := by
  exact (X.rotation.C.faceBoundary_nodup (X.faceEquiv.symm f)).map
    X.edgeEquiv.injective

theorem faceBoundary_toFinset (f : StrictFace n) :
    (X.faceBoundary f).toFinset = faceEdges n f := by
  ext e
  rw [List.mem_toFinset, X.faceEdge_iff]
  rw [faceBoundary, List.mem_map]
  constructor
  · rintro ⟨e', he', heq⟩
    subst e
    simpa using he'
  · intro he
    exact ⟨X.edgeEquiv.symm e, he, X.edgeEquiv.apply_symm_apply e⟩

/-- The supporting-line label is injective along the cyclic edge boundary of
every transported face. -/
theorem strictEdgeOwner_injective_on_faceBoundary (f : StrictFace n) :
    Set.InjOn strictEdgeOwner {e | e ∈ X.faceBoundary f} := by
  apply (strictEdgeOwner_injective_on_faceEdges (n := n) f).mono
  intro e he
  rw [← X.faceBoundary_toFinset f]
  simpa using he

/-- Indexed form of `strictEdgeOwner_injective_on_faceBoundary`, matching the
boundary indexing used by the discharging data. -/
theorem boundaryOwner_injective (f : StrictFace n) :
    Function.Injective (fun i : Fin (X.faceBoundary f).length ↦
      strictEdgeOwner ((X.faceBoundary f).get i)) := by
  intro i j hij
  have hedge : (X.faceBoundary f).get i = (X.faceBoundary f).get j :=
    strictEdgeOwner_injective_on_faceBoundary X f
      (List.get_mem _ _) (List.get_mem _ _) hij
  exact (X.faceBoundary_nodup f).injective_get hedge

/-- A compatible rotation realization supplies the complete
`SignVector.BoundaryExtraction`, including the spherical Euler identity. -/
noncomputable def toBoundaryExtraction : BoundaryExtraction n hn where
  Vertex := V
  instFintypeVertex := inferInstance
  instDecidableEqVertex := inferInstance
  blueMultiplicity := X.rotation.blueMultiplicity
  edgeVertices := X.edgeVertices
  vertexEdges := X.vertexEdges
  vertexEdge_iff := X.vertexEdge_iff
  edgeVertices_card := fun e ↦ X.rotation.C.edgeVertices_card (X.edgeEquiv.symm e)
  vertexEdges_card := by
    intro v
    rw [vertexEdges, Finset.card_map]
    exact X.rotation.C.vertexEdges_card v
  blueMultiplicity_two_le := X.rotation.multiplicity_two_le
  faceBoundary := X.faceBoundary
  faceBoundary_nodup := X.faceBoundary_nodup
  faceBoundary_toFinset := X.faceBoundary_toFinset
  faceDegree_three_le := by
    intro f
    simpa [faceBoundary] using
      X.rotation.C.faceDegree_three_le (X.faceEquiv.symm f)
  euler_sphere := by
    have he := Fintype.card_congr X.edgeEquiv
    have hf := Fintype.card_congr X.faceEquiv
    rw [← he, ← hf]
    exact X.rotation.C.euler_sphere

/-- The sign-vector cellulation obtained by transporting a spherical
rotation realization. -/
abbrev strictC : BlueCellulation V (StrictEdge n) (StrictFace n) :=
  X.toBoundaryExtraction.toBlueCellulation n hn

theorem strictC_faceDegree_eq (f : StrictFace n) :
    X.strictC.faceDegree f =
      X.rotation.C.faceDegree (X.faceEquiv.symm f) := by
  simp [strictC, toBoundaryExtraction, BoundaryExtraction.toBlueCellulation,
    BlueCellulation.faceDegree, faceBoundary,
    RotationCellulation.SphericalRotationData.C,
    RotationCellulation.SphericalRotationData.toBlueCellulation]

/-- Transport between an index of a sign-vector face boundary and the
corresponding index in the original spherical rotation face. -/
noncomputable def faceIndexEquiv (f : StrictFace n) :
    Fin (X.strictC.faceDegree f) ≃
      Fin (X.rotation.C.faceDegree (X.faceEquiv.symm f)) where
  toFun i := ⟨i.val, by rw [← X.strictC_faceDegree_eq f]; exact i.isLt⟩
  invFun i := ⟨i.val, by rw [X.strictC_faceDegree_eq f]; exact i.isLt⟩
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl

abbrev StrictFaceDart :=
  (f : StrictFace n) × Fin (X.strictC.faceDegree f)

/-- Dependent equivalence between transported boundary darts and the original
rotation-system boundary darts. -/
noncomputable def faceDartEquiv : X.StrictFaceDart ≃ X.rotation.FaceDart :=
  Equiv.sigmaCongr X.faceEquiv.symm (fun f ↦ X.faceIndexEquiv f)

def boundaryVertex (f : StrictFace n) (i : Fin (X.strictC.faceDegree f)) : V :=
  X.rotation.boundaryVertex (X.faceEquiv.symm f) (X.faceIndexEquiv f i)

def boundaryEdge (f : StrictFace n) (i : Fin (X.strictC.faceDegree f)) : StrictEdge n :=
  X.edgeEquiv (X.rotation.boundaryEdge (X.faceEquiv.symm f) (X.faceIndexEquiv f i))

/-- Across-edge pairing transported to sign-vector faces and edges. -/
noncomputable def across (d : X.StrictFaceDart) : X.StrictFaceDart :=
  X.faceDartEquiv.symm (X.rotation.across (X.faceDartEquiv d))

@[simp] theorem faceDartEquiv_across (d : X.StrictFaceDart) :
    X.faceDartEquiv (X.across d) = X.rotation.across (X.faceDartEquiv d) := by
  simp [across]

theorem boundaryVertex_injective (f : StrictFace n) :
    Function.Injective (X.boundaryVertex f) := by
  intro i j hij
  apply X.faceIndexEquiv f |>.injective
  exact X.rotation.boundaryVertex_injective (X.faceEquiv.symm f) hij

theorem boundaryEdge_injective (f : StrictFace n) :
    Function.Injective (X.boundaryEdge f) := by
  intro i j hij
  apply X.faceIndexEquiv f |>.injective
  apply X.rotation.boundaryEdge_injective (X.faceEquiv.symm f)
  exact X.edgeEquiv.injective hij

theorem boundaryEdge_mem (f : StrictFace n) (i : Fin (X.strictC.faceDegree f)) :
    X.boundaryEdge f i ∈ X.strictC.faceBoundary f := by
  change X.edgeEquiv _ ∈ X.faceBoundary f
  rw [faceBoundary, List.mem_map]
  exact ⟨_, X.rotation.boundaryEdge_mem _ _, rfl⟩

def strictFaceSucc (f : StrictFace n) (i : Fin (X.strictC.faceDegree f)) :
    Fin (X.strictC.faceDegree f) :=
  ⟨(i.val + 1) % X.strictC.faceDegree f,
    Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0 < 3)
      (X.strictC.faceDegree_three_le f))⟩

theorem faceIndexEquiv_strictFaceSucc (f : StrictFace n)
    (i : Fin (X.strictC.faceDegree f)) :
    X.faceIndexEquiv f (X.strictFaceSucc f i) =
      X.rotation.faceSucc (X.faceEquiv.symm f) (X.faceIndexEquiv f i) := by
  apply Fin.ext
  simp only [faceIndexEquiv, strictFaceSucc,
    RotationCellulation.SphericalRotationData.faceSucc]
  exact congrArg (fun k ↦ (i.val + 1) % k) (X.strictC_faceDegree_eq f)

theorem boundaryEdge_vertices (f : StrictFace n) (i : Fin (X.strictC.faceDegree f)) :
    X.strictC.edgeVertices (X.boundaryEdge f i) =
      {X.boundaryVertex f i, X.boundaryVertex f (X.strictFaceSucc f i)} := by
  change X.edgeVertices (X.edgeEquiv _) = _
  simp only [edgeVertices, X.edgeEquiv.symm_apply_apply]
  rw [X.rotation.boundaryEdge_vertices]
  congr 1
  rw [boundaryVertex, X.faceIndexEquiv_strictFaceSucc]

theorem across_involutive : Function.Involutive X.across := by
  intro d
  apply X.faceDartEquiv.injective
  simp only [across, Equiv.apply_symm_apply]
  rw [X.rotation.across_involutive]

theorem across_otherFace (d : X.StrictFaceDart) : (X.across d).1 ≠ d.1 := by
  intro h
  apply X.rotation.across_otherFace (X.faceDartEquiv d)
  calc
    (X.rotation.across (X.faceDartEquiv d)).1 =
        (X.faceDartEquiv (X.across d)).1 :=
      congrArg Sigma.fst (X.faceDartEquiv_across d).symm
    _ = X.faceEquiv.symm (X.across d).1 := rfl
    _ = X.faceEquiv.symm d.1 := congrArg X.faceEquiv.symm h
    _ = (X.faceDartEquiv d).1 := rfl

theorem across_sameEdge (d : X.StrictFaceDart) :
    X.boundaryEdge d.1 d.2 = X.boundaryEdge (X.across d).1 (X.across d).2 := by
  have hsrc := X.rotation.across_sameEdge (X.faceDartEquiv d)
  rw [← X.faceDartEquiv_across d] at hsrc
  exact congrArg X.edgeEquiv hsrc

/-- Supporting arrangement lines are pairwise distinct around a transported
face boundary. -/
theorem indexedBoundaryOwner_injective (f : StrictFace n) :
    Function.Injective (fun i ↦ strictEdgeOwner (X.boundaryEdge f i)) := by
  intro i j hij
  apply X.boundaryEdge_injective f
  apply strictEdgeOwner_injective_on_faceEdges (n := n) f
  · have hi := X.boundaryEdge_mem f i
    change X.boundaryEdge f i ∈ X.faceBoundary f at hi
    rw [← X.faceBoundary_toFinset f]
    simpa using hi
  · have hj := X.boundaryEdge_mem f j
    change X.boundaryEdge f j ∈ X.faceBoundary f at hj
    rw [← X.faceBoundary_toFinset f]
    simpa using hj
  · exact hij

theorem boundaryEdge_mem_faceEdges (f : StrictFace n)
    (i : Fin (X.strictC.faceDegree f)) :
    X.boundaryEdge f i ∈ faceEdges n f := by
  have hi := X.boundaryEdge_mem f i
  change X.boundaryEdge f i ∈ X.faceBoundary f at hi
  rw [← X.faceBoundary_toFinset f]
  simpa using hi

/-- Crossing a transported boundary edge reaches exactly the sign-vector
chamber obtained by flipping the sign of its supporting line.  Thus the
topological across pairing and the algebraic two-face incidence coincide. -/
theorem across_face_eq_edgeFace_flip (d : X.StrictFaceDart) :
    (X.across d).1 = edgeFace n hn (X.boundaryEdge d.1 d.2)
      (!(d.1.1 (strictEdgeOwner (X.boundaryEdge d.1 d.2)))) := by
  let e := X.boundaryEdge d.1 d.2
  let g := (X.across d).1
  have hf : FaceEdgeIncident n d.1 e :=
    (mem_faceEdges_iff n d.1 e).mp (X.boundaryEdge_mem_faceEdges d.1 d.2)
  have hgmem : e ∈ faceEdges n g := by
    have hm := X.boundaryEdge_mem_faceEdges (X.across d).1 (X.across d).2
    change X.boundaryEdge (X.across d).1 (X.across d).2 ∈ faceEdges n g at hm
    simpa only [e, X.across_sameEdge d] using hm
  have hg : FaceEdgeIncident n g e :=
    (mem_faceEdges_iff n g e).mp hgmem
  have hfeq := eq_edgeFace_of_incident n hn d.1 e hf
  have hgeq := eq_edgeFace_of_incident n hn g e hg
  have hsign : g.1 e.1.1 = !(d.1.1 e.1.1) := by
    by_contra h
    have bool_same : ∀ a b : Bool, a ≠ !b → a = b := by decide
    have hs : g.1 e.1.1 = d.1.1 e.1.1 := bool_same _ _ h
    apply X.across_otherFace d
    change g = d.1
    rw [hgeq, hfeq, hs]
  change g = edgeFace n hn e (!(d.1.1 e.1.1))
  rw [hgeq, hsign]

/-- The boundary/across fragment of the ABKPR data, now indexed directly by
strict sign-vector faces and edges. -/
structure TransportedBoundaryAcrossData where
  boundaryVertex : ∀ f, Fin (X.strictC.faceDegree f) → V
  boundaryEdge : ∀ f, Fin (X.strictC.faceDegree f) → StrictEdge n
  boundaryVertex_injective : ∀ f, Function.Injective (boundaryVertex f)
  boundaryEdge_injective : ∀ f, Function.Injective (boundaryEdge f)
  boundaryOwner_injective : ∀ f,
    Function.Injective (fun i ↦ strictEdgeOwner (boundaryEdge f i))
  boundaryEdge_mem : ∀ f i, boundaryEdge f i ∈ X.strictC.faceBoundary f
  boundaryEdge_vertices : ∀ f i,
    X.strictC.edgeVertices (boundaryEdge f i) =
      {boundaryVertex f i, boundaryVertex f (X.strictFaceSucc f i)}
  across : X.StrictFaceDart → X.StrictFaceDart
  across_involutive : Function.Involutive across
  across_otherFace : ∀ d, (across d).1 ≠ d.1
  across_sameEdge : ∀ d,
    boundaryEdge d.1 d.2 = boundaryEdge (across d).1 (across d).2

/-- Complete checked transport of the rotation-system boundary/across fields
to the sign-vector cellulation. -/
noncomputable def toTransportedBoundaryAcrossData :
    TransportedBoundaryAcrossData X where
  boundaryVertex := X.boundaryVertex
  boundaryEdge := X.boundaryEdge
  boundaryVertex_injective := X.boundaryVertex_injective
  boundaryEdge_injective := X.boundaryEdge_injective
  boundaryOwner_injective := X.indexedBoundaryOwner_injective
  boundaryEdge_mem := X.boundaryEdge_mem
  boundaryEdge_vertices := X.boundaryEdge_vertices
  across := X.across
  across_involutive := X.across_involutive
  across_otherFace := X.across_otherFace
  across_sameEdge := X.across_sameEdge

end RotationRealization
end Erdos735.SignVector
