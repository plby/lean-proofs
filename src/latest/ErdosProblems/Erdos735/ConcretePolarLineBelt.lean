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

import ErdosProblems.Erdos735.ConcreteStrictEdgeCyclic
import ErdosProblems.Erdos735.LeviSignVector

/-!
# The two-sided cyclic belt of faces along one literal polar line

For an arbitrary sign-vector arrangement, a face incident with a selected
owner `s` contains a unique strict edge owned by `s`, and is one of the two
sign extensions of that edge.  Thus incident faces are exactly

`(strict edges owned by s) × Bool`.

For the literal polar arrangement, the owner-preserving edge realization
identifies a strict edge with a lifted cyclic interval in the genuine
projective one-skeleton.  Restricting that equivalence to the owner fiber
therefore gives the promised belt enumeration

`(lifted cyclic intervals on s) × Bool ≃ (faces incident with s)`.

The final theorems in this file turn an exhaustive statement about all
triangular incident faces into a pointwise statement on these literal belt
slots.  This isolates the remaining Stage-4 geometry: every non-end belt
slot must be recognized as the face across the opposite edge of a helping
or bad quadrangle, and hence excluded from being triangular.
-/

open Classical
noncomputable section

namespace Erdos735

namespace SignVectorArrangement

open SignVector

universe uI

variable {I : Type uI} [Fintype I] [DecidableEq I]

/-- Switching to the antipodal lift of an open projective edge and
switching its side produces the antipodal face.  Thus the four spherical
slots over one projective interval form exactly two antipodal face
orbits. -/
theorem edgeFace_antipodalEdge_flip {n : I → Vec3}
    (hn : ∀ i, n i ≠ 0) (e : StrictEdge n) (b : Bool) :
    edgeFace n hn (antipodalEdge n e) b =
      antipodalStrictFace (edgeFace n hn e (!b)) := by
  apply Subtype.ext
  funext j
  by_cases hj : j = e.1.1
  · subst j
    simp only [edgeFace_sign, antipodalStrictFace_sign, antipodalSign]
    calc
      extendEdgeSign (antipodalEdge n e).1 b e.1.1 =
          extendEdgeSign (antipodalEdge n e).1 b
            (antipodalEdge n e).1.1 := by
              rw [antipodalEdge_support]
      _ = b := extendEdgeSign_support _ _
      _ = !(!b) := by simp
      _ = !(extendEdgeSign e.1 (!b) e.1.1) := by
        rw [extendEdgeSign_support]
  · have hjanti : j ≠ (antipodalEdge n e).1.1 := by simpa
    simp only [edgeFace_sign, antipodalStrictFace_sign, antipodalSign]
    rw [extendEdgeSign_other _ _ hjanti, extendEdgeSign_other _ _ hj]
    rfl

/-- The face on a chosen side of a strict edge owned by `s`. -/
def lineBeltFace {n : I → Vec3} (hn : ∀ i, n i ≠ 0) (s : I)
    (x : SignVector.StrictEdgeOn n s × Bool) : StrictFace n :=
  edgeFace n hn x.1.1 x.2

/-- Every belt face is incident with its selected owner. -/
theorem lineBeltFace_incident {n : I → Vec3} (hn : ∀ i, n i ≠ 0)
    (s : I) (x : SignVector.StrictEdgeOn n s × Bool) :
    LineFaceIncident n s (lineBeltFace hn s x) := by
  refine ⟨x.1.1, ?_, x.1.2⟩
  rw [mem_faceEdges_iff]
  exact faceEdgeIncident_edgeFace n hn x.1.1 x.2

/-- Different owner-edge/side pairs give different incident faces. -/
theorem lineBeltFace_injective {n : I → Vec3} (hn : ∀ i, n i ≠ 0)
    (s : I) : Function.Injective (lineBeltFace hn s) := by
  rintro ⟨e, b⟩ ⟨e', b'⟩ hface
  have heMem : e.1 ∈ faceEdges n (lineBeltFace hn s (e, b)) := by
    rw [mem_faceEdges_iff]
    exact faceEdgeIncident_edgeFace n hn e.1 b
  have he'Mem : e'.1 ∈ faceEdges n (lineBeltFace hn s (e, b)) := by
    rw [hface, mem_faceEdges_iff]
    exact faceEdgeIncident_edgeFace n hn e'.1 b'
  have he : e.1 = e'.1 := strictEdge_eq_of_faceEdges_of_owner_eq
    heMem he'Mem (e.2.trans e'.2.symm)
  have hb : b = b' := by
    apply edgeFace_injective n hn e.1
    simpa only [lineBeltFace, he] using hface
  exact Prod.ext (Subtype.ext he) hb

/-- Every face incident with `s` occurs in exactly one belt slot. -/
theorem lineBeltFace_surjective {n : I → Vec3} (hn : ∀ i, n i ≠ 0)
    (s : I) : Function.Surjective
      (fun x : SignVector.StrictEdgeOn n s × Bool ↦
        (⟨lineBeltFace hn s x, lineBeltFace_incident hn s x⟩ :
          {f : StrictFace n // LineFaceIncident n s f})) := by
  rintro ⟨f, hf⟩
  obtain ⟨e, heFace, heOwner⟩ := hf
  let x : SignVector.StrictEdgeOn n s × Bool :=
    (⟨e, heOwner⟩, f.1 e.1.1)
  refine ⟨x, Subtype.ext ?_⟩
  change edgeFace n hn e (f.1 e.1.1) = f
  exact (eq_edgeFace_of_incident n hn f e
    ((mem_faceEdges_iff n f e).mp heFace)).symm

/-- Abstract two-sided belt enumeration on a fixed sign-vector owner. -/
noncomputable def lineFaceBeltEquiv {n : I → Vec3} (hn : ∀ i, n i ≠ 0)
    (s : I) :
    SignVector.StrictEdgeOn n s × Bool ≃
      {f : StrictFace n // LineFaceIncident n s f} :=
  Equiv.ofBijective
    (fun x ↦ ⟨lineBeltFace hn s x, lineBeltFace_incident hn s x⟩)
    ⟨fun _ _ h ↦ lineBeltFace_injective hn s (Subtype.ext_iff.mp h),
      lineBeltFace_surjective hn s⟩

@[simp] theorem lineFaceBeltEquiv_apply_val {n : I → Vec3}
    (hn : ∀ i, n i ≠ 0) (s : I)
    (x : SignVector.StrictEdgeOn n s × Bool) :
    (lineFaceBeltEquiv hn s x).1 = lineBeltFace hn s x := rfl

/-- Checking all triangular incident faces is equivalent to checking every
slot in the owner-edge/side belt. -/
theorem all_incident_triangles_iff_all_lineBelt_slots
    {n : I → Vec3} (hn : ∀ i, n i ≠ 0) (s : I)
    (endpoint : Fin 2 → StrictFace n) :
    (∀ f : StrictFace n, LineFaceIncident n s f →
        strictFaceDegree n f = 3 → ∃ k, endpoint k = f) ↔
      ∀ x : SignVector.StrictEdgeOn n s × Bool,
        strictFaceDegree n (lineBeltFace hn s x) = 3 →
          ∃ k, endpoint k = lineBeltFace hn s x := by
  constructor
  · intro h x hx
    exact h _ (lineBeltFace_incident hn s x) hx
  · intro h f hf htri
    obtain ⟨x, hx⟩ := (lineFaceBeltEquiv hn s).surjective ⟨f, hf⟩
    have hxval : lineBeltFace hn s x = f := congrArg Subtype.val hx
    obtain ⟨k, hk⟩ := h x (by simpa [hxval] using htri)
    exact ⟨k, hk.trans hxval⟩

/-- Projectively correct belt reduction: the two selected endpoint
triangles stand for their complete antipodal orbits. -/
theorem all_incident_triangles_iff_all_lineBelt_slots_or_antipode
    {n : I → Vec3} (hn : ∀ i, n i ≠ 0) (s : I)
    (endpoint : Fin 2 → StrictFace n) :
    (∀ f : StrictFace n, LineFaceIncident n s f →
        strictFaceDegree n f = 3 →
          ∃ k, endpoint k = f ∨ antipodalStrictFace (endpoint k) = f) ↔
      ∀ x : SignVector.StrictEdgeOn n s × Bool,
        strictFaceDegree n (lineBeltFace hn s x) = 3 →
          ∃ k, endpoint k = lineBeltFace hn s x ∨
            antipodalStrictFace (endpoint k) = lineBeltFace hn s x := by
  constructor
  · intro h x hx
    exact h _ (lineBeltFace_incident hn s x) hx
  · intro h f hf htri
    obtain ⟨x, hx⟩ := (lineFaceBeltEquiv hn s).surjective ⟨f, hf⟩
    have hxval : lineBeltFace hn s x = f := congrArg Subtype.val hx
    obtain ⟨k, hk | hk⟩ := h x (by simpa [hxval] using htri)
    · exact ⟨k, Or.inl (hk.trans hxval)⟩
    · exact ⟨k, Or.inr (hk.trans hxval)⟩

end SignVectorArrangement

namespace ConcretePolarLineBelt

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement
open SignVector.ProjectiveEdgeEndpointEquiv
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B
abbrev Vertex (B : Finset Point) := ProjectiveBoundaryExtraction.Vertex B

variable (B : Finset Point) {a b c : Point}
variable (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
variable [Nonempty (Line B)]

/-- The two antipodal strict-edge lifts have disjoint sets of literal
oriented endpoints.  A common oriented endpoint would weakly realize both
an edge sign sector and its opposite, hence would be orthogonal to every
normal; spanning then forces its nonzero representative to vanish. -/
theorem concreteEdgeVertices_antipodal_disjoint
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)
    (e : StrictEdge (normals B)) (v : OrientedVertex B)
    (hv : v ∈ ConcretePolarEdgeVertices.concreteEdgeVertices hspan e)
    (hvanti : v ∈ ConcretePolarEdgeVertices.concreteEdgeVertices hspan
      (antipodalEdge (normals B) e)) : False := by
  have hw := ConcretePolarEdgeVertices.concreteEdgeVertex_weaklyRealizes_restriction
    hspan e v hv
  have hwanti :=
    ConcretePolarEdgeVertices.concreteEdgeVertex_weaklyRealizes_restriction
      hspan (antipodalEdge (normals B) e) v hvanti
  have hall : ∀ i, normals B i ⬝ᵥ orientedRep v = 0 := by
    intro i
    by_cases hi : i = e.1.1
    · subst i
      have hinc := ConcretePolarEdgeVertices.concreteEdgeVertex_on_support
        hspan e v hv
      apply (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).mp
      rw [orientedRep_projectivization]
      exact hinc
    · let j : {j : Line B // j ≠ e.1.1} := ⟨i, hi⟩
      have h₁ := hw j
      have h₂ := hwanti j
      change 0 ≤ signed (e.1.2 j)
        (normals B i ⬝ᵥ orientedRep v) at h₁
      change 0 ≤ signed (!(e.1.2 j))
        (normals B i ⬝ᵥ orientedRep v) at h₂
      cases hs : e.1.2 j <;>
        simp [signed, hs] at h₁ h₂ <;> linarith
  let F : Vec3 →ₗ[ℝ] ℝ :=
    { toFun := fun z ↦ z ⬝ᵥ orientedRep v
      map_add' := by intro x y; simp [add_dotProduct]
      map_smul' := by intro r x; simp [smul_dotProduct] }
  have hrange : Set.range (normals B) ⊆ F.ker := by
    rintro z ⟨i, rfl⟩
    exact hall i
  have hle : Submodule.span ℝ (Set.range (normals B)) ≤ F.ker :=
    (Submodule.span_le).2 hrange
  rw [hspan] at hle
  have hself : orientedRep v ⬝ᵥ orientedRep v = 0 := hle (by simp)
  exact orientedRep_ne_zero v (dotProduct_self_eq_zero.mp hself)

/-- Equality of the underlying projective cyclic interval determines a
strict sign-vector edge up to antipode.  This is the precise fact needed to
pass from projective belt exhaustion to the two spherical sheets. -/
theorem eq_or_antipodal_of_liftedCyclic_base_eq
    (pick : OtherLineChoice (Line B))
    (e e' : StrictEdge (normals B))
    (hbase :
      (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1 =
        (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e').1) :
    e' = e ∨ e' = antipodalEdge (normals B) e := by
  have hnorm : normalizeProjectiveEdge pick (normals B) e =
      normalizeProjectiveEdge pick (normals B) e' := by
    exact (projectiveStrictEdgeCyclicEquiv B ha hb hc hncol pick).injective hbase
  by_cases he : IsPositiveEdgeRepresentative pick (normals B) e
  · by_cases he' : IsPositiveEdgeRepresentative pick (normals B) e'
    · left
      have hv := congrArg Subtype.val hnorm
      simpa [normalizeProjectiveEdge, he, he'] using hv.symm
    · right
      have hv := congrArg Subtype.val hnorm
      have hea : e = antipodalEdge (normals B) e' := by
        simpa [normalizeProjectiveEdge, he, he'] using hv
      have := congrArg (antipodalEdge (normals B)) hea
      simpa using this.symm
  · by_cases he' : IsPositiveEdgeRepresentative pick (normals B) e'
    · right
      have hv := congrArg Subtype.val hnorm
      simpa [normalizeProjectiveEdge, he, he'] using hv.symm
    · left
      have hv := congrArg Subtype.val hnorm
      have haa : antipodalEdge (normals B) e =
          antipodalEdge (normals B) e' := by
        simpa [normalizeProjectiveEdge, he, he'] using hv
      have := congrArg (antipodalEdge (normals B)) haa
      simpa using this.symm

/-- Equality of projective intervals upgrades to equality of spherical
strict edges as soon as the two edges share one literal oriented endpoint.
The antipodal alternative has disjoint oriented endpoint sets. -/
theorem strictEdge_eq_of_liftedCyclic_base_eq_of_common_orientedVertex
    (pick : OtherLineChoice (Line B))
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)
    (e e' : StrictEdge (normals B))
    (hbase :
      (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1 =
        (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e').1)
    (v : OrientedVertex B)
    (hv : v ∈ ConcretePolarEdgeVertices.concreteEdgeVertices hspan e)
    (hv' : v ∈ ConcretePolarEdgeVertices.concreteEdgeVertices hspan e') :
    e' = e := by
  rcases eq_or_antipodal_of_liftedCyclic_base_eq
      B ha hb hc hncol pick e e' hbase with heq | heq
  · exact heq
  · exfalso
    apply concreteEdgeVertices_antipodal_disjoint (B := B) hspan e v hv
    rwa [← heq]

/-- Local projective-slot classifier.  If one face at a reference strict
edge is `endpoint` and the other face is not triangular, then every
triangular face carried by either lift of the same projective interval is
`endpoint` or its antipode. -/
theorem triangular_face_eq_or_antipodal_of_liftedCyclic_base_eq
    (pick : OtherLineChoice (Line B))
    (e e' : StrictEdge (normals B))
    (endpoint f : StrictFace (normals B))
    (hendpoint : FaceEdgeIncident (normals B) endpoint e)
    (hf : FaceEdgeIncident (normals B) f e')
    (hbase :
      (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1 =
        (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e').1)
    (hother : strictFaceDegree (normals B)
      (edgeFace (normals B) (normals_ne_zero B) e
        (!(endpoint.1 e.1.1))) ≠ 3)
    (htri : strictFaceDegree (normals B) f = 3) :
    endpoint = f ∨ antipodalStrictFace endpoint = f := by
  let n := normals B
  let hn := normals_ne_zero B
  have hend : endpoint = edgeFace n hn e (endpoint.1 e.1.1) :=
    eq_edgeFace_of_incident n hn endpoint e hendpoint
  rcases eq_or_antipodal_of_liftedCyclic_base_eq
      B ha hb hc hncol pick e e' hbase with heq | heq
  · subst e'
    have hface : f = edgeFace n hn e (f.1 e.1.1) :=
      eq_edgeFace_of_incident n hn f e hf
    by_cases hs : f.1 e.1.1 = endpoint.1 e.1.1
    · left
      rw [hend, hface, hs]
    · have hflip : f.1 e.1.1 = Bool.not (endpoint.1 e.1.1) :=
        Bool.eq_not_iff.mpr hs
      exfalso
      apply hother
      rw [← hflip, ← hface]
      exact htri
  · subst e'
    have hface : f = edgeFace n hn (antipodalEdge n e)
        (f.1 (antipodalEdge n e).1.1) :=
      eq_edgeFace_of_incident n hn f (antipodalEdge n e) hf
    rw [edgeFace_antipodalEdge_flip] at hface
    by_cases hs : Bool.not (f.1 (antipodalEdge n e).1.1) =
        endpoint.1 e.1.1
    · right
      rw [hend, hface, hs]
    · have hflip : Bool.not (f.1 (antipodalEdge n e).1.1) =
          Bool.not (endpoint.1 e.1.1) :=
        Bool.eq_not_iff.mpr hs
      exfalso
      apply hother
      have hanti : strictFaceDegree n
          (antipodalStrictFace
            (edgeFace n hn e (!(endpoint.1 e.1.1)))) = 3 := by
        rw [← hflip, ← hface]
        exact htri
      rwa [strictFaceDegree_antipodalStrictFace] at hanti

/-- Every spherical face slot above one projective cyclic interval lies in
the antipodal orbit of one of the two sides of any chosen lift of that
interval. -/
theorem exists_edgeFace_sameOrbit_of_liftedCyclic_base_eq
    (pick : OtherLineChoice (Line B))
    (e₀ e : StrictEdge (normals B))
    (f : StrictFace (normals B))
    (hbase :
      (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e₀).1 =
        (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1)
    (hf : FaceEdgeIncident (normals B) f e) :
    ∃ side : Bool, SameAntipodalFaceOrbit
      (edgeFace (normals B) (normals_ne_zero B) e₀ side) f := by
  let n := normals B
  let hn := normals_ne_zero B
  rcases eq_or_antipodal_of_liftedCyclic_base_eq
      B ha hb hc hncol pick e₀ e hbase with heq | heq
  · subst e
    let side := f.1 e₀.1.1
    refine ⟨side, Or.inl ?_⟩
    exact (eq_edgeFace_of_incident n hn f e₀ hf).symm
  · subst e
    let side := f.1 (antipodalEdge n e₀).1.1
    have hface : f = edgeFace n hn (antipodalEdge n e₀) side :=
      eq_edgeFace_of_incident n hn f (antipodalEdge n e₀) hf
    rw [edgeFace_antipodalEdge_flip] at hface
    exact ⟨!side, Or.inr hface.symm⟩

/-- If two non-antipodal faces occur above the same projective interval,
their two antipodal orbits exhaust all four spherical face slots above
that interval. -/
theorem sameOrbit_endpoint_or_endpoint_of_same_projective_edge
    (pick : OtherLineChoice (Line B))
    (e₀ e₁ e : StrictEdge (normals B))
    (f₀ f₁ f : StrictFace (normals B))
    (hbase₁ :
      (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e₀).1 =
        (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e₁).1)
    (hbase :
      (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e₀).1 =
        (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1)
    (hf₀ : FaceEdgeIncident (normals B) f₀ e₀)
    (hf₁ : FaceEdgeIncident (normals B) f₁ e₁)
    (hf : FaceEdgeIncident (normals B) f e)
    (horbit : ¬ SameAntipodalFaceOrbit f₀ f₁) :
    SameAntipodalFaceOrbit f₀ f ∨ SameAntipodalFaceOrbit f₁ f := by
  obtain ⟨side₀, hs₀⟩ :=
    exists_edgeFace_sameOrbit_of_liftedCyclic_base_eq
      B ha hb hc hncol pick e₀ e₀ f₀ rfl hf₀
  obtain ⟨side₁, hs₁⟩ :=
    exists_edgeFace_sameOrbit_of_liftedCyclic_base_eq
      B ha hb hc hncol pick e₀ e₁ f₁ hbase₁ hf₁
  obtain ⟨side, hs⟩ :=
    exists_edgeFace_sameOrbit_of_liftedCyclic_base_eq
      B ha hb hc hncol pick e₀ e f hbase hf
  have hsides : side₁ ≠ side₀ := by
    intro h
    subst side₁
    exact horbit (hs₀.symm.trans hs₁)
  by_cases hside : side = side₀
  · subst side
    exact Or.inl (hs₀.symm.trans hs)
  · have hside_not : side = !side₀ := Bool.eq_not_iff.mpr hside
    have hside₁_not : side₁ = !side₀ := Bool.eq_not_iff.mpr hsides
    have heq : side = side₁ := hside_not.trans hside₁_not.symm
    exact Or.inr (hs₁.symm.trans (by simpa [heq] using hs))

/-- Lifted cyclic intervals whose literal projective supporting line is `s`. -/
abbrev LiftedCyclicEdgeOn (s : Line B) :=
  {e : LiftedCyclicSkeletonEdge
      (Finset.univ : Finset (Vertex B)) (OnLine B) //
    cyclicEdgeLine e.1 = s}

/-- The genuine arrangement vertices lying on the selected projective line. -/
abbrev VertexOn (s : Line B) := {v : Vertex B // OnLine B v s}

/-- A lifted cyclic interval on `s` is its initial arrangement vertex in
the cyclic order, together with the spherical sheet.  The terminal vertex
is definitionally the cyclic successor of the initial vertex. -/
noncomputable def liftedCyclicEdgeOnEquivVertexOnTimesBool (s : Line B) :
    LiftedCyclicEdgeOn B s ≃ VertexOn B s × Bool where
  toFun e := (⟨cyclicEdgeStart e.1.1, by
    have h := cyclicEdgeStart_incident
      (Finset.univ : Finset (Vertex B)) (OnLine B) e.1.1
    rw [e.2] at h
    exact h⟩, e.1.2)
  invFun x := ⟨(⟨s, ⟨x.1.1, by
    rw [mem_verticesOn]
    exact ⟨Finset.mem_univ _, x.1.2⟩⟩⟩, x.2), rfl⟩
  left_inv := by
    rintro ⟨⟨⟨l, v⟩, sheet⟩, hl⟩
    have hls : l = s := by
      simpa only [cyclicEdgeLine] using hl
    subst l
    rfl
  right_inv := by
    rintro ⟨v, sheet⟩
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

/-- Restrict the literal owner-preserving strict-edge realization to one
supporting-line fiber. -/
noncomputable def strictEdgeOnLiftedCyclicEquiv
    (pick : OtherLineChoice (Line B)) (s : Line B) :
    StrictEdgeOn (normals B) s ≃ LiftedCyclicEdgeOn B s where
  toFun e := ⟨strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e.1,
    (strictEdgeLiftedCyclicEquiv_line B ha hb hc hncol pick e.1).trans e.2⟩
  invFun e := ⟨(strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick).symm e.1, by
    have hline := strictEdgeLiftedCyclicEquiv_line B ha hb hc hncol pick
      ((strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick).symm e.1)
    rw [(strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick).apply_symm_apply] at hline
    exact hline.symm.trans e.2⟩
  left_inv e := by
    apply Subtype.ext
    exact (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick).symm_apply_apply e.1
  right_inv e := by
    apply Subtype.ext
    exact (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick).apply_symm_apply e.1

/-- The literal cyclic, lifted, two-sided belt is exactly the subtype of
strict faces incident with `s`.  The Boolean already inside a lifted edge is
the spherical lift; the final Boolean chooses one of the two faces adjacent
to that lifted edge. -/
noncomputable def literalLineFaceBeltEquiv
    (pick : OtherLineChoice (Line B)) (s : Line B) :
    LiftedCyclicEdgeOn B s × Bool ≃
      {f : StrictFace (normals B) // LineFaceIncident (normals B) s f} :=
  ((strictEdgeOnLiftedCyclicEquiv B ha hb hc hncol pick s).symm.prodCongr
      (Equiv.refl Bool)).trans
    (lineFaceBeltEquiv (normals_ne_zero B) s)

/-- Fully expanded cyclic belt enumeration.  One projective interval starts
at every arrangement vertex on `s`; the first Boolean selects its spherical
lift and the second Boolean selects the adjacent face side. -/
noncomputable def literalLineFaceCyclicBeltEquiv
    (pick : OtherLineChoice (Line B)) (s : Line B) :
    (VertexOn B s × Bool) × Bool ≃
      {f : StrictFace (normals B) // LineFaceIncident (normals B) s f} :=
  (((liftedCyclicEdgeOnEquivVertexOnTimesBool B s).symm.prodCongr
      (Equiv.refl Bool))).trans
    (literalLineFaceBeltEquiv B ha hb hc hncol pick s)

omit [Nonempty (Line B)] in
include ha hb hc hncol in
/-- Cardinal form of the cyclic belt: one projective interval per vertex on
`s`, two spherical lifts, and two incident face sides. -/
theorem card_incidentFaces_eq_four_mul_verticesOn
    (pick : OtherLineChoice (Line B)) (s : Line B) :
    Fintype.card
        {f : StrictFace (normals B) // LineFaceIncident (normals B) s f} =
      4 * (verticesOn (Finset.univ : Finset (Vertex B)) (OnLine B) s).card := by
  rw [Fintype.card_congr
    (literalLineFaceCyclicBeltEquiv B ha hb hc hncol pick s).symm]
  simp only [Fintype.card_prod, Fintype.card_bool]
  change Fintype.card {v : Vertex B // OnLine B v s} * 2 * 2 =
    4 * (Finset.univ.filter fun v : Vertex B ↦ OnLine B v s).card
  rw [Fintype.card_subtype]
  ring

/-- The face in the cyclic belt whose projective interval starts at `x.1.1`,
whose spherical lift is `x.1.2`, and whose edge side is `x.2`. -/
noncomputable def literalCyclicBeltFace
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (x : (VertexOn B s × Bool) × Bool) : StrictFace (normals B) :=
  (literalLineFaceCyclicBeltEquiv B ha hb hc hncol pick s x).1

omit [Nonempty (Line B)] in
theorem literalCyclicBeltFace_incident
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (x : (VertexOn B s × Bool) × Bool) :
    LineFaceIncident (normals B) s
      (literalCyclicBeltFace B ha hb hc hncol pick s x) :=
  (literalLineFaceCyclicBeltEquiv B ha hb hc hncol pick s x).2

/-- The face represented by a literal belt slot. -/
noncomputable def literalBeltFace
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (x : LiftedCyclicEdgeOn B s × Bool) : StrictFace (normals B) :=
  (literalLineFaceBeltEquiv B ha hb hc hncol pick s x).1

omit [Nonempty (Line B)] in
theorem literalBeltFace_incident
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (x : LiftedCyclicEdgeOn B s × Bool) :
    LineFaceIncident (normals B) s
      (literalBeltFace B ha hb hc hncol pick s x) :=
  (literalLineFaceBeltEquiv B ha hb hc hncol pick s x).2

omit [Nonempty (Line B)] in
/-- Literal-belt form of the exact Stage-4 exhaustion obligation. -/
theorem all_incident_triangles_iff_all_literalBelt_slots
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (endpoint : Fin 2 → StrictFace (normals B)) :
    (∀ f : StrictFace (normals B), LineFaceIncident (normals B) s f →
        strictFaceDegree (normals B) f = 3 → ∃ k, endpoint k = f) ↔
      ∀ x : LiftedCyclicEdgeOn B s × Bool,
        strictFaceDegree (normals B)
            (literalBeltFace B ha hb hc hncol pick s x) = 3 →
          ∃ k, endpoint k = literalBeltFace B ha hb hc hncol pick s x := by
  constructor
  · intro h x hx
    exact h _ (literalBeltFace_incident B ha hb hc hncol pick s x) hx
  · intro h f hf htri
    obtain ⟨x, hx⟩ :=
      (literalLineFaceBeltEquiv B ha hb hc hncol pick s).surjective ⟨f, hf⟩
    have hxval : literalBeltFace B ha hb hc hncol pick s x = f :=
      congrArg Subtype.val hx
    obtain ⟨k, hk⟩ := h x (by simpa [hxval] using htri)
    exact ⟨k, hk.trans hxval⟩

omit [Nonempty (Line B)] in
/-- Antipodally correct literal-belt form of Stage-4 exhaustion. -/
theorem all_incident_triangles_iff_all_literalBelt_slots_or_antipode
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (endpoint : Fin 2 → StrictFace (normals B)) :
    (∀ f : StrictFace (normals B), LineFaceIncident (normals B) s f →
        strictFaceDegree (normals B) f = 3 →
          ∃ k, endpoint k = f ∨ antipodalStrictFace (endpoint k) = f) ↔
      ∀ x : LiftedCyclicEdgeOn B s × Bool,
        strictFaceDegree (normals B)
            (literalBeltFace B ha hb hc hncol pick s x) = 3 →
          ∃ k, endpoint k = literalBeltFace B ha hb hc hncol pick s x ∨
            antipodalStrictFace (endpoint k) =
              literalBeltFace B ha hb hc hncol pick s x := by
  constructor
  · intro h x hx
    exact h _ (literalBeltFace_incident B ha hb hc hncol pick s x) hx
  · intro h f hf htri
    obtain ⟨x, hx⟩ :=
      (literalLineFaceBeltEquiv B ha hb hc hncol pick s).surjective ⟨f, hf⟩
    have hxval : literalBeltFace B ha hb hc hncol pick s x = f :=
      congrArg Subtype.val hx
    obtain ⟨k, hk | hk⟩ := h x (by simpa [hxval] using htri)
    · exact ⟨k, Or.inl (hk.trans hxval)⟩
    · exact ⟨k, Or.inr (hk.trans hxval)⟩

omit [Nonempty (Line B)] in
/-- Fully cyclic version of the Stage-4 exhaustion obligation.  It is enough
to classify the four lifted/side slots based at every projective arrangement
vertex on the selected line. -/
theorem all_incident_triangles_iff_all_literalCyclicBelt_slots
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (endpoint : Fin 2 → StrictFace (normals B)) :
    (∀ f : StrictFace (normals B), LineFaceIncident (normals B) s f →
        strictFaceDegree (normals B) f = 3 → ∃ k, endpoint k = f) ↔
      ∀ x : (VertexOn B s × Bool) × Bool,
        strictFaceDegree (normals B)
            (literalCyclicBeltFace B ha hb hc hncol pick s x) = 3 →
          ∃ k, endpoint k =
            literalCyclicBeltFace B ha hb hc hncol pick s x := by
  constructor
  · intro h x hx
    exact h _ (literalCyclicBeltFace_incident
      B ha hb hc hncol pick s x) hx
  · intro h f hf htri
    obtain ⟨x, hx⟩ :=
      (literalLineFaceCyclicBeltEquiv
        B ha hb hc hncol pick s).surjective ⟨f, hf⟩
    have hxval : literalCyclicBeltFace B ha hb hc hncol pick s x = f :=
      congrArg Subtype.val hx
    obtain ⟨k, hk⟩ := h x (by simpa [hxval] using htri)
    exact ⟨k, hk.trans hxval⟩

omit [Nonempty (Line B)] in
/-- Fully cyclic antipodal-orbit form of the Stage-4 exhaustion
obligation. -/
theorem all_incident_triangles_iff_all_literalCyclicBelt_slots_or_antipode
    (pick : OtherLineChoice (Line B)) (s : Line B)
    (endpoint : Fin 2 → StrictFace (normals B)) :
    (∀ f : StrictFace (normals B), LineFaceIncident (normals B) s f →
        strictFaceDegree (normals B) f = 3 →
          ∃ k, endpoint k = f ∨ antipodalStrictFace (endpoint k) = f) ↔
      ∀ x : (VertexOn B s × Bool) × Bool,
        strictFaceDegree (normals B)
            (literalCyclicBeltFace B ha hb hc hncol pick s x) = 3 →
          ∃ k, endpoint k = literalCyclicBeltFace B ha hb hc hncol pick s x ∨
            antipodalStrictFace (endpoint k) =
              literalCyclicBeltFace B ha hb hc hncol pick s x := by
  constructor
  · intro h x hx
    exact h _ (literalCyclicBeltFace_incident
      B ha hb hc hncol pick s x) hx
  · intro h f hf htri
    obtain ⟨x, hx⟩ :=
      (literalLineFaceCyclicBeltEquiv
        B ha hb hc hncol pick s).surjective ⟨f, hf⟩
    have hxval : literalCyclicBeltFace B ha hb hc hncol pick s x = f :=
      congrArg Subtype.val hx
    obtain ⟨k, hk | hk⟩ := h x (by simpa [hxval] using htri)
    · exact ⟨k, Or.inl (hk.trans hxval)⟩
    · exact ⟨k, Or.inr (hk.trans hxval)⟩

end ConcretePolarLineBelt

end Erdos735
