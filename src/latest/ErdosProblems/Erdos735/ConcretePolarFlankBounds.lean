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

import ErdosProblems.Erdos735.ConcretePolarABKPRData
import ErdosProblems.Erdos735.Stage4FlankCardinality
import ErdosProblems.Erdos735.PolarBoundaryAcrossEndpoints

/-!
# Supporting-line bounds for the literal polar Stage-4 flank graph

The supporting line of a strict polar edge is its owner.  On the boundary
of a fixed polar face, owners are enumerated by `boundaryOwnerEquiv`, and
are therefore injective.  This supplies the first of the two degree bounds
needed for the Stage-4 helping graph without any additional geometric
assumption.

The last construction in this file packages the remaining two genuinely
local statements -- existence of a zero-diagonal flank and the two-endpoint
bound for a fixed helper -- into the final `GeometricFlankBounds` object.
-/

open Classical
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization

namespace Erdos735.ConcretePolarFlankBounds

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarBoundaryOrder
open ConcretePolarOrientedVertex

namespace PolarBoundaryAcross

open SignVector.PolarFace SignVector.PolarPlaneChart
open SignVector.PolarBoundaryOrder
open SignVector.PolarBoundaryAcross
open SignVector.PolarBoundaryAcrossEndpoints

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
variable (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
variable (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
variable (hspan : Submodule.span ℝ (Set.range n) = ⊤)

/-- A boundary vertex which lies on an owner line occurring on the face is
an endpoint of that owner's unique boundary edge. -/
theorem boundaryVertex_mem_edgeVertices_of_onLine
    (f : StrictFace n) (i u : BoundaryIndex n f)
    (hon : ProjectiveArrangement.OnProjectiveLine
      (n (boundaryEdge n hcross hspan f i).1.1)
      (boundaryVertex n hcross hspan f u)) :
    boundaryVertex n hcross hspan f u ∈
      projectiveEdgeVertices n hcross hspan f i := by
  let t : BoundaryIndex n f := (finRotate _).symm u
  have htu : Erdos957.cyclicSucc t = u := (finRotate _).apply_symm_apply u
  have hon' : ProjectiveArrangement.OnProjectiveLine
      (n (boundaryEdge n hcross hspan f i).1.1)
      (boundaryProjectiveVertex f (faceWitness_realizes n f) hcross hspan t) := by
    simpa [t, boundaryVertex] using hon
  have hzero : n (boundaryEdge n hcross hspan f i).1.1 ⬝ᵥ
      cornerVector f (faceWitness_realizes n f) hcross hspan t = 0 := by
    rw [← cornerProjectiveVertex_eq_boundaryProjectiveVertex f
      (faceWitness_realizes n f) hcross hspan t,
      cornerProjectiveVertex,
      ProjectiveArrangement.onProjectiveLine_mk_iff] at hon'
    exact hon'
  have hownerMem : (boundaryEdge n hcross hspan f i).1.1 ∈ edgeOwners n f.1 := by
    change boundaryOwner f (faceWitness_realizes n f) hcross hspan i ∈
      edgeOwners n f.1
    exact (boundaryOwnerEquiv f (faceWitness_realizes n f) hcross hspan i).2
  have hep := owner_eq_endpoint_of_dot_cornerVector_eq_zero f
    (faceWitness_realizes n f) hcross hspan t
    (boundaryEdge n hcross hspan f i).1.1 hownerMem hzero
  have hinj : Function.Injective
      (boundaryOwner f (faceWitness_realizes n f) hcross hspan) := by
    intro x y hxy
    apply (boundaryOwnerEquiv f (faceWitness_realizes n f) hcross hspan).injective
    exact Subtype.ext hxy
  have hi : i = t ∨ i = Erdos957.cyclicSucc t := by
    rcases hep with hep | hep
    · left
      apply hinj
      change boundaryOwner f (faceWitness_realizes n f) hcross hspan i =
        boundaryOwner f (faceWitness_realizes n f) hcross hspan t at hep
      exact hep
    · right
      apply hinj
      change boundaryOwner f (faceWitness_realizes n f) hcross hspan i =
        boundaryOwner f (faceWitness_realizes n f) hcross hspan
          (Erdos957.cyclicSucc t) at hep
      exact hep
  simp only [projectiveEdgeVertices, Finset.mem_insert, Finset.mem_singleton]
  rcases hi with rfl | hi
  · right
    rw [htu]
  · left
    rw [hi, htu]

theorem boundaryVertex_injective (f : StrictFace n) :
    Function.Injective (boundaryVertex n hcross hspan f) := by
  intro i j hij
  apply (finRotate _).symm.injective
  apply boundaryProjectiveVertex_injective f (faceWitness_realizes n f)
    hcross hspan
  simpa only [boundaryVertex] using hij

/-- In a simple cyclic boundary, two distinct edges which share a boundary
vertex are cyclically adjacent. -/
theorem cyclicAdjacent_of_common_boundaryVertex
    (f : StrictFace n) (i j : BoundaryIndex n f) (hij : i ≠ j)
    {v : ℙ ℝ Vec3}
    (hvi : v ∈ projectiveEdgeVertices n hcross hspan f i)
    (hvj : v ∈ projectiveEdgeVertices n hcross hspan f j) :
    Erdos957.cyclicSucc i = j ∨ Erdos957.cyclicSucc j = i := by
  simp only [projectiveEdgeVertices, Finset.mem_insert, Finset.mem_singleton] at hvi hvj
  rcases hvi with hvi | hvi <;> rcases hvj with hvj | hvj
  · exfalso
    apply hij
    exact boundaryVertex_injective n hcross hspan f (hvi.symm.trans hvj)
  · right
    exact boundaryVertex_injective n hcross hspan f (hvj.symm.trans hvi)
  · left
    exact boundaryVertex_injective n hcross hspan f (hvi.symm.trans hvj)
  · exfalso
    apply hij
    apply (finRotate _).injective
    exact boundaryVertex_injective n hcross hspan f (hvi.symm.trans hvj)

/-- Flipping across one member of an adjacent edge pair transports their
common corner.  Any edge of the new face with the other member's owner has
that transported corner as an endpoint. -/
theorem adjacent_across_common_endpoint
    (q : StrictFace n) (k j : BoundaryIndex n q)
    (hadj : Erdos957.cyclicSucc k = j ∨ Erdos957.cyclicSucc j = k)
    (i : BoundaryIndex n (across n hn hcross hspan ⟨q, j⟩).1)
    (howner :
      (boundaryEdge n hcross hspan q k).1.1 =
        (boundaryEdge n hcross hspan
          (across n hn hcross hspan ⟨q, j⟩).1 i).1.1) :
    ∃ v,
      v ∈ projectiveEdgeVertices n hcross hspan
        (across n hn hcross hspan ⟨q, j⟩).1
        (across n hn hcross hspan ⟨q, j⟩).2 ∧
      v ∈ projectiveEdgeVertices n hcross hspan
        (across n hn hcross hspan ⟨q, j⟩).1 i := by
  let v : ℙ ℝ Vec3 := if Erdos957.cyclicSucc k = j then
      boundaryVertex n hcross hspan q j
    else boundaryVertex n hcross hspan q k
  have hvk : v ∈ projectiveEdgeVertices n hcross hspan q k := by
    simp only [projectiveEdgeVertices, Finset.mem_insert, Finset.mem_singleton]
    by_cases hkj : Erdos957.cyclicSucc k = j
    · right
      change (if Erdos957.cyclicSucc k = j then
        boundaryVertex n hcross hspan q j
        else boundaryVertex n hcross hspan q k) =
          boundaryVertex n hcross hspan q (Erdos957.cyclicSucc k)
      rw [if_pos hkj, hkj]
    · left
      change (if Erdos957.cyclicSucc k = j then
        boundaryVertex n hcross hspan q j
        else boundaryVertex n hcross hspan q k) =
          boundaryVertex n hcross hspan q k
      rw [if_neg hkj]
  have hvj : v ∈ projectiveEdgeVertices n hcross hspan q j := by
    simp only [projectiveEdgeVertices, Finset.mem_insert, Finset.mem_singleton]
    by_cases hkj : Erdos957.cyclicSucc k = j
    · left
      change (if Erdos957.cyclicSucc k = j then
        boundaryVertex n hcross hspan q j
        else boundaryVertex n hcross hspan q k) =
          boundaryVertex n hcross hspan q j
      rw [if_pos hkj]
    · have hjk : Erdos957.cyclicSucc j = k := hadj.resolve_left hkj
      right
      change (if Erdos957.cyclicSucc k = j then
        boundaryVertex n hcross hspan q j
        else boundaryVertex n hcross hspan q k) =
          boundaryVertex n hcross hspan q (Erdos957.cyclicSucc j)
      rw [if_neg hkj, hjk]
  have hvAcross : v ∈ projectiveEdgeVertices n hcross hspan
      (across n hn hcross hspan ⟨q, j⟩).1
      (across n hn hcross hspan ⟨q, j⟩).2 := by
    rw [← projectiveEdgeVertices_across n hn hcross hspan ⟨q, j⟩]
    exact hvj
  have hvline : ProjectiveArrangement.OnProjectiveLine
      (n (boundaryEdge n hcross hspan
        (across n hn hcross hspan ⟨q, j⟩).1 i).1.1) v := by
    rw [← howner]
    simp only [projectiveEdgeVertices, Finset.mem_insert,
      Finset.mem_singleton] at hvk
    rcases hvk with hvk | hvk
    · rw [hvk]
      exact boundaryVertex_on_edge_start n hcross hspan q k
    · rw [hvk]
      exact boundaryVertex_on_edge_finish n hcross hspan q k
  refine ⟨v, hvAcross, ?_⟩
  simp only [projectiveEdgeVertices, Finset.mem_insert,
    Finset.mem_singleton] at hvAcross
  rcases hvAcross with hv | hv
  · have hon : ProjectiveArrangement.OnProjectiveLine
        (n (boundaryEdge n hcross hspan
          (across n hn hcross hspan ⟨q, j⟩).1 i).1.1)
        (boundaryVertex n hcross hspan
          (across n hn hcross hspan ⟨q, j⟩).1
          (across n hn hcross hspan ⟨q, j⟩).2) := by
      rw [← hv]
      exact hvline
    have hm := boundaryVertex_mem_edgeVertices_of_onLine n hcross hspan _ i _ hon
    rwa [← hv] at hm
  · have hon : ProjectiveArrangement.OnProjectiveLine
        (n (boundaryEdge n hcross hspan
          (across n hn hcross hspan ⟨q, j⟩).1 i).1.1)
        (boundaryVertex n hcross hspan
          (across n hn hcross hspan ⟨q, j⟩).1
          (Erdos957.cyclicSucc (across n hn hcross hspan ⟨q, j⟩).2)) := by
      rw [← hv]
      exact hvline
    have hm := boundaryVertex_mem_edgeVertices_of_onLine n hcross hspan _ i _ hon
    rwa [← hv] at hm

/-- Transporting a boundary index along equality of faces preserves its
supporting-line owner. -/
theorem boundaryEdge_owner_cast
    (f g : StrictFace n) (hfg : f = g) (i : BoundaryIndex n f) :
    (boundaryEdge n hcross hspan g
      (Fin.cast (congrArg (fun z : StrictFace n ↦
        Erdos957.hullVertexCount
          (boundaryPolygon n z.1 (faceWitness n z))) hfg) i)).1.1 =
      (boundaryEdge n hcross hspan f i).1.1 := by
  subst g
  rfl

theorem cyclicAdjacent_cast
    (f g : StrictFace n) (hfg : f = g)
    {i j : BoundaryIndex n f}
    (hij : Erdos957.cyclicSucc i = j ∨ Erdos957.cyclicSucc j = i) :
    Erdos957.cyclicSucc
        (Fin.cast (congrArg (fun z : StrictFace n ↦
          Erdos957.hullVertexCount
            (boundaryPolygon n z.1 (faceWitness n z))) hfg) i) =
      Fin.cast (congrArg (fun z : StrictFace n ↦
          Erdos957.hullVertexCount
            (boundaryPolygon n z.1 (faceWitness n z))) hfg) j ∨
    Erdos957.cyclicSucc
        (Fin.cast (congrArg (fun z : StrictFace n ↦
          Erdos957.hullVertexCount
            (boundaryPolygon n z.1 (faceWitness n z))) hfg) j) =
      Fin.cast (congrArg (fun z : StrictFace n ↦
          Erdos957.hullVertexCount
            (boundaryPolygon n z.1 (faceWitness n z))) hfg) i := by
  subst g
  exact hij

end PolarBoundaryAcross

end Erdos735.ConcretePolarFlankBounds

namespace Erdos735.ABKPR.Data

universe uV uEd uF uL

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
variable {C₀ : BlueCellulation Vertex Edge Face}
variable {A : ABKPR.Data C₀}
variable {Line₀ : Type uL} [Fintype Line₀] [DecidableEq Line₀]

noncomputable def endpointAdjacentIndex
    (edgeLine₀ : Edge → Line₀) (h : A.HelpingPair)
    (e : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h}) :
    Fin (C₀.faceDegree (A.across (A.evilDart e.1)).1) :=
  Classical.choose e.2.1

theorem endpointAdjacentIndex_spec
    (edgeLine₀ : Edge → Line₀) (h : A.HelpingPair)
    (e : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h}) :
    CyclicAdjacentIndex (C := C₀) (A.across (A.evilDart e.1)).2
        (A.endpointAdjacentIndex edgeLine₀ h e) ∧
      (A.across ⟨(A.across (A.evilDart e.1)).1,
        A.endpointAdjacentIndex edgeLine₀ h e⟩).1 = h.face :=
  Classical.choose_spec e.2.1

noncomputable def endpointAcrossDart
    (edgeLine₀ : Edge → Line₀) (h : A.HelpingPair)
    (e : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h}) :
    ABKPR.FaceDart C₀ :=
  A.across ⟨(A.across (A.evilDart e.1)).1,
    A.endpointAdjacentIndex edgeLine₀ h e⟩

theorem endpointAcrossDart_face
    (edgeLine₀ : Edge → Line₀) (h : A.HelpingPair)
    (e : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h}) :
    (A.endpointAcrossDart edgeLine₀ h e).1 = h.face :=
  (A.endpointAdjacentIndex_spec edgeLine₀ h e).2

noncomputable def endpointHelperIndex
    (edgeLine₀ : Edge → Line₀) (h : A.HelpingPair)
    (e : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h}) :
    Fin (C₀.faceDegree h.face) :=
  Fin.cast (congrArg C₀.faceDegree
    (A.endpointAcrossDart_face edgeLine₀ h e))
    (A.endpointAcrossDart edgeLine₀ h e).2

theorem endpointAcrossDart_eq
    (edgeLine₀ : Edge → Line₀) (h : A.HelpingPair)
    (e : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h}) :
    A.endpointAcrossDart edgeLine₀ h e =
      ⟨h.face, A.endpointHelperIndex edgeLine₀ h e⟩ := by
  rcases hp : A.endpointAcrossDart edgeLine₀ h e with ⟨f, i⟩
  have hf := A.endpointAcrossDart_face edgeLine₀ h e
  rw [hp] at hf
  dsimp only at hf
  subst f
  apply Sigma.ext_iff.mpr
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  apply Fin.ext
  simp only [endpointHelperIndex, Fin.val_cast]
  exact (congrArg (fun q : ABKPR.FaceDart C₀ ↦ q.2.val) hp).symm

private theorem faceDart_eq_of_fst_eq_of_boundaryLine_eq
    (edgeLine₀ : Edge → Line₀)
    (hinj : ∀ f, Function.Injective
      (fun i ↦ edgeLine₀ (A.boundaryEdge f i)))
    (q q' : ABKPR.FaceDart C₀) (hface : q.1 = q'.1)
    (hline : edgeLine₀ (A.boundaryEdge q.1 q.2) =
      edgeLine₀ (A.boundaryEdge q'.1 q'.2)) : q = q' := by
  rcases q with ⟨f, i⟩
  rcases q' with ⟨g, j⟩
  dsimp only at hface
  subst g
  have hij : i = j := hinj f hline
  subst j
  rfl

/-- Pure cellulation bookkeeping: if a geometric flank really meets the
designated helper edge at one of its two cyclic endpoints, distinct evil
faces give distinct endpoint indices. -/
theorem endpointHelperIndex_injective
    (edgeLine₀ : Edge → Line₀)
    (hinj : ∀ f, Function.Injective
      (fun i ↦ edgeLine₀ (A.boundaryEdge f i)))
    (h : A.HelpingPair) :
    Function.Injective (A.endpointHelperIndex edgeLine₀ h) := by
  intro e e' hee'
  have hdart : A.endpointAcrossDart edgeLine₀ h e =
      A.endpointAcrossDart edgeLine₀ h e' := by
    rw [A.endpointAcrossDart_eq edgeLine₀ h e,
      A.endpointAcrossDart_eq edgeLine₀ h e', hee']
  have horig :
      (⟨(A.across (A.evilDart e.1)).1,
        A.endpointAdjacentIndex edgeLine₀ h e⟩ : ABKPR.FaceDart C₀) =
      ⟨(A.across (A.evilDart e'.1)).1,
        A.endpointAdjacentIndex edgeLine₀ h e'⟩ := by
    apply A.across_involutive.injective
    exact hdart
  have hface : (A.across (A.evilDart e.1)).1 =
      (A.across (A.evilDart e'.1)).1 := (Sigma.ext_iff.mp horig).1
  let q := A.across (A.evilDart e.1)
  let q' := A.across (A.evilDart e'.1)
  have hline (x : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h}) :
      edgeLine₀ (A.boundaryEdge (A.across (A.evilDart x.1)).1
          (A.across (A.evilDart x.1)).2) =
        edgeLine₀ (A.boundaryEdge h.face h.index) := by
    rw [← A.across_sameEdge (A.evilDart x.1)]
    exact x.2.2.symm
  have hq : q = q' := by
    apply faceDart_eq_of_fst_eq_of_boundaryLine_eq edgeLine₀ hinj q q' hface
    exact (hline e).trans (hline e').symm
  have hevilDart : A.evilDart e.1 = A.evilDart e'.1 := by
    apply A.across_involutive.injective
    exact hq
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z ↦ z.1) hevilDart

/-- If the transported flank edge is cyclically adjacent to the helper's
designated edge, a fixed helper has at most two evil endpoints. -/
theorem geometricEvilEndpoints_card_le_two_of_endpoint_adjacent
    (edgeLine₀ : Edge → Line₀)
    (hinj : ∀ f, Function.Injective
      (fun i ↦ edgeLine₀ (A.boundaryEdge f i)))
    (hadj : ∀ (h : A.HelpingPair)
        (e : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h}),
      CyclicAdjacentIndex (C := C₀) h.index
        (A.endpointHelperIndex edgeLine₀ h e))
    (h : A.HelpingPair) :
    (A.geometricEvilEndpoints edgeLine₀ h).card ≤ 2 := by
  rw [← Fintype.card_coe]
  let φ : {e : A.EvilFace // e ∈ A.geometricEvilEndpoints edgeLine₀ h} → Bool :=
    fun e ↦ decide (ABKPR.faceSucc C₀ h.face h.index =
      A.endpointHelperIndex edgeLine₀ h
        ⟨e.1, (Finset.mem_filter.mp e.2).2⟩)
  have hφ : Function.Injective φ := by
    intro e e' hside
    let x : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h} :=
      ⟨e.1, (Finset.mem_filter.mp e.2).2⟩
    let y : {e : A.EvilFace // A.IsGeometricFlank edgeLine₀ e h} :=
      ⟨e'.1, (Finset.mem_filter.mp e'.2).2⟩
    have hindex : A.endpointHelperIndex edgeLine₀ h x =
        A.endpointHelperIndex edgeLine₀ h y := by
      by_cases hx : ABKPR.faceSucc C₀ h.face h.index =
          A.endpointHelperIndex edgeLine₀ h x
      · have hxtrue : φ e = true := by simp [φ, x, hx]
        have hytrue : φ e' = true := by rw [← hside]; exact hxtrue
        have hy : ABKPR.faceSucc C₀ h.face h.index =
            A.endpointHelperIndex edgeLine₀ h y := by
          simpa [φ, y] using hytrue
        exact hx.symm.trans hy
      · have hxfalse : φ e = false := by simp [φ, x, hx]
        have hyfalse : φ e' = false := by rw [← hside]; exact hxfalse
        have hy : ABKPR.faceSucc C₀ h.face h.index ≠
            A.endpointHelperIndex edgeLine₀ h y := by
          simpa [φ, y] using hyfalse
        have hax := (hadj h x).resolve_left hx
        have hay := (hadj h y).resolve_left hy
        exact (ABKPR.faceSucc_injective C₀ h.face) (hax.trans hay.symm)
    apply Subtype.ext
    exact congrArg (fun z : {e : A.EvilFace //
      A.IsGeometricFlank edgeLine₀ e h} ↦ z.1)
        ((A.endpointHelperIndex_injective edgeLine₀ hinj h) hindex)
  have hc := Fintype.card_le_of_injective φ hφ
  simpa only [Fintype.card_bool] using hc

theorem faceSucc_ne_self (f : Face) (i : Fin (C₀.faceDegree f)) :
    ABKPR.faceSucc C₀ f i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  simp only [ABKPR.faceSucc, ABKPR.cyclicSucc] at hval
  have hdeg := C₀.faceDegree_three_le f
  change 3 ≤ C₀.faceDegree f at hdeg
  by_cases hi : i.val + 1 < C₀.faceDegree f
  · rw [Nat.mod_eq_of_lt hi] at hval
    omega
  · have hilast : i.val + 1 = C₀.faceDegree f := by omega
    rw [hilast, Nat.mod_self] at hval
    rw [← hilast] at hdeg
    have hipos : 0 < i.val := by omega
    exact (Nat.ne_of_lt hipos) hval

end Erdos735.ABKPR.Data

namespace Erdos735.ConcretePolarFlankBounds

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarBoundaryOrder
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

abbrev B := nonordinaryPoints P

abbrev C := ConcretePolarCellulation.blueCellulation
  (nonordinaryPoints P) ha hb hd hncol

abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol

theorem dartEquiv_across
    (q : ABKPR.FaceDart (C ha hb hd hncol)) :
    ConcretePolarABKPRData.dartEquiv
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol)
        ha hb hd hncol ((D hred ha hb hd hncol).across q) =
      SignVector.PolarBoundaryAcross.across
        (normals (nonordinaryPoints P))
        (normals_ne_zero (nonordinaryPoints P)) normal_cross
        (ConcretePolarABKPRData.hspan ha hb hd hncol)
        (ConcretePolarABKPRData.dartEquiv
          (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
            (nonordinaryPoints P) ha hb hd hncol)
          ha hb hd hncol q) := by
  rfl

/-- The arrangement line supporting a strict polar edge. -/
def edgeLine
    (e : StrictEdge (normals (nonordinaryPoints P))) :
    ProjectiveBoundaryExtraction.Line (nonordinaryPoints P) :=
  e.1.1

/-- Along one literal polar face, distinct boundary positions have distinct
supporting arrangement lines. -/
theorem boundary_edgeLine_injective
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Function.Injective (fun i ↦
      edgeLine (ConcretePolarABKPRData.boundaryEdge
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol)
        ha hb hd hncol f i)) := by
  intro i j hij
  apply (ConcretePolarABKPRData.indexEquiv
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (nonordinaryPoints P) ha hb hd hncol)
    ha hb hd hncol f).injective
  apply (PolarBoundaryOrder.boundaryOwnerEquiv f
    (SignVector.faceWitness_realizes (normals (nonordinaryPoints P)) f)
    normal_cross
    (ConcretePolarABKPRData.hspan ha hb hd hncol)).injective
  apply Subtype.ext
  exact hij

/-- The owner label is injective on every boundary cycle of the assembled
concrete ABKPR data. -/
theorem data_boundary_edgeLine_injective
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Function.Injective (fun i ↦ edgeLine ((D hred ha hb hd hncol).boundaryEdge f i)) := by
  exact boundary_edgeLine_injective (ha := ha) (hb := hb) (hd := hd)
    (hncol := hncol) f

/-- A fixed evil triangle has at most the two cyclic flank slots. -/
theorem evil_geometricFlanks_card_le_two
    (e : (D hred ha hb hd hncol).EvilFace) :
    ((D hred ha hb hd hncol).geometricFlanks edgeLine e).card ≤ 2 := by
  exact ABKPR.Data.geometricFlanks_card_le_two_of_boundaryLine_injective
    edgeLine
    (data_boundary_edgeLine_injective hred ha hb hd hncol)
    e

/-- The edge obtained by crossing an evil flank is adjacent, on the helper
face, to the helper's designated edge. -/
theorem endpointHelperIndex_adjacent
    (h : (D hred ha hb hd hncol).HelpingPair)
    (e : {e : (D hred ha hb hd hncol).EvilFace //
      (D hred ha hb hd hncol).IsGeometricFlank edgeLine e h}) :
    ABKPR.Data.CyclicAdjacentIndex h.index
      ((D hred ha hb hd hncol).endpointHelperIndex edgeLine h e) := by
  let qd : ConcretePolarABKPRData.FaceDart
      (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
        (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol :=
    (D hred ha hb hd hncol).across
      ((D hred ha hb hd hncol).evilDart e.1)
  let jd : Fin ((ConcretePolarABKPRData.C
      (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
        (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol).faceDegree qd.1) :=
    (D hred ha hb hd hncol).endpointAdjacentIndex edgeLine h e
  let dd : ConcretePolarABKPRData.FaceDart
      (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
        (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol := ⟨qd.1, jd⟩
  let de := ConcretePolarABKPRData.dartEquiv
    (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
      (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol
  let pa := SignVector.PolarBoundaryAcross.across
    (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
    normal_cross (ConcretePolarABKPRData.hspan ha hb hd hncol)
  have hspec := (D hred ha hb hd hncol).endpointAdjacentIndex_spec edgeLine h e
  have hadjp : Erdos957.cyclicSucc (de qd).2 = (de dd).2 ∨
      Erdos957.cyclicSucc (de dd).2 = (de qd).2 := by
    rcases hspec.1 with hs | hs
    · left
      change Erdos957.cyclicSucc
          (ConcretePolarABKPRData.indexEquiv
            (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
              (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol qd.1 qd.2) =
        ConcretePolarABKPRData.indexEquiv
          (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
            (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol qd.1 jd
      rw [← ConcretePolarABKPRData.indexEquiv_succ
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol]
      exact congrArg (ConcretePolarABKPRData.indexEquiv
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol qd.1) hs
    · right
      change Erdos957.cyclicSucc
          (ConcretePolarABKPRData.indexEquiv
            (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
              (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol qd.1 jd) =
        ConcretePolarABKPRData.indexEquiv
          (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
            (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol qd.1 qd.2
      rw [← ConcretePolarABKPRData.indexEquiv_succ
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol]
      exact congrArg (ConcretePolarABKPRData.indexEquiv
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol qd.1) hs
  have hmap : de ((D hred ha hb hd hncol).across dd) = pa (de dd) := by
    exact dartEquiv_across hred ha hb hd hncol dd
  have hfaceP : (pa (de dd)).1 = h.face := by
    rw [← hmap]
    exact hspec.2
  let ip : SignVector.PolarBoundaryAcross.BoundaryIndex
      (normals (nonordinaryPoints P)) (pa (de dd)).1 :=
    Fin.cast (congrArg (fun f : StrictFace (normals (nonordinaryPoints P)) ↦
      Erdos957.hullVertexCount
        (SignVector.PolarPlaneChart.boundaryPolygon
          (normals (nonordinaryPoints P)) f.1
          (SignVector.faceWitness (normals (nonordinaryPoints P)) f))) hfaceP.symm)
      (ConcretePolarABKPRData.indexEquiv
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol h.face h.index)
  have hownerD : edgeLine ((D hred ha hb hd hncol).boundaryEdge qd.1 qd.2) =
      edgeLine ((D hred ha hb hd hncol).boundaryEdge h.face h.index) := by
    calc
      edgeLine ((D hred ha hb hd hncol).boundaryEdge qd.1 qd.2) =
          edgeLine ((D hred ha hb hd hncol).boundaryEdge e.1.1
            ((D hred ha hb hd hncol).evilIndex e.1)) := by
        exact congrArg edgeLine
          ((D hred ha hb hd hncol).across_sameEdge
            ((D hred ha hb hd hncol).evilDart e.1)).symm
      _ = edgeLine ((D hred ha hb hd hncol).boundaryEdge h.face h.index) :=
        e.2.2.symm
  have hownerP :
      (SignVector.PolarBoundaryAcross.boundaryEdge
        (normals (nonordinaryPoints P)) normal_cross
        (ConcretePolarABKPRData.hspan ha hb hd hncol) (de qd).1 (de qd).2).1.1 =
      (SignVector.PolarBoundaryAcross.boundaryEdge
        (normals (nonordinaryPoints P)) normal_cross
        (ConcretePolarABKPRData.hspan ha hb hd hncol) (pa (de dd)).1 ip).1.1 := by
    calc
      (SignVector.PolarBoundaryAcross.boundaryEdge
        (normals (nonordinaryPoints P)) normal_cross
        (ConcretePolarABKPRData.hspan ha hb hd hncol) (de qd).1 (de qd).2).1.1 =
          edgeLine ((D hred ha hb hd hncol).boundaryEdge qd.1 qd.2) := rfl
      _ = edgeLine ((D hred ha hb hd hncol).boundaryEdge h.face h.index) := hownerD
      _ = (SignVector.PolarBoundaryAcross.boundaryEdge
          (normals (nonordinaryPoints P)) normal_cross
          (ConcretePolarABKPRData.hspan ha hb hd hncol) (pa (de dd)).1 ip).1.1 := by
        exact (PolarBoundaryAcross.boundaryEdge_owner_cast
          (normals (nonordinaryPoints P)) normal_cross
          (ConcretePolarABKPRData.hspan ha hb hd hncol)
          h.face (pa (de dd)).1 hfaceP.symm
          (ConcretePolarABKPRData.indexEquiv
            (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
              (nonordinaryPoints P) ha hb hd hncol)
            ha hb hd hncol h.face h.index)).symm
  obtain ⟨v, hvdd, hvip⟩ :=
    PolarBoundaryAcross.adjacent_across_common_endpoint
      (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
      normal_cross (ConcretePolarABKPRData.hspan ha hb hd hncol)
      (de qd).1 (de qd).2 (de dd).2 hadjp ip hownerP
  have howner_ne :
      (SignVector.PolarBoundaryAcross.boundaryEdge
        (normals (nonordinaryPoints P)) normal_cross
        (ConcretePolarABKPRData.hspan ha hb hd hncol) (de qd).1 (de qd).2).1.1 ≠
      (SignVector.PolarBoundaryAcross.boundaryEdge
        (normals (nonordinaryPoints P)) normal_cross
        (ConcretePolarABKPRData.hspan ha hb hd hncol) (de dd).1 (de dd).2).1.1 := by
    have hjd : jd ≠ qd.2 := by
      intro hjd
      rcases hspec.1 with hs | hs
      · exact ABKPR.Data.faceSucc_ne_self qd.1 qd.2
          (hs.trans hjd)
      · exact ABKPR.Data.faceSucc_ne_self qd.1 jd
          (hs.trans hjd.symm)
    change edgeLine ((D hred ha hb hd hncol).boundaryEdge qd.1 qd.2) ≠
      edgeLine ((D hred ha hb hd hncol).boundaryEdge qd.1 jd)
    exact (Function.Injective.ne
      (data_boundary_edgeLine_injective hred ha hb hd hncol qd.1) hjd.symm)
  have hne : (pa (de dd)).2 ≠ ip := by
    intro heq
    apply howner_ne
    calc
      (SignVector.PolarBoundaryAcross.boundaryEdge
        (normals (nonordinaryPoints P)) normal_cross
        (ConcretePolarABKPRData.hspan ha hb hd hncol) (de qd).1 (de qd).2).1.1 =
          (SignVector.PolarBoundaryAcross.boundaryEdge
            (normals (nonordinaryPoints P)) normal_cross
            (ConcretePolarABKPRData.hspan ha hb hd hncol) (pa (de dd)).1 ip).1.1 := hownerP
      _ = (SignVector.PolarBoundaryAcross.boundaryEdge
            (normals (nonordinaryPoints P)) normal_cross
            (ConcretePolarABKPRData.hspan ha hb hd hncol)
            (pa (de dd)).1 (pa (de dd)).2).1.1 := by rw [heq]
      _ = (SignVector.PolarBoundaryAcross.boundaryEdge
            (normals (nonordinaryPoints P)) normal_cross
            (ConcretePolarABKPRData.hspan ha hb hd hncol)
            (de dd).1 (de dd).2).1.1 :=
        congrArg (fun x : SignVector.StrictEdge
          (normals (nonordinaryPoints P)) ↦ x.1.1)
          (SignVector.PolarBoundaryAcross.across_sameEdge
            (normals (nonordinaryPoints P)) (normals_ne_zero (nonordinaryPoints P))
            normal_cross (ConcretePolarABKPRData.hspan ha hb hd hncol) (de dd)).symm
  have hadjP := PolarBoundaryAcross.cyclicAdjacent_of_common_boundaryVertex
    (normals (nonordinaryPoints P)) normal_cross
    (ConcretePolarABKPRData.hspan ha hb hd hncol) (pa (de dd)).1
    (pa (de dd)).2 ip hne hvdd hvip
  let castToHelper := fun
      (i : SignVector.PolarBoundaryAcross.BoundaryIndex
        (normals (nonordinaryPoints P)) (pa (de dd)).1) ↦
    Fin.cast (congrArg (fun f : StrictFace (normals (nonordinaryPoints P)) ↦
      Erdos957.hullVertexCount
        (SignVector.PolarPlaneChart.boundaryPolygon
          (normals (nonordinaryPoints P)) f.1
          (SignVector.faceWitness (normals (nonordinaryPoints P)) f))) hfaceP) i
  have hadjH := PolarBoundaryAcross.cyclicAdjacent_cast
    (normals (nonordinaryPoints P)) (pa (de dd)).1 h.face hfaceP hadjP
  let rD := (D hred ha hb hd hncol).endpointHelperIndex edgeLine h e
  have hmapVal := congrArg
    (fun z : SignVector.PolarBoundaryAcross.IndexedDart
      (normals (nonordinaryPoints P)) ↦ z.2.val) hmap
  have hdartEq : (D hred ha hb hd hncol).across dd = ⟨h.face, rD⟩ := by
    exact (D hred ha hb hd hncol).endpointAcrossDart_eq edgeLine h e
  have hdartVal := congrArg
    (fun z : ABKPR.FaceDart (C ha hb hd hncol) ↦ z.2.val) hdartEq
  have hr : castToHelper (pa (de dd)).2 =
      ConcretePolarABKPRData.indexEquiv
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol h.face rD := by
    apply Fin.ext
    calc
      (castToHelper (pa (de dd)).2).val = (pa (de dd)).2.val := Fin.val_cast _ _
      _ = (de ((D hred ha hb hd hncol).across dd)).2.val := hmapVal.symm
      _ = ((D hred ha hb hd hncol).across dd).2.val := rfl
      _ = rD.val := hdartVal
      _ = (ConcretePolarABKPRData.indexEquiv
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol h.face rD).val := rfl
  have hi : castToHelper ip =
      ConcretePolarABKPRData.indexEquiv
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol h.face h.index := by
    apply Fin.ext
    rfl
  change Erdos957.cyclicSucc (castToHelper (pa (de dd)).2) = castToHelper ip ∨
    Erdos957.cyclicSucc (castToHelper ip) = castToHelper (pa (de dd)).2 at hadjH
  rw [hr, hi] at hadjH
  rw [ABKPR.Data.CyclicAdjacentIndex]
  change
    ABKPR.faceSucc (ConcretePolarABKPRData.C
      (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
        (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol)
        h.face h.index = rD ∨
      ABKPR.faceSucc (ConcretePolarABKPRData.C
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol)
        h.face rD = h.index
  have hdegree : (C ha hb hd hncol).faceDegree h.face =
      Erdos957.hullVertexCount
        (SignVector.PolarPlaneChart.boundaryPolygon
          (normals (nonordinaryPoints P)) h.face.1
          (SignVector.faceWitness (normals (nonordinaryPoints P)) h.face)) := by
    simpa only [ConcretePolarABKPRData.C,
      ConcretePolarCellulation.blueCellulation] using
      (ConcretePolarABKPRData.faceDegree_eq_boundaryCount
        (vertex_degree := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
          (nonordinaryPoints P) ha hb hd hncol) ha hb hd hncol h.face)
  rcases hadjH with hs | hs
  · right
    apply Fin.ext
    have hsval := congrArg Fin.val hs
    rw [Erdos957.cyclicSucc_val] at hsval
    change (rD.val + 1) % Erdos957.hullVertexCount
      (SignVector.PolarPlaneChart.boundaryPolygon
        (normals (nonordinaryPoints P)) h.face.1
        (SignVector.faceWitness (normals (nonordinaryPoints P)) h.face)) =
      h.index.val at hsval
    change (rD.val + 1) % (C ha hb hd hncol).faceDegree h.face = h.index.val
    exact (congrArg (fun n ↦ (rD.val + 1) % n) hdegree).trans hsval
  · left
    apply Fin.ext
    have hsval := congrArg Fin.val hs
    rw [Erdos957.cyclicSucc_val] at hsval
    change (h.index.val + 1) % Erdos957.hullVertexCount
      (SignVector.PolarPlaneChart.boundaryPolygon
        (normals (nonordinaryPoints P)) h.face.1
        (SignVector.faceWitness (normals (nonordinaryPoints P)) h.face)) =
      rD.val at hsval
    change (h.index.val + 1) % (C ha hb hd hncol).faceDegree h.face = rD.val
    exact (congrArg (fun n ↦ (h.index.val + 1) % n) hdegree).trans hsval

/-- A fixed literal helping pair is adjacent to at most the two evil
triangles occurring at the endpoints of its designated edge. -/
theorem helper_geometricEndpoints_card_le_two
    (h : (D hred ha hb hd hncol).HelpingPair) :
    ((D hred ha hb hd hncol).geometricEvilEndpoints edgeLine h).card ≤ 2 := by
  exact ABKPR.Data.geometricEvilEndpoints_card_le_two_of_endpoint_adjacent
      (A := D hred ha hb hd hncol)
      edgeLine (data_boundary_edgeLine_injective hred ha hb hd hncol)
      (endpointHelperIndex_adjacent hred ha hb hd hncol) h

/-- Once the two remaining local polar facts are supplied, all lookup maps
and both graph degree bounds are extracted by the generic Stage-4 code. -/
noncomputable def geometricFlankBounds
    (evil_has_geometric_flank : ∀ e : (D hred ha hb hd hncol).EvilFace,
      ((D hred ha hb hd hncol).geometricFlanks edgeLine e).Nonempty) :
    (D hred ha hb hd hncol).GeometricFlankBounds
      (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P)) where
  edgeLine := edgeLine
  evil_has_geometric_flank := evil_has_geometric_flank
  evil_geometricFlanks_card_le_two :=
    evil_geometricFlanks_card_le_two hred ha hb hd hncol
  helper_geometricEndpoints_card_le_two :=
    helper_geometricEndpoints_card_le_two hred ha hb hd hncol

end Erdos735.ConcretePolarFlankBounds
