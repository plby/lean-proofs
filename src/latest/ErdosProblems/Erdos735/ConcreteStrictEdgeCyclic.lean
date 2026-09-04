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

import ErdosProblems.Erdos735.ConcretePolarEdgeVertices
import ErdosProblems.Erdos735.ProjectiveEdgeEndpointEquiv
import ErdosProblems.Erdos735.CyclicThreeEdge

/-!
# Literal strict-edge endpoints and the genuine projective cyclic skeleton

`ProjectiveEdgeEndpointEquiv` constructs the genuine cyclic projective edge
of every strict restriction sector.  The concrete polar cellulation uses an
independent, literal construction of the two endpoints.  Here we prove that
their projective endpoint pairs agree.  This is the label-preserving bridge
needed by the local failed-Fano recognition arguments.
-/

open Classical
open scoped BigOperators Matrix LinearAlgebra.Projectivization
open Matrix

namespace Erdos735.ConcreteStrictEdgeCyclic

open ChartOrder ProjectiveArrangement ProjectiveBoundaryExtraction
open SignVector SignVector.RedChordSector
open SignVector.ProjectiveEdgeEndpointEquiv
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B
abbrev Vertex (B : Finset Point) := ProjectiveBoundaryExtraction.Vertex B

private theorem orientedSum_dot_pos_of_weak_of_insertSpan
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {n : I → Vec3} {s : I → Bool} {h y : Vec3}
    (hspan : Submodule.span ℝ (Set.insert h (Set.range n)) = ⊤)
    (hy0 : y ≠ 0) (hhy : h ⬝ᵥ y = 0)
    (hy : WeaklyRealizes n s y) :
    0 < orientedSum n s ⬝ᵥ y := by
  have hnonneg (i : I) : 0 ≤ PolarFace.orientedNormal n s i ⬝ᵥ y := by
    simpa [PolarFace.orientedNormal_dot] using hy i
  rw [orientedSum, sum_dotProduct]
  by_contra hnot
  have hallzero (i : I) : PolarFace.orientedNormal n s i ⬝ᵥ y = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hi
      apply hnot
      exact Finset.sum_pos' (fun j _ ↦ hnonneg j)
        ⟨i, Finset.mem_univ i, hi⟩
    · exact hnonneg i
  let L : Vec3 →ₗ[ℝ] ℝ :=
    { toFun := fun z ↦ z ⬝ᵥ y
      map_add' := by intro u v; simp [add_dotProduct]
      map_smul' := by intro a z; simp [smul_dotProduct] }
  have hnker : Set.range n ⊆ L.ker := by
    rintro z ⟨i, rfl⟩
    change n i ⬝ᵥ y = 0
    have hi := hallzero i
    cases hs : s i <;> simp [PolarFace.orientedNormal,
      PolarFace.signScalar, hs] at hi ⊢ <;> exact hi
  have hhker : h ∈ L.ker := hhy
  have hins : Set.insert h (Set.range n) ⊆ L.ker := by
    intro z hz
    rcases hz with rfl | hz
    · exact hhker
    · exact hnker hz
  have hle : Submodule.span ℝ (Set.insert h (Set.range n)) ≤ L.ker :=
    (Submodule.span_le).2 hins
  rw [hspan] at hle
  have hself : y ⬝ᵥ y = 0 := hle (by simp)
  exact hy0 (dotProduct_self_eq_zero.mp hself)

private theorem projective_eq_lower_or_upper_of_weak
    (B : Finset Point) {a b c : Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (pick : OtherLineChoice (Line B))
    (e : ProjectiveStrictEdge pick (normals B))
    (y : Vec3) (hy0 : y ≠ 0)
    (hyowner : normals B e.1.1.1 ⬝ᵥ y = 0)
    (hyweak : WeaklyRealizes
      (otherNormals (normals B) e.1.1.1) e.1.1.2 y)
    (hyvertex : Projectivization.mk ℝ y hy0 ∈ projectiveVertices B) :
    Projectivization.mk ℝ y hy0 =
        lowerEdgeProjectiveEndpoint B ha hb hc hncol pick e ∨
      Projectivization.mk ℝ y hy0 =
        upperEdgeProjectiveEndpoint B ha hb hc hncol pick e := by
  let : Nonempty {j : Line B // j ≠ e.1.1.1} := ⟨pick e.1.1.1⟩
  let n := otherNormals (normals B) e.1.1.1
  let s := e.1.1.2
  let h := normals B e.1.1.1
  let x := edgeWitness B pick e
  let D := edgeEndpointData B ha hb hc hncol pick e
  have hx : Realizes n s x := edgeWitness_realizes B pick e
  have hhx : h ⬝ᵥ x = 0 := edgeWitness_on_owner B pick e
  have hspan : Submodule.span ℝ (Set.insert h (Set.range n)) = ⊤ := by
    exact span_insert_otherNormals_eq_top B ha hb hc hncol e.1.1.1
  have hsumx : 0 < orientedSum n s ⬝ᵥ x := by
    rw [orientedSum, sum_dotProduct]
    exact Finset.sum_pos (fun i _ ↦ by
      simpa [PolarFace.orientedNormal_dot] using hx i) Finset.univ_nonempty
  have hsumy : 0 < orientedSum n s ⬝ᵥ y :=
    orientedSum_dot_pos_of_weak_of_insertSpan hspan hy0 hyowner hyweak
  let q : ℝ := (orientedSum n s ⬝ᵥ x) / (orientedSum n s ⬝ᵥ y)
  have hq : 0 < q := div_pos hsumx hsumy
  let y' : Vec3 := q • y
  have hy'0 : y' ≠ 0 := smul_ne_zero hq.ne' hy0
  have hy'weak : WeaklyRealizes n s y' := by
    intro i
    have hi := hyweak i
    have hid : signed (s i) (n i ⬝ᵥ y') =
        q * signed (s i) (n i ⬝ᵥ y) := by
      cases hs : s i <;>
        simp [y', signed, hs, dotProduct_smul, smul_eq_mul]
    rw [hid]
    exact mul_nonneg hq.le hi
  let v : Vertex B := ⟨Projectivization.mk ℝ y hy0, hyvertex⟩
  have hynreal : ¬ Realizes n s y := by
    intro hyr
    obtain ⟨j, hjne, hvj⟩ := exists_other_incident_line B v e.1.1.1
    let jj : {j : Line B // j ≠ e.1.1.1} := ⟨j, hjne⟩
    have hjzero : n jj ⬝ᵥ y = 0 := by
      change normalVec j.1 ⬝ᵥ y = 0
      apply (onProjectiveLine_mk_iff _ _ hy0).mp
      exact hvj
    have hjpos := hyr jj
    cases hs : s jj <;> simp [signed, hs, hjzero] at hjpos
  have hy'nreal : ¬ Realizes n s y' := by
    intro hyr
    exact hynreal (realizes_of_realizes_pos_smul hq hyr)
  have hhdiff : h ⬝ᵥ (y' - x) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hyowner, hhx, smul_eq_mul,
      mul_zero, sub_self]
  have hsumdiff : orientedSum n s ⬝ᵥ (y' - x) = 0 := by
    have hqy : q * (orientedSum n s ⬝ᵥ y) =
        orientedSum n s ⬝ᵥ x := by
      dsimp [q]
      field_simp [hsumy.ne']
    simp [y', dotProduct_sub, dotProduct_smul, smul_eq_mul, hqy]
  obtain ⟨t, ht⟩ := eq_smul_cross_of_dot_eq_zero
    D.direction_ne_zero hhdiff hsumdiff
  have hyparam : y' = chartPoint n s h x t := by
    calc
      y' = x + (y' - x) := by abel
      _ = x + t • (h ⨯₃ orientedSum n s) := by rw [ht]
      _ = chartPoint n s h x t := by rfl
  have htend : t = lowerEndpoint n s h x D.lower_nonempty ∨
      t = upperEndpoint n s h x D.upper_nonempty := by
    apply (D.boundary_iff t).mp
    rw [← hyparam]
    exact ⟨hy'weak, hy'nreal⟩
  have hprojscale : Projectivization.mk ℝ y' hy'0 =
      Projectivization.mk ℝ y hy0 := by
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hy'0 hy0).2
    exact ⟨q, by rfl⟩
  rcases htend with rfl | rfl
  · left
    rw [← hprojscale]
    have hyparam' : y' = chartPoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e)
        (lowerEndpoint (otherNormals (normals B) e.1.1.1) e.1.1.2
          (normals B e.1.1.1) (edgeWitness B pick e) D.lower_nonempty) := by
      simpa only [n, s, h, x] using hyparam
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hy'0
      (chartPoint_ne_zero hx _)).2
    exact ⟨1, by simpa only [one_smul] using hyparam'.symm⟩
  · right
    rw [← hprojscale]
    have hyparam' : y' = chartPoint
        (otherNormals (normals B) e.1.1.1) e.1.1.2
        (normals B e.1.1.1) (edgeWitness B pick e)
        (upperEndpoint (otherNormals (normals B) e.1.1.1) e.1.1.2
          (normals B e.1.1.1) (edgeWitness B pick e) D.upper_nonempty) := by
      simpa only [n, s, h, x] using hyparam
    apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hy'0
      (chartPoint_ne_zero hx _)).2
    exact ⟨1, by simpa only [one_smul] using hyparam'.symm⟩

private theorem normalize_projective_eq_lower_or_upper
    (B : Finset Point) {a b c : Point}
    [Nonempty (Line B)]
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (pick : OtherLineChoice (Line B))
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)
    (e : StrictEdge (normals B))
    (v : OrientedVertex B) (hv : v ∈ concreteEdgeVertices hspan e) :
    v.1.1 = lowerEdgeProjectiveEndpoint B ha hb hc hncol pick
          (normalizeProjectiveEdge pick (normals B) e) ∨
      v.1.1 = upperEdgeProjectiveEndpoint B ha hb hc hncol pick
          (normalizeProjectiveEdge pick (normals B) e) := by
  have hvinc := concreteEdgeVertex_on_support hspan e v hv
  have hvweak := concreteEdgeVertex_weaklyRealizes_restriction hspan e v hv
  have hyowner : normals B e.1.1 ⬝ᵥ orientedRep v = 0 := by
    apply (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).mp
    rw [orientedRep_projectivization]
    exact hvinc
  by_cases he : IsPositiveEdgeRepresentative pick (normals B) e
  · have hep : normalizeProjectiveEdge pick (normals B) e = ⟨e, he⟩ := by
      simp [normalizeProjectiveEdge, he]
    have hvprojective : Projectivization.mk ℝ (orientedRep v)
        (orientedRep_ne_zero v) ∈ projectiveVertices B := by
      rw [orientedRep_projectivization]
      exact v.1.2
    have hends := projective_eq_lower_or_upper_of_weak B ha hb hc hncol pick
      ⟨e, he⟩ (orientedRep v) (orientedRep_ne_zero v) hyowner hvweak
        hvprojective
    simpa [hep, orientedRep_projectivization] using hends
  · let y : Vec3 := -orientedRep v
    have hy0 : y ≠ 0 := neg_ne_zero.mpr (orientedRep_ne_zero v)
    have hyowner : normals B e.1.1 ⬝ᵥ y = 0 := by
      simp [y, dotProduct_neg, hyowner]
    have hyweak : WeaklyRealizes
        (otherNormals (normals B) e.1.1)
        (antipodalSign e.1.2) y := by
      intro j
      have hj := hvweak j
      cases hs : e.1.2 j <;>
        simpa [y, antipodalSign, signed, hs, dotProduct_neg] using hj
    have hep : normalizeProjectiveEdge pick (normals B) e =
        ⟨antipodalEdge (normals B) e,
          (antipodalEdge_isPositive_iff pick (normals B) e).2 he⟩ := by
      simp [normalizeProjectiveEdge, he]
    let ep : ProjectiveStrictEdge pick (normals B) :=
      ⟨antipodalEdge (normals B) e,
        (antipodalEdge_isPositive_iff pick (normals B) e).2 he⟩
    have hyproj : Projectivization.mk ℝ y hy0 = v.1.1 := by
      calc
        Projectivization.mk ℝ y hy0 =
            Projectivization.mk ℝ (orientedRep v) (orientedRep_ne_zero v) := by
          apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hy0
            (orientedRep_ne_zero v)).2
          exact ⟨-1, by simp [y]⟩
        _ = v.1.1 := orientedRep_projectivization v
    have hepowner : normals B ep.1.1.1 ⬝ᵥ y = 0 := by
      exact hyowner
    have hepweak : WeaklyRealizes
        (otherNormals (normals B) ep.1.1.1) ep.1.1.2 y := by
      change WeaklyRealizes (otherNormals (normals B) e.1.1)
        (antipodalSign e.1.2) y
      exact hyweak
    have hepvertex : Projectivization.mk ℝ y hy0 ∈ projectiveVertices B := by
      rw [hyproj]
      exact v.1.2
    have hends := projective_eq_lower_or_upper_of_weak B ha hb hc hncol pick
      ep y hy0 hepowner hepweak hepvertex
    simpa [hep, ep, hyproj] using hends

/-- The projective images of the two literal polar endpoints of a strict
edge are precisely the endpoints of its genuine projective cyclic edge. -/
theorem strictEdgeLiftedCyclicEquiv_projectiveVertices_eq_concrete
    (B : Finset Point) {a b c : Point}
    [Nonempty (Line B)]
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    (pick : OtherLineChoice (Line B))
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)
    (e : StrictEdge (normals B)) :
    cyclicEdgeVertices (Finset.univ : Finset (Vertex B)) (OnLine B)
        (vertexCoord B) (strictEdgeLiftedCyclicEquiv
          B ha hb hc hncol pick e).1 =
      (concreteEdgeVertices hspan e).image Prod.fst := by
  let target := cyclicEdgeVertices (Finset.univ : Finset (Vertex B)) (OnLine B)
    (vertexCoord B) (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1
  have hsub : (concreteEdgeVertices hspan e).image Prod.fst ⊆ target := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    have hends := normalize_projective_eq_lower_or_upper
      B ha hb hc hncol pick hspan e v hv
    change v.1 ∈ cyclicEdgeVertices (Finset.univ : Finset (Vertex B))
      (OnLine B) (vertexCoord B)
        (strictEdgeLiftedCyclicEquiv B ha hb hc hncol pick e).1
    rw [strictEdgeLiftedCyclicEquiv_projectiveVertices]
    rcases hends with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr
        (Subtype.ext h)))
  have htarget : target.card = 2 := by
    apply cyclicEdgeVertices_card
    · exact vertexCoord_injective B
    · exact two_vertices_on_every_line B ha hb hc hncol
  have himage : ((concreteEdgeVertices hspan e).image Prod.fst).card = 2 := by
    let d := canonicalDart hspan e
    change ((orientedEdgeVertices hspan d.1 d.2).image Prod.fst).card = 2
    simp only [orientedEdgeVertices, Finset.image_insert, Finset.image_singleton]
    rw [Finset.card_pair]
    intro heq
    exact boundaryVertex_ne_succ hspan d.1 d.2
      (congrArg Subtype.val heq)
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [htarget, himage])).symm

end Erdos735.ConcreteStrictEdgeCyclic
