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

import ErdosProblems.Erdos735.ConcreteDonationPacking
import ErdosProblems.Erdos735.ConcreteDoubleCornerSector
import ErdosProblems.Erdos735.ConcretePolarRecognition
import ErdosProblems.Erdos735.ConcretePolarFlankBounds
import ErdosProblems.Erdos735.Stage4OppositeLine

/-!
# Recognition from opposite triangles at a bad quadrangle

If triangles occur across opposite sides of a bad two-diagonal
quadrangle, either intervening boundary owner has three consecutive
projective edges: the quadrangle edge and one continuation edge in each
triangle.  The two endpoints on the quadrangle are double.  The concrete
three-edge recognition theorem therefore gives failed Fano.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix

namespace Erdos735.OppositeTriangleRecognition

open ChartOrder ProjectiveArrangement ProjectiveBoundaryExtraction
open SignVector ConcretePolarOrientedVertex ConcretePolarEdgeVertices
open ConcretePolarFlankBounds

universe uV uE uF

/-- The two non-shared sides of a triangle, organized by the two endpoints
of its shared side.  This is a purely cyclic-cellulation lemma. -/
private theorem triangle_other_edges_at_shared_endpoints
    {Vertex : Type uV} {Edge : Type uE} {Face : Type uF}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    {C : BlueCellulation Vertex Edge Face} (A : ABKPR.Data C)
    {t : Face} (ht : C.faceDegree t = 3)
    (k : Fin (C.faceDegree t))
    (a b : Vertex) (hab : a ≠ b)
    (hpair : C.edgeVertices (A.boundaryEdge t k) = {a, b}) :
    ∃ ka kb : Fin (C.faceDegree t), ∃ x : Vertex,
      ka ≠ k ∧ kb ≠ k ∧ ka ≠ kb ∧
      C.edgeVertices (A.boundaryEdge t ka) = {x, a} ∧
      C.edgeVertices (A.boundaryEdge t kb) = {b, x} := by
  let k₁ := ABKPR.faceSucc C t k
  let k₂ := ABKPR.faceSucc C t k₁
  have hk₁ne : k₁ ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    simp only [k₁, ABKPR.faceSucc, ABKPR.cyclicSucc] at hv
    simp only [ht] at hv
    omega
  have hk₂ne : k₂ ≠ k := by
    intro h
    have hv := congrArg Fin.val h
    simp only [k₁, k₂, ABKPR.faceSucc, ABKPR.cyclicSucc] at hv
    simp only [ht] at hv
    omega
  have hk₁k₂ : k₁ ≠ k₂ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [k₁, k₂, ABKPR.faceSucc, ABKPR.cyclicSucc] at hv
    simp only [ht] at hv
    omega
  have hcycle : ABKPR.faceSucc C t k₂ = k := by
    apply Fin.ext
    simp only [k₁, k₂, ABKPR.faceSucc, ABKPR.cyclicSucc]
    simp only [ht]
    omega
  have hpair' :
      ({A.boundaryVertex t k, A.boundaryVertex t k₁} : Finset Vertex) =
        {a, b} := by
    simpa only [A.boundaryEdge_vertices, k₁] using hpair
  have ha : a = A.boundaryVertex t k ∨ a = A.boundaryVertex t k₁ := by
    have hamem : a ∈
        ({A.boundaryVertex t k, A.boundaryVertex t k₁} : Finset Vertex) := by
      rw [hpair']
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hamem
  have hb : b = A.boundaryVertex t k ∨ b = A.boundaryVertex t k₁ := by
    have hbmem : b ∈
        ({A.boundaryVertex t k, A.boundaryVertex t k₁} : Finset Vertex) := by
      rw [hpair']
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hbmem
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hab (ha.trans hb.symm))
  · refine ⟨k₂, k₁, A.boundaryVertex t k₂,
      hk₂ne, hk₁ne, hk₁k₂.symm, ?_, ?_⟩
    · rw [A.boundaryEdge_vertices, hcycle, ha]
    · rw [A.boundaryEdge_vertices, hb]
  · refine ⟨k₁, k₂, A.boundaryVertex t k₂,
      hk₁ne, hk₂ne, hk₁k₂, ?_, ?_⟩
    · rw [A.boundaryEdge_vertices, ha]
      exact Finset.pair_comm _ _
    · rw [A.boundaryEdge_vertices, hcycle, hb]
      exact Finset.pair_comm _ _
  · exact False.elim (hab (ha.trans hb.symm))

abbrev Point := ProjectiveArrangement.Point
private abbrev B {P : Finset Point} := nonordinaryPoints P
private abbrev C {P : Finset Point} {a b d : Point}
    (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P)) (hd : d ∈ B (P := P))
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :=
  ConcretePolarCellulation.blueCellulation (B (P := P)) ha hb hd hncol
private abbrev D {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c) {a b d : Point}
    (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P)) (hd : d ∈ B (P := P))
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :=
  ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev hs {P : Finset Point} {a b d : Point}
    (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P)) (hd : d ∈ B (P := P))
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :
    Submodule.span ℝ (Set.range (normals (B (P := P)))) = ⊤ :=
  ConcretePolarABKPRData.hspan ha hb hd hncol

section Concrete

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ B (P := P)) (hb : b ∈ B (P := P))
variable (hd : d ∈ B (P := P))
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (B (P := P)))]

private noncomputable def pick : OtherLineChoice
    (ProjectiveBoundaryExtraction.Line (B (P := P))) :=
  otherLineChoiceOfPair ⟨a, ha⟩ ⟨b, hb⟩ (by
    intro hab
    apply hncol
    have : a = b := congrArg Subtype.val hab
    subst b
    simp [ProjectiveDuality.Collinear3, ProjectiveDuality.orientationDet])

private theorem projectiveEdgeVertices_card_eq_two
    (e : StrictEdge (normals (B (P := P)))) :
    ((concreteEdgeVertices (hs ha hb hd hncol) e).image Prod.fst).card = 2 := by
  let q := ConcretePolarEdgeVertices.canonicalDart (hs ha hb hd hncol) e
  change ((orientedEdgeVertices (hs ha hb hd hncol) q.1 q.2).image Prod.fst).card = 2
  simp only [orientedEdgeVertices, Finset.image_insert, Finset.image_singleton]
  rw [Finset.card_pair]
  intro heq
  exact boundaryVertex_ne_succ (hs ha hb hd hncol) q.1 q.2
    (congrArg Subtype.val heq)

/-- A bad quadrangle with triangles across opposite edges is the dual
failed-Fano arrangement. -/
theorem isFailedFano_of_oppositeTrianglesAtBadQuadrangle
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hop : ConcreteDonationPacking.OppositeTrianglesAtBadQuadrangle
      (D hred ha hb hd hncol)) :
    IsFailedFano P := by
  let CC := C ha hb hd hncol
  let DD := D hred ha hb hd hncol
  rcases hop with ⟨q, hbad, i₀, i₂, htri₀, htri₂, hi₂⟩
  let i₁ := ABKPR.faceSucc CC q i₀
  let i₃ := ABKPR.faceSucc CC q i₂
  have hqdeg : CC.faceDegree q = 4 := hbad.1.1
  have hi₂def : i₂ = ABKPR.faceSucc CC q i₁ := by
    exact hi₂
  have hi₃cycle : ABKPR.faceSucc CC q i₃ = i₀ := by
    subst i₂
    exact ABKPR.faceSucc_four_of_faceDegree_eq_four CC hqdeg i₀
  have hi₀ne₁ : i₀ ≠ i₁ := by
    intro h
    exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC hqdeg i₀ h.symm
  have hi₁ne₂ : i₁ ≠ i₂ := by
    rw [hi₂def]
    exact (ABKPR.faceSucc_ne_of_faceDegree_eq_four CC hqdeg i₁).symm
  have hi₂ne₃ : i₂ ≠ i₃ := by
    exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC hqdeg i₂ |>.symm
  have hi₃ne₀ : i₃ ≠ i₀ := by
    intro h
    exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC hqdeg i₃
      (hi₃cycle.trans h.symm)
  have hi₀ne₂ : i₀ ≠ i₂ := by
    rw [hi₂def]
    simpa only [i₁] using
      (ABKPR.secondSucc_ne_of_faceDegree_eq_four CC hqdeg i₀).symm
  have hi₁ne₃ : i₁ ≠ i₃ := by
    intro h
    apply hi₀ne₂
    calc
      i₀ = ABKPR.faceSucc CC q i₃ := hi₃cycle.symm
      _ = ABKPR.faceSucc CC q i₁ := congrArg (ABKPR.faceSucc CC q) h.symm
      _ = i₂ := hi₂def.symm
  let v₀ := DD.boundaryVertex q i₀
  let v₁ := DD.boundaryVertex q i₁
  let v₂ := DD.boundaryVertex q i₂
  let v₃ := DD.boundaryVertex q i₃
  have hv₀v₁ : v₀ ≠ v₁ := fun h ↦ hi₀ne₁ (DD.boundaryVertex_injective q h)
  have hv₁v₂ : v₁ ≠ v₂ := fun h ↦ hi₁ne₂ (DD.boundaryVertex_injective q h)
  have hv₂v₃ : v₂ ≠ v₃ := fun h ↦ hi₂ne₃ (DD.boundaryVertex_injective q h)
  let t₀ := (DD.across ⟨q, i₀⟩).1
  let k₀ := (DD.across ⟨q, i₀⟩).2
  let t₂ := (DD.across ⟨q, i₂⟩).1
  let k₂ := (DD.across ⟨q, i₂⟩).2
  have hpair₀ : CC.edgeVertices (DD.boundaryEdge t₀ k₀) = {v₀, v₁} := by
    rw [← DD.across_sameEdge ⟨q, i₀⟩, DD.boundaryEdge_vertices]
  have hpair₂ : CC.edgeVertices (DD.boundaryEdge t₂ k₂) = {v₂, v₃} := by
    rw [← DD.across_sameEdge ⟨q, i₂⟩, DD.boundaryEdge_vertices]
  obtain ⟨ka₀, kb₀, x₀, hka₀, hkb₀, hkab₀,
      hpaira₀, hpairb₀⟩ :=
    triangle_other_edges_at_shared_endpoints DD htri₀ k₀ v₀ v₁
      hv₀v₁ hpair₀
  obtain ⟨ka₂, kb₂, x₂, hka₂, hkb₂, hkab₂,
      hpaira₂, hpairb₂⟩ :=
    triangle_other_edges_at_shared_endpoints DD htri₂ k₂ v₂ v₃
      hv₂v₃ hpair₂
  let e₀ := DD.boundaryEdge q i₀
  let e₁ := DD.boundaryEdge q i₁
  let e₂ := DD.boundaryEdge q i₂
  let e₃ := DD.boundaryEdge q i₃
  let ea₀ := DD.boundaryEdge t₀ ka₀
  let eb₀ := DD.boundaryEdge t₀ kb₀
  let ea₂ := DD.boundaryEdge t₂ ka₂
  let eb₂ := DD.boundaryEdge t₂ kb₂
  let l₀ := edgeLine e₀
  let l₁ := edgeLine e₁
  let l₂ := edgeLine e₂
  let l₃ := edgeLine e₃
  have hl₀ne₁ : l₀ ≠ l₁ := by
    intro h
    exact hi₀ne₁ (data_boundary_edgeLine_injective hred ha hb hd hncol q h)
  have hl₂ne₁ : l₂ ≠ l₁ := by
    intro h
    exact hi₁ne₂ (data_boundary_edgeLine_injective hred ha hb hd hncol q h.symm)
  have hl₀ne₃ : l₀ ≠ l₃ := by
    intro h
    exact hi₃ne₀ (data_boundary_edgeLine_injective hred ha hb hd hncol q h.symm)
  have hl₂ne₃ : l₂ ≠ l₃ := by
    intro h
    exact hi₂ne₃ (data_boundary_edgeLine_injective hred ha hb hd hncol q h)
  have hl₁ne₃ : l₁ ≠ l₃ := by
    intro h
    exact hi₁ne₃ (data_boundary_edgeLine_injective hred ha hb hd hncol q h)
  have hmult₀ : lineMultiplicity (OnLine (B (P := P))) v₀.1 = 2 :=
    DD.badTwo_boundaryVertex_multiplicity_two hbad i₀
  have hmult₁ : lineMultiplicity (OnLine (B (P := P))) v₁.1 = 2 :=
    DD.badTwo_boundaryVertex_multiplicity_two hbad i₁
  have hmult₂ : lineMultiplicity (OnLine (B (P := P))) v₂.1 = 2 :=
    DD.badTwo_boundaryVertex_multiplicity_two hbad i₂
  have hmult₃ : lineMultiplicity (OnLine (B (P := P))) v₃.1 = 2 :=
    DD.badTwo_boundaryVertex_multiplicity_two hbad i₃
  have line_on {e : StrictEdge (normals (B (P := P)))}
      {v : OrientedVertex (B (P := P))}
      (hv : v ∈ CC.edgeVertices e) :
      OnLine (B (P := P)) v.1 (edgeLine e) := by
    exact concreteEdgeVertex_on_support (hs ha hb hd hncol) e v hv
  have hv₀e₀ : v₀ ∈ CC.edgeVertices e₀ := by
    rw [DD.boundaryEdge_vertices]
    simp [v₀]
  have hv₁e₀ : v₁ ∈ CC.edgeVertices e₀ := by
    rw [DD.boundaryEdge_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    rfl
  have hv₁e₁ : v₁ ∈ CC.edgeVertices e₁ := by
    rw [DD.boundaryEdge_vertices]
    simp [v₁]
  have hv₂e₁ : v₂ ∈ CC.edgeVertices e₁ := by
    rw [DD.boundaryEdge_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    exact congrArg (DD.boundaryVertex q) hi₂def
  have hv₂e₂ : v₂ ∈ CC.edgeVertices e₂ := by
    rw [DD.boundaryEdge_vertices]
    simp [v₂]
  have hv₃e₂ : v₃ ∈ CC.edgeVertices e₂ := by
    rw [DD.boundaryEdge_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    rfl
  have hv₃e₃ : v₃ ∈ CC.edgeVertices e₃ := by
    rw [DD.boundaryEdge_vertices]
    simp [v₃]
  have hv₀e₃ : v₀ ∈ CC.edgeVertices e₃ := by
    rw [DD.boundaryEdge_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    exact congrArg (DD.boundaryVertex q) hi₃cycle.symm
  have hv₀ea₀ : v₀ ∈ CC.edgeVertices ea₀ := by rw [hpaira₀]; simp
  have hv₁eb₀ : v₁ ∈ CC.edgeVertices eb₀ := by rw [hpairb₀]; simp
  have hv₂ea₂ : v₂ ∈ CC.edgeVertices ea₂ := by rw [hpaira₂]; simp
  have hv₃eb₂ : v₃ ∈ CC.edgeVertices eb₂ := by rw [hpairb₂]; simp
  have hea₀ne₀ : edgeLine ea₀ ≠ l₀ := by
    intro h
    have hshared : edgeLine (DD.boundaryEdge t₀ k₀) = l₀ :=
      congrArg edgeLine (DD.across_sameEdge ⟨q, i₀⟩).symm
    exact hka₀ (data_boundary_edgeLine_injective hred ha hb hd hncol t₀
      (h.trans hshared.symm))
  have heb₀ne₀ : edgeLine eb₀ ≠ l₀ := by
    intro h
    have hshared : edgeLine (DD.boundaryEdge t₀ k₀) = l₀ :=
      congrArg edgeLine (DD.across_sameEdge ⟨q, i₀⟩).symm
    exact hkb₀ (data_boundary_edgeLine_injective hred ha hb hd hncol t₀
      (h.trans hshared.symm))
  have hea₂ne₂ : edgeLine ea₂ ≠ l₂ := by
    intro h
    have hshared : edgeLine (DD.boundaryEdge t₂ k₂) = l₂ :=
      congrArg edgeLine (DD.across_sameEdge ⟨q, i₂⟩).symm
    exact hka₂ (data_boundary_edgeLine_injective hred ha hb hd hncol t₂
      (h.trans hshared.symm))
  have heb₂ne₂ : edgeLine eb₂ ≠ l₂ := by
    intro h
    have hshared : edgeLine (DD.boundaryEdge t₂ k₂) = l₂ :=
      congrArg edgeLine (DD.across_sameEdge ⟨q, i₂⟩).symm
    exact hkb₂ (data_boundary_edgeLine_injective hred ha hb hd hncol t₂
      (h.trans hshared.symm))
  have hea₀line : edgeLine ea₀ = l₃ :=
    ConcreteDoubleCornerSector.other_incident_line_eq_of_multiplicity_two
      v₀.1 l₀ l₃ (edgeLine ea₀) hmult₀
      (line_on hv₀e₀) (line_on hv₀e₃) (line_on hv₀ea₀)
      hl₀ne₃ hea₀ne₀
  have heb₀line : edgeLine eb₀ = l₁ :=
    ConcreteDoubleCornerSector.other_incident_line_eq_of_multiplicity_two
      v₁.1 l₀ l₁ (edgeLine eb₀) hmult₁
      (line_on hv₁e₀) (line_on hv₁e₁) (line_on hv₁eb₀)
      hl₀ne₁ heb₀ne₀
  have hea₂line : edgeLine ea₂ = l₁ :=
    ConcreteDoubleCornerSector.other_incident_line_eq_of_multiplicity_two
      v₂.1 l₂ l₁ (edgeLine ea₂) hmult₂
      (line_on hv₂e₂) (line_on hv₂e₁) (line_on hv₂ea₂)
      hl₂ne₁ hea₂ne₂
  have heb₂line : edgeLine eb₂ = l₃ :=
    ConcreteDoubleCornerSector.other_incident_line_eq_of_multiplicity_two
      v₃.1 l₂ l₃ (edgeLine eb₂) hmult₃
      (line_on hv₃e₂) (line_on hv₃e₃) (line_on hv₃eb₂)
      hl₂ne₃ heb₂ne₂
  have hx₀ea₀ : x₀ ∈ CC.edgeVertices ea₀ := by rw [hpaira₀]; simp
  have hx₀eb₀ : x₀ ∈ CC.edgeVertices eb₀ := by rw [hpairb₀]; simp
  have hx₂ea₂ : x₂ ∈ CC.edgeVertices ea₂ := by rw [hpaira₂]; simp
  have hx₂eb₂ : x₂ ∈ CC.edgeVertices eb₂ := by rw [hpairb₂]; simp
  have hxproj : x₀.1 = x₂.1 := by
    apply Subtype.ext
    apply ProjectiveArrangement.eq_of_two_common_lines
      (fun h ↦ hl₁ne₃ (Subtype.ext h))
    · have h := line_on hx₀eb₀
      change Incident x₀.1.1 (edgeLine eb₀).1 at h
      rw [heb₀line] at h
      exact h
    · have h := line_on hx₀ea₀
      change Incident x₀.1.1 (edgeLine ea₀).1 at h
      rw [hea₀line] at h
      exact h
    · have h := line_on hx₂ea₂
      change Incident x₂.1.1 (edgeLine ea₂).1 at h
      rw [hea₂line] at h
      exact h
    · have h := line_on hx₂eb₂
      change Incident x₂.1.1 (edgeLine eb₂).1 at h
      rw [heb₂line] at h
      exact h
  let pv₁ : ProjectiveBoundaryExtraction.Vertex (B (P := P)) := v₁.1
  let pv₂ : ProjectiveBoundaryExtraction.Vertex (B (P := P)) := v₂.1
  let px : ProjectiveBoundaryExtraction.Vertex (B (P := P)) := x₀.1
  have hpair₁₂ :
      (concreteEdgeVertices (hs ha hb hd hncol) e₁).image Prod.fst =
        {pv₁, pv₂} := by
    change (CC.edgeVertices e₁).image Prod.fst = _
    rw [DD.boundaryEdge_vertices]
    simp only [Finset.image_insert, Finset.image_singleton]
    change ({v₁.1,
      (DD.boundaryVertex q (ABKPR.faceSucc CC q i₁)).1} :
        Finset (ProjectiveBoundaryExtraction.Vertex (B (P := P)))) =
      {v₁.1, v₂.1}
    rw [← hi₂def]
  have hpair₂x :
      (concreteEdgeVertices (hs ha hb hd hncol) ea₂).image Prod.fst =
        {pv₂, px} := by
    change (CC.edgeVertices ea₂).image Prod.fst = _
    rw [hpaira₂]
    simp only [Finset.image_insert, Finset.image_singleton]
    change ({x₂.1, v₂.1} : Finset
      (ProjectiveBoundaryExtraction.Vertex (B (P := P)))) = {v₂.1, x₀.1}
    rw [← hxproj]
    exact Finset.pair_comm _ _
  have hpairx₁ :
      (concreteEdgeVertices (hs ha hb hd hncol) eb₀).image Prod.fst =
        {px, pv₁} := by
    change (CC.edgeVertices eb₀).image Prod.fst = _
    rw [hpairb₀]
    simp only [Finset.image_insert, Finset.image_singleton]
    exact Finset.pair_comm _ _
  have hpv₁pv₂ : pv₁ ≠ pv₂ := by
    intro h
    have hc := projectiveEdgeVertices_card_eq_two ha hb hd hncol e₁
    rw [hpair₁₂, h] at hc
    simp at hc
  have hpv₂x : pv₂ ≠ px := by
    intro h
    have hc := projectiveEdgeVertices_card_eq_two ha hb hd hncol ea₂
    rw [hpair₂x, h] at hc
    simp at hc
  have hpv₁x : pv₁ ≠ px := by
    intro h
    have hc := projectiveEdgeVertices_card_eq_two ha hb hd hncol eb₀
    rw [hpairx₁, ← h] at hc
    simp at hc
  exact ConcretePolarRecognition.isFailedFano_of_three_literal_edges_two_double
    hred hAcard ha hb hd hncol (pick ha hb hncol)
    l₁ pv₁ pv₂ px hpv₁pv₂ hpv₁x hpv₂x
    e₁ ea₂ eb₀ rfl hea₂line heb₀line
    hpair₁₂ hpair₂x hpairx₁ hmult₁ hmult₂

/-- Argument-expanded form, convenient when the two triangular faces have
already been constructed as explicit opposite darts of a bad quadrangle. -/
theorem isFailedFano_of_badQuadrangle_opposite_triangles
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (q : StrictFace (normals (B (P := P))))
    (hbad : (D hred ha hb hd hncol).IsBadTwoQuadrangle q)
    (i j : Fin ((C ha hb hd hncol).faceDegree q))
    (htriᵢ : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across ⟨q, i⟩).1 = 3)
    (htriⱼ : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across ⟨q, j⟩).1 = 3)
    (hopposite : j = ABKPR.faceSucc (C ha hb hd hncol) q
      (ABKPR.faceSucc (C ha hb hd hncol) q i)) :
    IsFailedFano P := by
  apply isFailedFano_of_oppositeTrianglesAtBadQuadrangle
    hred ha hb hd hncol hAcard
  exact ConcreteDonationPacking.OppositeTrianglesAtBadQuadrangle.intro
    q hbad i j htriᵢ htriⱼ hopposite

/-- A collision of two canonical donation edges is therefore a direct
failed-Fano exit. -/
theorem isFailedFano_of_donationEdgeCollision
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (f : StrictFace (normals (B (P := P))))
    (x y : (D hred ha hb hd hncol).donationRecipients f)
    (hxy : x ≠ y)
    (hedge : (D hred ha hb hd hncol).donationEdgeOfGeometry f x =
      (D hred ha hb hd hncol).donationEdgeOfGeometry f y) :
    IsFailedFano P := by
  apply isFailedFano_of_oppositeTrianglesAtBadQuadrangle
    hred ha hb hd hncol hAcard
  exact ConcreteDonationPacking.oppositeTriangles_of_donationEdgeCollision
    hred ha hb hd hncol f x y hxy hedge

end Concrete

end Erdos735.OppositeTriangleRecognition
