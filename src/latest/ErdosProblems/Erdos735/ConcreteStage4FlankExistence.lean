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

import ErdosProblems.Erdos735.Stage4FlankExistence
import ErdosProblems.Erdos735.ConcretePolarFlankBounds
import ErdosProblems.Erdos735.ConcreteStage3Local
import ErdosProblems.Erdos735.Stage4OppositeLine
import ErdosProblems.Erdos735.ConcretePolarAcrossSquare
import ErdosProblems.Erdos735.TriangleExceptionCardinality

/-!
# Concrete existence of Stage-4 flank edges

At either endpoint of the bad edge belonging to an evil triangle, exactly
two projective blue lines occur.  Consequently, after crossing an adjacent
edge of the bad quadrangle, the other boundary edge at the transported
corner has the same owner as the evil edge.  This file records that literal
polar construction and packages every zero-diagonal flank whose continuation
is not bad as a concrete helping pair.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization Matrix

namespace Erdos735.ConcreteStage4FlankExistence

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices

abbrev Point := ProjectiveArrangement.Point

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol
private abbrev hspan : Submodule.span ℝ
    (Set.range (normals (B (P := P)))) = ⊤ :=
  ConcretePolarABKPRData.hspan ha hb hd hncol

private theorem line_eq_of_multiplicity_two
    (v : ProjectiveBoundaryExtraction.Vertex (B (P := P)))
    (l₀ l₁ l : ProjectiveBoundaryExtraction.Line (B (P := P)))
    (hmult : lineMultiplicity (OnLine (B (P := P))) v = 2)
    (hl₀ : OnLine (B (P := P)) v l₀)
    (hl₁ : OnLine (B (P := P)) v l₁)
    (hl : OnLine (B (P := P)) v l)
    (h₀₁ : l₀ ≠ l₁) (hl₀ne : l ≠ l₀) : l = l₁ := by
  let S := Finset.univ.filter fun q :
    ProjectiveBoundaryExtraction.Line (B (P := P)) ↦
      OnLine (B (P := P)) v q
  have hpair : ({l₀, l₁} : Finset
      (ProjectiveBoundaryExtraction.Line (B (P := P)))) ⊆ S := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [S, hl₀, hl₁]
  have hcard : S.card = 2 := hmult
  have hpCard : ({l₀, l₁} : Finset
      (ProjectiveBoundaryExtraction.Line (B (P := P)))).card = 2 :=
    Finset.card_pair h₀₁
  have heq : S = {l₀, l₁} := by
    exact Finset.Subset.antisymm
      (Finset.eq_of_subset_of_card_le hpair (by omega) |>.symm.subset) hpair
  have hlmem : l ∈ S := by simp [S, hl]
  rw [heq] at hlmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlmem
  exact hlmem.resolve_left hl₀ne

private theorem faceSucc_three_of_faceDegree_eq_three
    {Vertex Edge Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    (C₀ : BlueCellulation Vertex Edge Face) {f : Face}
    (hthree : C₀.faceDegree f = 3) (i : Fin (C₀.faceDegree f)) :
    ABKPR.faceSucc C₀ f
      (ABKPR.faceSucc C₀ f (ABKPR.faceSucc C₀ f i)) = i := by
  apply Fin.ext
  have hi : i.val < 3 := by simpa [hthree] using i.isLt
  interval_cases hval : i.val <;>
    simp [ABKPR.faceSucc, ABKPR.cyclicSucc, hthree, hval]

private theorem faceSucc_ne_of_faceDegree_eq_three
    {Vertex Edge Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    (C₀ : BlueCellulation Vertex Edge Face) {f : Face}
    (hthree : C₀.faceDegree f = 3) (i : Fin (C₀.faceDegree f)) :
    ABKPR.faceSucc C₀ f i ≠ i := by
  intro heq
  have hi : i.val < 3 := by simpa [hthree] using i.isLt
  have heqv := congrArg Fin.val heq
  interval_cases hval : i.val <;>
    simp [ABKPR.faceSucc, ABKPR.cyclicSucc, hthree, hval] at heqv

private theorem boundaryEdge_line_cast
    {Vertex Edge Face Line : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    {C₀ : BlueCellulation Vertex Edge Face} (A : ABKPR.Data C₀)
    (edgeLine : Edge → Line) {f g : Face} (hfg : f = g)
    (i : Fin (C₀.faceDegree f)) :
    edgeLine (A.boundaryEdge g
      (Fin.cast (congrArg C₀.faceDegree hfg) i)) =
        edgeLine (A.boundaryEdge f i) := by
  subst g
  rfl

private theorem faceDart_cast_eq
    {Vertex Edge Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    (C₀ : BlueCellulation Vertex Edge Face) {f g : Face} (hfg : f = g)
    (i : Fin (C₀.faceDegree f)) :
    (⟨g, Fin.cast (congrArg C₀.faceDegree hfg) i⟩ : ABKPR.FaceDart C₀) =
      ⟨f, i⟩ := by
  subst g
  rfl

/-- At a double corner of two adjacent bad-quadrangle edges, crossing the
second edge exposes a boundary edge with the first edge's owner. -/
theorem exists_continuation_index
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (hfour : (C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 = 4) :
    ∃ i : Fin ((C ha hb hd hncol).faceDegree
        ((D hred ha hb hd hncol).across
          ⟨((D hred ha hb hd hncol).across
            ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1),
      ConcretePolarFlankBounds.edgeLine
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ⟨((D hred ha hb hd hncol).across
                ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 i) =
        ConcretePolarFlankBounds.edgeLine
          ((D hred ha hb hd hncol).boundaryEdge e.1
            ((D hred ha hb hd hncol).evilIndex e)) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let flankDart := DD.across ⟨bad.1, j⟩
  let k := bad.2
  let v : OrientedVertex (B (P := P)) :=
    if ABKPR.faceSucc CC bad.1 k = j then
      DD.boundaryVertex bad.1 j else DD.boundaryVertex bad.1 k
  have hvk : v ∈ CC.edgeVertices (DD.boundaryEdge bad.1 k) := by
    rw [DD.boundaryEdge_vertices bad.1 k]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hkj : ABKPR.faceSucc CC bad.1 k = j
    · right
      simpa only [v, if_pos hkj] using
        congrArg (DD.boundaryVertex bad.1) hkj.symm
    · left; simp [v, hkj]
  have hvj : v ∈ CC.edgeVertices (DD.boundaryEdge bad.1 j) := by
    rw [DD.boundaryEdge_vertices bad.1 j]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hkj : ABKPR.faceSucc CC bad.1 k = j
    · left; simp [v, hkj]
    · right
      have hjk : ABKPR.faceSucc CC bad.1 j = k := hadj.resolve_left hkj
      simpa only [v, if_neg hkj] using
        congrArg (DD.boundaryVertex bad.1) hjk.symm
  have hvflank : v ∈ CC.edgeVertices
      (DD.boundaryEdge flankDart.1 flankDart.2) := by
    dsimp only [flankDart]
    rw [← DD.across_sameEdge ⟨bad.1, j⟩]
    exact hvj
  obtain ⟨i, hine, hvi⟩ : ∃ i : Fin (CC.faceDegree flankDart.1),
      i ≠ flankDart.2 ∧
        v ∈ CC.edgeVertices (DD.boundaryEdge flankDart.1 i) := by
    rw [DD.boundaryEdge_vertices] at hvflank
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvflank
    rcases hvflank with hvstart | hvfinish
    · let i := ABKPR.faceSucc CC flankDart.1
          (ABKPR.faceSucc CC flankDart.1
            (ABKPR.faceSucc CC flankDart.1 flankDart.2))
      refine ⟨i, ?_, ?_⟩
      · intro hir
        apply ABKPR.faceSucc_ne_of_faceDegree_eq_four CC hfour i
        calc
          ABKPR.faceSucc CC flankDart.1 i = flankDart.2 :=
            ABKPR.faceSucc_four_of_faceDegree_eq_four CC hfour flankDart.2
          _ = i := hir.symm
      · rw [DD.boundaryEdge_vertices]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        rw [ABKPR.faceSucc_four_of_faceDegree_eq_four CC hfour flankDart.2]
        exact hvstart
    · refine ⟨ABKPR.faceSucc CC flankDart.1 flankDart.2,
        ABKPR.faceSucc_ne_of_faceDegree_eq_four CC hfour flankDart.2, ?_⟩
      rw [DD.boundaryEdge_vertices]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hvfinish
  let lCross := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge flankDart.1 flankDart.2)
  let lOther := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge flankDart.1 i)
  let lPath := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 k)
  have hjne : j ≠ k := by
    intro hjk
    subst j
    rcases hadj with hs | hs
    · exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC
        (DD.evilDart_across_bad e).1.1 k hs
    · exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC
        (DD.evilDart_across_bad e).1.1 k hs
  have hcrossne : lCross ≠ lPath := by
    intro h
    have hjcross : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad.1 j) = lCross :=
      congrArg ConcretePolarFlankBounds.edgeLine
        (DD.across_sameEdge ⟨bad.1, j⟩)
    have howner : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad.1 j) =
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad.1 k) :=
      hjcross.trans h
    exact hjne (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol bad.1 howner)
  have hotherne : lOther ≠ lCross := by
    intro h
    exact hine (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol flankDart.1 h)
  have hlCross : OnLine (B (P := P)) v.1 lCross :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge flankDart.1 flankDart.2) v hvflank
  have hlOther : OnLine (B (P := P)) v.1 lOther :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge flankDart.1 i) v hvi
  have hlPath : OnLine (B (P := P)) v.1 lPath :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1 k) v hvk
  have hvmemEvil : v ∈ CC.edgeVertices
      (DD.boundaryEdge e.1 (DD.evilIndex e)) := by
    change v ∈ CC.edgeVertices
      (DD.boundaryEdge (DD.evilDart e).1 (DD.evilDart e).2)
    rw [DD.across_sameEdge (DD.evilDart e)]
    simpa only [bad, k] using hvk
  have hmult : lineMultiplicity (OnLine (B (P := P))) v.1 = 2 := by
    rw [DD.boundaryEdge_vertices] at hvmemEvil
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvmemEvil
    rcases hvmemEvil with hv | hv
    · rw [hv]
      exact ConcreteStage3Local.badNeighbor_start_lineMultiplicity_eq_two
        hred ha hb hd hncol e.1 (DD.evilIndex e) (DD.evilDart_across_bad e)
    · rw [hv]
      exact ConcreteStage3Local.badNeighbor_finish_lineMultiplicity_eq_two
        hred ha hb hd hncol e.1 (DD.evilIndex e) (DD.evilDart_across_bad e)
  refine ⟨i, ?_⟩
  have hline : lOther = lPath := line_eq_of_multiplicity_two v.1
    lCross lPath lOther hmult hlCross hlPath hlOther hcrossne hotherne
  change lOther = _
  calc
    lOther = lPath := hline
    _ = ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge e.1 (DD.evilIndex e)) := by
      exact congrArg ConcretePolarFlankBounds.edgeLine
        (DD.across_sameEdge (DD.evilDart e)).symm

/-- At the same double corner, the adjacent bad-quadrangle owner continues
onto the evil triangle. -/
theorem exists_evil_continuation_index
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j) :
    ∃ u : Fin ((C ha hb hd hncol).faceDegree e.1),
      ConcretePolarFlankBounds.edgeLine
          ((D hred ha hb hd hncol).boundaryEdge e.1 u) =
        ConcretePolarFlankBounds.edgeLine
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ((D hred ha hb hd hncol).evilDart e)).1 j) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let k := bad.2
  let evilBack := DD.across ⟨bad.1, k⟩
  let v : OrientedVertex (B (P := P)) :=
    if ABKPR.faceSucc CC bad.1 k = j then
      DD.boundaryVertex bad.1 j else DD.boundaryVertex bad.1 k
  have hvk : v ∈ CC.edgeVertices (DD.boundaryEdge bad.1 k) := by
    rw [DD.boundaryEdge_vertices bad.1 k]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hkj : ABKPR.faceSucc CC bad.1 k = j
    · right
      simpa only [v, if_pos hkj] using
        congrArg (DD.boundaryVertex bad.1) hkj.symm
    · left; simp [v, hkj]
  have hvj : v ∈ CC.edgeVertices (DD.boundaryEdge bad.1 j) := by
    rw [DD.boundaryEdge_vertices bad.1 j]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hkj : ABKPR.faceSucc CC bad.1 k = j
    · left; simp [v, hkj]
    · right
      have hjk : ABKPR.faceSucc CC bad.1 j = k := hadj.resolve_left hkj
      simpa only [v, if_neg hkj] using
        congrArg (DD.boundaryVertex bad.1) hjk.symm
  have hvevilBack : v ∈ CC.edgeVertices
      (DD.boundaryEdge evilBack.1 evilBack.2) := by
    dsimp only [evilBack]
    rw [← DD.across_sameEdge ⟨bad.1, k⟩]
    exact hvk
  have hinv : evilBack = DD.evilDart e := by
    exact DD.across_involutive (DD.evilDart e)
  have hbackthree : CC.faceDegree evilBack.1 = 3 := by
    rw [hinv]
    exact e.2.1.1
  obtain ⟨u, hune, hvu⟩ : ∃ u : Fin (CC.faceDegree evilBack.1),
      u ≠ evilBack.2 ∧
        v ∈ CC.edgeVertices (DD.boundaryEdge evilBack.1 u) := by
    rw [DD.boundaryEdge_vertices] at hvevilBack
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvevilBack
    rcases hvevilBack with hvstart | hvfinish
    · let u := ABKPR.faceSucc CC evilBack.1
          (ABKPR.faceSucc CC evilBack.1 evilBack.2)
      refine ⟨u, ?_, ?_⟩
      · intro hur
        apply faceSucc_ne_of_faceDegree_eq_three CC hbackthree u
        calc
          ABKPR.faceSucc CC evilBack.1 u = evilBack.2 :=
            faceSucc_three_of_faceDegree_eq_three CC hbackthree evilBack.2
          _ = u := hur.symm
      · rw [DD.boundaryEdge_vertices]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        rw [faceSucc_three_of_faceDegree_eq_three CC hbackthree evilBack.2]
        exact hvstart
    · refine ⟨ABKPR.faceSucc CC evilBack.1 evilBack.2,
        faceSucc_ne_of_faceDegree_eq_three CC hbackthree evilBack.2, ?_⟩
      rw [DD.boundaryEdge_vertices]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl hvfinish
  let lCross := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge evilBack.1 evilBack.2)
  let lOther := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge evilBack.1 u)
  let lSide := ConcretePolarFlankBounds.edgeLine
    (DD.boundaryEdge bad.1 j)
  have hjne : j ≠ k := by
    intro hjk
    subst j
    rcases hadj with hs | hs
    · exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC
        (DD.evilDart_across_bad e).1.1 k hs
    · exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC
        (DD.evilDart_across_bad e).1.1 k hs
  have hcrossne : lCross ≠ lSide := by
    intro h
    have hkcross : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad.1 k) = lCross :=
      congrArg ConcretePolarFlankBounds.edgeLine
        (DD.across_sameEdge ⟨bad.1, k⟩)
    have howner : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad.1 k) =
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad.1 j) :=
      hkcross.trans h
    exact hjne ((ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol bad.1 howner).symm)
  have hotherne : lOther ≠ lCross := by
    intro h
    exact hune (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol evilBack.1 h)
  have hlCross : OnLine (B (P := P)) v.1 lCross :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge evilBack.1 evilBack.2) v hvevilBack
  have hlOther : OnLine (B (P := P)) v.1 lOther :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge evilBack.1 u) v hvu
  have hlSide : OnLine (B (P := P)) v.1 lSide :=
    concreteEdgeVertex_on_support (hspan ha hb hd hncol)
      (DD.boundaryEdge bad.1 j) v hvj
  have hmult : lineMultiplicity (OnLine (B (P := P))) v.1 = 2 := by
    have hvmemEvil : v ∈ CC.edgeVertices
        (DD.boundaryEdge e.1 (DD.evilIndex e)) := by
      change v ∈ CC.edgeVertices
        (DD.boundaryEdge (DD.evilDart e).1 (DD.evilDart e).2)
      rw [DD.across_sameEdge (DD.evilDart e)]
      simpa only [bad, k] using hvk
    rw [DD.boundaryEdge_vertices] at hvmemEvil
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvmemEvil
    rcases hvmemEvil with hv | hv
    · rw [hv]
      exact ConcreteStage3Local.badNeighbor_start_lineMultiplicity_eq_two
        hred ha hb hd hncol e.1 (DD.evilIndex e) (DD.evilDart_across_bad e)
    · rw [hv]
      exact ConcreteStage3Local.badNeighbor_finish_lineMultiplicity_eq_two
        hred ha hb hd hncol e.1 (DD.evilIndex e) (DD.evilDart_across_bad e)
  have hline : lOther = lSide := line_eq_of_multiplicity_two v.1
    lCross lSide lOther hmult hlCross hlSide hlOther hcrossne hotherne
  have hface : evilBack.1 = e.1 := congrArg Sigma.fst hinv
  let ue : Fin (CC.faceDegree e.1) :=
    Fin.cast (congrArg CC.faceDegree hface) u
  refine ⟨ue, ?_⟩
  exact (boundaryEdge_line_cast DD ConcretePolarFlankBounds.edgeLine
    hface u).trans hline

/-- If the owner-preserving continuation of a zero flank were itself
bordered by a bad quadrangle, the evil triangle would have two distinct bad
neighbors and the triangle-exception recognition would force failed Fano. -/
theorem isFailedFano_of_bad_zeroFlank_continuation
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (i : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1))
    (hiowner : ConcretePolarFlankBounds.edgeLine
        ((D hred ha hb hd hncol).boundaryEdge
          ((D hred ha hb hd hncol).across
            ⟨((D hred ha hb hd hncol).across
              ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 i) =
      ConcretePolarFlankBounds.edgeLine
        ((D hred ha hb hd hncol).boundaryEdge e.1
          ((D hred ha hb hd hncol).evilIndex e)))
    (hbad : (D hred ha hb hd hncol).IsBadTwoQuadrangle
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ⟨((D hred ha hb hd hncol).across
            ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1, i⟩).1) :
    IsFailedFano P := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let k := bad.2
  let flankDart := DD.across ⟨bad.1, j⟩
  let evilBack := DD.across ⟨bad.1, k⟩
  obtain ⟨u, huowner⟩ := exists_evil_continuation_index
    hred ha hb hd hncol e j hadj
  have hinv : evilBack = DD.evilDart e := DD.across_involutive (DD.evilDart e)
  have hface : evilBack.1 = e.1 := congrArg Sigma.fst hinv
  let ub : Fin (CC.faceDegree evilBack.1) :=
    Fin.cast (congrArg CC.faceDegree hface.symm) u
  have hubowner : ConcretePolarFlankBounds.edgeLine
      (DD.boundaryEdge evilBack.1 ub) =
      ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad.1 j) := by
    exact (boundaryEdge_line_cast DD ConcretePolarFlankBounds.edgeLine
      hface.symm u).trans huowner
  have hjne : j ≠ k := by
    intro hjk
    subst j
    rcases hadj with hs | hs
    · exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC
        (DD.evilDart_across_bad e).1.1 k hs
    · exact ABKPR.faceSucc_ne_of_faceDegree_eq_four CC
        (DD.evilDart_across_bad e).1.1 k hs
  have hkowner : ConcretePolarFlankBounds.edgeLine
      (DD.boundaryEdge flankDart.1 i) =
      ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad.1 k) := by
    exact hiowner.trans (congrArg ConcretePolarFlankBounds.edgeLine
      (DD.across_sameEdge (DD.evilDart e)))
  have hsquare : (DD.across ⟨evilBack.1, ub⟩).1 =
      (DD.across ⟨flankDart.1, i⟩).1 := by
    exact ConcretePolarABKPRData.concreteData_across_square_face
      hred ha hb hd hncol bad.1 k j hjne.symm ub i hubowner hkowner
  have hdart : (⟨evilBack.1, ub⟩ : ABKPR.FaceDart CC) = ⟨e.1, u⟩ :=
    faceDart_cast_eq CC hface.symm u
  have hbadU : DD.IsBadTwoQuadrangle (DD.across ⟨e.1, u⟩).1 := by
    rw [← hdart, hsquare]
    exact hbad
  have huBad : u ∈ DD.badNeighborIndices e.1 := by
    rw [ABKPR.Data.badNeighborIndices, Finset.mem_filter]
    exact ⟨Finset.mem_univ u, hbadU⟩
  have hkBad : DD.evilIndex e ∈ DD.badNeighborIndices e.1 := by
    rw [DD.badNeighborIndices_eq_singleton e]
    simp
  have huk : u ≠ DD.evilIndex e := by
    intro huk
    have howners : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad.1 j) =
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad.1 k) := by
      calc
        _ = ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge e.1 u) :=
          huowner.symm
        _ = ConcretePolarFlankBounds.edgeLine
            (DD.boundaryEdge e.1 (DD.evilIndex e)) := by rw [huk]
        _ = _ := congrArg ConcretePolarFlankBounds.edgeLine
          (DD.across_sameEdge (DD.evilDart e))
    exact hjne (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
      hred ha hb hd hncol bad.1 howners)
  exact TriangleExceptionCardinality.isFailedFano_of_triangleTwoBad
    hred ha hb hd hncol hAcard e.1 e.2.1.1 u (DD.evilIndex e)
      huk huBad hkBad

/-- A zero-diagonal cyclic flank is an actual helping pair whenever its
owner-preserving continuation does not border another bad quadrangle. -/
theorem exists_geometricFlank_of_zeroDiagonal_of_continuation_not_bad
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (hzero : (D hred ha hb hd hncol).IsZeroDiagonalQuadrangle
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1)
    (hnotbad : ∀ i, ConcretePolarFlankBounds.edgeLine
          ((D hred ha hb hd hncol).boundaryEdge
            ((D hred ha hb hd hncol).across
              ⟨((D hred ha hb hd hncol).across
                ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 i) =
        ConcretePolarFlankBounds.edgeLine
          ((D hred ha hb hd hncol).boundaryEdge e.1
            ((D hred ha hb hd hncol).evilIndex e)) →
      ¬ (D hred ha hb hd hncol).IsBadTwoQuadrangle
        ((D hred ha hb hd hncol).across
          ⟨((D hred ha hb hd hncol).across
            ⟨((D hred ha hb hd hncol).across
              ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1, i⟩).1) :
    ∃ h : (D hred ha hb hd hncol).HelpingPair,
      h.face = ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 ∧
      (D hred ha hb hd hncol).IsGeometricFlank
        ConcretePolarFlankBounds.edgeLine e h := by
  let DD := D hred ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let flankDart := DD.across ⟨bad.1, j⟩
  obtain ⟨i, hiowner⟩ := exists_continuation_index hred ha hb hd hncol
    e j hadj hzero.1
  have hihelp : i ∈ DD.helpingIndices flankDart.1 := by
    rw [ABKPR.Data.helpingIndices, Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hzero, hnotbad i hiowner⟩
  let h : DD.HelpingPair := ⟨flankDart.1, ⟨i, hihelp⟩⟩
  refine ⟨h, rfl, ?_⟩
  refine ⟨⟨j, hadj, rfl⟩, ?_⟩
  exact hiowner

/-- Outside failed Fano, every zero-diagonal cyclic flank supplies a
geometric helper, with its literal face retained in the conclusion. -/
theorem exists_geometricFlank_of_zeroDiagonal
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (e : (D hred ha hb hd hncol).EvilFace)
    (j : Fin ((C ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).1))
    (hadj : ABKPR.Data.CyclicAdjacentIndex
      ((D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)).2 j)
    (hzero : (D hred ha hb hd hncol).IsZeroDiagonalQuadrangle
      ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1) :
    ∃ h : (D hred ha hb hd hncol).HelpingPair,
      h.face = ((D hred ha hb hd hncol).across
        ⟨((D hred ha hb hd hncol).across
          ((D hred ha hb hd hncol).evilDart e)).1, j⟩).1 ∧
      (D hred ha hb hd hncol).IsGeometricFlank
        ConcretePolarFlankBounds.edgeLine e h := by
  apply exists_geometricFlank_of_zeroDiagonal_of_continuation_not_bad
    hred ha hb hd hncol e j hadj hzero
  intro i hiowner hbad
  exact hnotFF (isFailedFano_of_bad_zeroFlank_continuation
    hred ha hb hd hncol hAcard e j hadj i hiowner hbad)

/-- Once the remaining all-triangular local sector is recognized as failed
Fano, every evil triangle has an actual geometric helping flank. -/
theorem evil_has_geometric_flank_of_both_triangles_failedFano
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (both_triangles_failedFano : ∀ e : (D hred ha hb hd hncol).EvilFace,
      let bad := (D hred ha hb hd hncol).across
        ((D hred ha hb hd hncol).evilDart e)
      let jNext := ABKPR.faceSucc (C ha hb hd hncol) bad.1 bad.2
      let jPrev := ABKPR.faceSucc (C ha hb hd hncol) bad.1
        (ABKPR.faceSucc (C ha hb hd hncol) bad.1
          (ABKPR.faceSucc (C ha hb hd hncol) bad.1 bad.2))
      (C ha hb hd hncol).faceDegree
          ((D hred ha hb hd hncol).across ⟨bad.1, jNext⟩).1 = 3 →
        (C ha hb hd hncol).faceDegree
          ((D hred ha hb hd hncol).across ⟨bad.1, jPrev⟩).1 = 3 →
        IsFailedFano P) :
    ∀ e : (D hred ha hb hd hncol).EvilFace,
      ((D hred ha hb hd hncol).geometricFlanks
        ConcretePolarFlankBounds.edgeLine e).Nonempty := by
  intro e
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let bad := DD.across (DD.evilDart e)
  let jNext := ABKPR.faceSucc CC bad.1 bad.2
  let jPrev := ABKPR.faceSucc CC bad.1
    (ABKPR.faceSucc CC bad.1 (ABKPR.faceSucc CC bad.1 bad.2))
  have hbadfour : CC.faceDegree bad.1 = 4 := (DD.evilDart_across_bad e).1.1
  have hadjNext : ABKPR.Data.CyclicAdjacentIndex bad.2 jNext := Or.inl rfl
  have hadjPrev : ABKPR.Data.CyclicAdjacentIndex bad.2 jPrev := by
    right
    exact ABKPR.faceSucc_four_of_faceDegree_eq_four CC hbadfour bad.2
  have hclassNext := DD.flank_triangle_or_zeroDiagonal
    (ConcretePolarEndpointRestriction.concreteData_endpointRestriction
      hred ha hb hd hncol) e jNext hadjNext
  have hclassPrev := DD.flank_triangle_or_zeroDiagonal
    (ConcretePolarEndpointRestriction.concreteData_endpointRestriction
      hred ha hb hd hncol) e jPrev hadjPrev
  have makeHelper (j : Fin (CC.faceDegree bad.1))
      (hadj : ABKPR.Data.CyclicAdjacentIndex bad.2 j)
      (hzero : DD.IsZeroDiagonalQuadrangle (DD.across ⟨bad.1, j⟩).1) :
      (DD.geometricFlanks ConcretePolarFlankBounds.edgeLine e).Nonempty := by
    have hnotbad : ∀ i, ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge (DD.across ⟨bad.1, j⟩).1 i) =
        ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge e.1 (DD.evilIndex e)) →
      ¬ DD.IsBadTwoQuadrangle
        (DD.across ⟨(DD.across ⟨bad.1, j⟩).1, i⟩).1 := by
      intro i hiowner hbad
      exact hnotFF (isFailedFano_of_bad_zeroFlank_continuation
        hred ha hb hd hncol hAcard e j hadj i hiowner hbad)
    obtain ⟨h, _hface, hh⟩ :=
      exists_geometricFlank_of_zeroDiagonal_of_continuation_not_bad
        hred ha hb hd hncol e j hadj hzero hnotbad
    refine ⟨h, ?_⟩
    simpa [ABKPR.Data.geometricFlanks] using hh
  rcases hclassNext with htriNext | hzeroNext
  · rcases hclassPrev with htriPrev | hzeroPrev
    · exact (hnotFF (both_triangles_failedFano e htriNext htriPrev)).elim
    · exact makeHelper jPrev hadjPrev hzeroPrev
  · exact makeHelper jNext hadjNext hzeroNext

end Erdos735.ConcreteStage4FlankExistence
