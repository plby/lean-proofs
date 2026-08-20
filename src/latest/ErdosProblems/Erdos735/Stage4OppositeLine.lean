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

import ErdosProblems.Erdos735.HallDeficientComponent
import ErdosProblems.Erdos735.Stage4FlankCardinality

/-!
# The opposite-edge line in the Stage-4 alternating path

For a quadrangular face and a distinguished boundary dart, the edge opposite
that dart is obtained by applying the cyclic successor twice.  This file
defines the opposite darts used in the ABKPR evil--evil path argument and
isolates the exact local coherence statement needed to propagate the second
line `ℓ'` along an alternating path.
-/

namespace Erdos735

noncomputable section

namespace ABKPR

universe uV uEd uF

variable {Vertex : Type uV} {Edge : Type uEd} {Face : Type uF}
variable [Fintype Vertex] [Fintype Edge] [Fintype Face]
variable [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]

/-- Move two boundary steps.  On a quadrangle this is the opposite dart. -/
def secondSuccDart (C : BlueCellulation Vertex Edge Face)
    (d : FaceDart C) : FaceDart C :=
  ⟨d.1, faceSucc C d.1 (faceSucc C d.1 d.2)⟩

@[simp] theorem secondSuccDart_face
    (C : BlueCellulation Vertex Edge Face) (d : FaceDart C) :
    (secondSuccDart C d).1 = d.1 := rfl

/-- Four successor steps return to the starting dart of a quadrangle. -/
theorem faceSucc_four_of_faceDegree_eq_four
    (C : BlueCellulation Vertex Edge Face) {f : Face}
    (hfour : C.faceDegree f = 4) (i : Fin (C.faceDegree f)) :
    faceSucc C f
        (faceSucc C f (faceSucc C f (faceSucc C f i))) = i := by
  apply Fin.ext
  have hi : i.val < 4 := by simpa [hfour] using i.isLt
  interval_cases hval : i.val <;>
    simp [faceSucc, cyclicSucc, hfour, hval]

/-- Taking the opposite dart twice is the identity on quadrangles. -/
theorem secondSuccDart_involutive_of_faceDegree_eq_four
    (C : BlueCellulation Vertex Edge Face) (d : FaceDart C)
    (hfour : C.faceDegree d.1 = 4) :
    secondSuccDart C (secondSuccDart C d) = d := by
  rcases d with ⟨f, i⟩
  change (⟨f, faceSucc C f
    (faceSucc C f (faceSucc C f (faceSucc C f i)))⟩ : FaceDart C) =
      ⟨f, i⟩
  congr 1
  exact faceSucc_four_of_faceDegree_eq_four C hfour i

/-- The opposite boundary index of a quadrangle differs from the starting
index. -/
theorem secondSucc_ne_of_faceDegree_eq_four
    (C : BlueCellulation Vertex Edge Face) {f : Face}
    (hfour : C.faceDegree f = 4) (i : Fin (C.faceDegree f)) :
    faceSucc C f (faceSucc C f i) ≠ i := by
  intro heq
  have hi : i.val < 4 := by simpa [hfour] using i.isLt
  have heqv := congrArg Fin.val heq
  interval_cases hval : i.val <;>
    simp [faceSucc, cyclicSucc, hfour, hval] at heqv

/-- One successor step is nontrivial on a quadrangle. -/
theorem faceSucc_ne_of_faceDegree_eq_four
    (C : BlueCellulation Vertex Edge Face) {f : Face}
    (hfour : C.faceDegree f = 4) (i : Fin (C.faceDegree f)) :
    faceSucc C f i ≠ i := by
  intro heq
  have hi : i.val < 4 := by simpa [hfour] using i.isLt
  have heqv := congrArg Fin.val heq
  interval_cases hval : i.val <;>
    simp [faceSucc, cyclicSucc, hfour, hval] at heqv

/-- A cyclic neighbor of an edge in a quadrangle is not its opposite edge. -/
theorem cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
    (C : BlueCellulation Vertex Edge Face) {f : Face}
    (hfour : C.faceDegree f = 4) (i j : Fin (C.faceDegree f))
    (hadj : Data.CyclicAdjacentIndex (C := C) i j) :
    j ≠ faceSucc C f (faceSucc C f i) := by
  intro hj
  rcases hadj with hadj | hadj
  · have heq : i = faceSucc C f i :=
      (faceSucc_injective C f) (hadj.trans hj)
    exact faceSucc_ne_of_faceDegree_eq_four C hfour i heq.symm
  · have heq := congrArg (faceSucc C f) (hj ▸ hadj)
    rw [faceSucc_four_of_faceDegree_eq_four C hfour] at heq
    exact faceSucc_ne_of_faceDegree_eq_four C hfour i heq.symm

/-- Cyclically adjacent boundary indices of a quadrangle are distinct. -/
theorem ne_of_cyclicAdjacent_of_faceDegree_eq_four
    (C : BlueCellulation Vertex Edge Face) {f : Face}
    (hfour : C.faceDegree f = 4) (i j : Fin (C.faceDegree f))
    (hadj : Data.CyclicAdjacentIndex (C := C) i j) : i ≠ j := by
  intro hij
  subst j
  rcases hadj with h | h
  · exact faceSucc_ne_of_faceDegree_eq_four C hfour i h
  · exact faceSucc_ne_of_faceDegree_eq_four C hfour i h

namespace Data

variable {C : BlueCellulation Vertex Edge Face}
variable (A : ABKPR.Data C)

/-- The dart opposite the evil triangle's path-line dart in its adjacent bad
quadrangle. -/
def evilBadOppositeDart (e : A.EvilFace) : FaceDart C :=
  secondSuccDart C (A.across (A.evilDart e))

/-- The edge opposite the distinguished path-line edge of a helping
quadrangle. -/
def helpingOppositeDart (h : A.HelpingPair) : FaceDart C :=
  secondSuccDart C h.dart

lemma evilBadOppositeDart_face (e : A.EvilFace) :
    (A.evilBadOppositeDart e).1 = (A.across (A.evilDart e)).1 := rfl

lemma helpingOppositeDart_face (h : A.HelpingPair) :
    (A.helpingOppositeDart h).1 = h.face := rfl

lemma evilBadOppositeDart_ne_pathDart (e : A.EvilFace) :
    (A.evilBadOppositeDart e).2 ≠ (A.across (A.evilDart e)).2 := by
  exact secondSucc_ne_of_faceDegree_eq_four C
    (A.evilDart_across_bad e).1.1 (A.across (A.evilDart e)).2

lemma helpingOppositeDart_ne_pathDart (h : A.HelpingPair) :
    (A.helpingOppositeDart h).2 ≠ h.index := by
  exact secondSucc_ne_of_faceDegree_eq_four C h.isZeroDiagonal.1 h.index

/-- At the far end of an edge adjacent to a distinguished quadrangle edge,
the adjacent edge meets the opposite edge but not the distinguished edge.
This is the finite boundary fact used to identify the common far endpoint
on both sides of a flank edge. -/
theorem exists_farVertex_mem_adjacent_opposite_not_path
    {f : Face} (hfour : C.faceDegree f = 4)
    (i j : Fin (C.faceDegree f))
    (hadj : CyclicAdjacentIndex (C := C) i j) :
    ∃ v : Vertex,
      v ∈ C.edgeVertices (A.boundaryEdge f j) ∧
      v ∈ C.edgeVertices
        (A.boundaryEdge f (faceSucc C f (faceSucc C f i))) ∧
      v ∉ C.edgeVertices (A.boundaryEdge f i) := by
  by_cases hij : faceSucc C f i = j
  · let v := A.boundaryVertex f (faceSucc C f j)
    have hji : j ≠ i := by
      rw [← hij]
      exact faceSucc_ne_of_faceDegree_eq_four C hfour i
    have hsecond : faceSucc C f j ≠ i := by
      rw [← hij]
      exact secondSucc_ne_of_faceDegree_eq_four C hfour i
    have hnextne : faceSucc C f j ≠ faceSucc C f i := by
      exact fun h ↦ hji (ABKPR.faceSucc_injective C f h)
    refine ⟨v, ?_, ?_, ?_⟩
    · rw [A.boundaryEdge_vertices]
      simp [v]
    · rw [A.boundaryEdge_vertices, hij]
      simp [v]
    · rw [A.boundaryEdge_vertices]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hv
      rcases hv with hv | hv
      · exact hsecond (A.boundaryVertex_injective f hv)
      · exact hnextne (A.boundaryVertex_injective f hv)
  · have hji : faceSucc C f j = i := hadj.resolve_left hij
    have hji_ne : j ≠ i := by
      intro h
      subst j
      exact faceSucc_ne_of_faceDegree_eq_four C hfour i hji
    have hj_succ_ne : j ≠ faceSucc C f i := by
      intro h
      have hsquare : faceSucc C f (faceSucc C f i) = i := by
        rw [← h, hji]
      exact secondSucc_ne_of_faceDegree_eq_four C hfour i hsquare
    have hthird : faceSucc C f
        (faceSucc C f (faceSucc C f i)) = j := by
      apply ABKPR.faceSucc_injective C f
      rw [faceSucc_four_of_faceDegree_eq_four C hfour, hji]
    let v := A.boundaryVertex f j
    refine ⟨v, ?_, ?_, ?_⟩
    · rw [A.boundaryEdge_vertices]
      simp [v]
    · rw [A.boundaryEdge_vertices, hthird]
      simp [v]
    · rw [A.boundaryEdge_vertices]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hv
      rcases hv with hv | hv
      · exact hji_ne (A.boundaryVertex_injective f hv)
      · exact hj_succ_ne (A.boundaryVertex_injective f hv)

/-- At the near end of an edge adjacent to a distinguished quadrangle
edge, the adjacent edge meets the distinguished edge but not its opposite.
This is the companion to `exists_farVertex_mem_adjacent_opposite_not_path`.
-/
theorem exists_nearVertex_mem_adjacent_path_not_opposite
    {f : Face} (hfour : C.faceDegree f = 4)
    (i j : Fin (C.faceDegree f))
    (hadj : CyclicAdjacentIndex (C := C) i j) :
    ∃ v : Vertex,
      v ∈ C.edgeVertices (A.boundaryEdge f j) ∧
      v ∈ C.edgeVertices (A.boundaryEdge f i) ∧
      v ∉ C.edgeVertices
        (A.boundaryEdge f (faceSucc C f (faceSucc C f i))) := by
  by_cases hij : faceSucc C f i = j
  · let v := A.boundaryVertex f j
    have hj_ne : j ≠ faceSucc C f j :=
      (faceSucc_ne_of_faceDegree_eq_four C hfour j).symm
    have hj_second_ne : j ≠ faceSucc C f (faceSucc C f j) :=
      (secondSucc_ne_of_faceDegree_eq_four C hfour j).symm
    refine ⟨v, ?_, ?_, ?_⟩
    · rw [A.boundaryEdge_vertices]
      simp [v]
    · rw [A.boundaryEdge_vertices]
      simp [v, hij]
    · rw [A.boundaryEdge_vertices, hij]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hv
      rcases hv with hv | hv
      · exact hj_ne (A.boundaryVertex_injective f hv)
      · exact hj_second_ne (A.boundaryVertex_injective f hv)
  · have hji : faceSucc C f j = i := hadj.resolve_left hij
    have hji_ne : i ≠ j := by
      intro h
      subst j
      exact faceSucc_ne_of_faceDegree_eq_four C hfour i hji
    have hi_second_ne : i ≠ faceSucc C f (faceSucc C f i) :=
      (secondSucc_ne_of_faceDegree_eq_four C hfour i).symm
    have hthird : faceSucc C f
        (faceSucc C f (faceSucc C f i)) = j := by
      apply ABKPR.faceSucc_injective C f
      rw [faceSucc_four_of_faceDegree_eq_four C hfour, hji]
    let v := A.boundaryVertex f i
    refine ⟨v, ?_, ?_, ?_⟩
    · rw [A.boundaryEdge_vertices]
      simp [v, hji]
    · rw [A.boundaryEdge_vertices]
      simp [v]
    · rw [A.boundaryEdge_vertices, hthird]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hv
      rcases hv with hv | hv
      · exact hi_second_ne (A.boundaryVertex_injective f hv)
      · exact hji_ne (A.boundaryVertex_injective f hv)

/-- The endpoint of an adjacent edge which is not on the distinguished
edge is precisely an endpoint of the opposite edge. -/
theorem mem_opposite_of_mem_adjacent_not_mem_path
    {f : Face} (hfour : C.faceDegree f = 4)
    (i j : Fin (C.faceDegree f))
    (hadj : CyclicAdjacentIndex (C := C) i j)
    {v : Vertex}
    (hvj : v ∈ C.edgeVertices (A.boundaryEdge f j))
    (hvnot : v ∉ C.edgeVertices (A.boundaryEdge f i)) :
    v ∈ C.edgeVertices
      (A.boundaryEdge f (faceSucc C f (faceSucc C f i))) := by
  by_cases hij : faceSucc C f i = j
  · rw [A.boundaryEdge_vertices] at hvj hvnot ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvj hvnot ⊢
    rcases hvj with hvj | hvj
    · exfalso
      apply hvnot
      right
      rw [hij]
      exact hvj
    · left
      rw [congrArg (faceSucc C f) hij]
      exact hvj
  · have hji : faceSucc C f j = i := hadj.resolve_left hij
    have hthird : faceSucc C f
        (faceSucc C f (faceSucc C f i)) = j := by
      apply ABKPR.faceSucc_injective C f
      rw [faceSucc_four_of_faceDegree_eq_four C hfour, hji]
    rw [A.boundaryEdge_vertices] at hvj hvnot ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvj hvnot ⊢
    rcases hvj with hvj | hvj
    · right
      rw [hthird]
      exact hvj
    · exfalso
      apply hvnot
      left
      rw [← hji]
      exact hvj

/-- At either endpoint of an edge of a triangular face, there is a second
boundary edge of that face through the same vertex. -/
theorem exists_other_boundaryEdge_at_vertex_of_faceDegree_eq_three
    {f : Face} (hthree : C.faceDegree f = 3)
    (i : Fin (C.faceDegree f)) {v : Vertex}
    (hv : v ∈ C.edgeVertices (A.boundaryEdge f i)) :
    ∃ j : Fin (C.faceDegree f), j ≠ i ∧
      v ∈ C.edgeVertices (A.boundaryEdge f j) := by
  have hcycle : faceSucc C f
      (faceSucc C f (faceSucc C f i)) = i := by
    apply Fin.ext
    have hi : i.val < 3 := by simpa [hthree] using i.isLt
    interval_cases hval : i.val <;>
      simp [faceSucc, cyclicSucc, hthree, hval]
  have hsucc_ne : faceSucc C f i ≠ i := by
    intro h
    have hi : i.val < 3 := by simpa [hthree] using i.isLt
    have hv := congrArg Fin.val h
    interval_cases hval : i.val <;>
      simp [faceSucc, cyclicSucc, hthree, hval] at hv
  have hsecond_ne : faceSucc C f (faceSucc C f i) ≠ i := by
    intro h
    have hi : i.val < 3 := by simpa [hthree] using i.isLt
    have hv := congrArg Fin.val h
    interval_cases hval : i.val <;>
      simp [faceSucc, cyclicSucc, hthree, hval] at hv
  rw [A.boundaryEdge_vertices] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv
  · refine ⟨faceSucc C f (faceSucc C f i), hsecond_ne, ?_⟩
    rw [A.boundaryEdge_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (by rw [hcycle]; exact hv)
  · refine ⟨faceSucc C f i, hsucc_ne, ?_⟩
    rw [A.boundaryEdge_vertices]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact Or.inl hv

/-- Any two distinct boundary edges of a triangular face meet in a
boundary vertex. -/
theorem exists_common_vertex_of_distinct_edges_of_faceDegree_eq_three
    {f : Face} (hthree : C.faceDegree f = 3)
    (i j : Fin (C.faceDegree f)) (hij : i ≠ j) :
    ∃ v : Vertex,
      v ∈ C.edgeVertices (A.boundaryEdge f i) ∧
      v ∈ C.edgeVertices (A.boundaryEdge f j) := by
  have hadj : faceSucc C f i = j ∨ faceSucc C f j = i := by
    simp only [Fin.ext_iff, faceSucc, cyclicSucc]
    have hi : i.val < 3 := by simpa [hthree] using i.isLt
    have hj : j.val < 3 := by simpa [hthree] using j.isLt
    have hijv : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    interval_cases hival : i.val <;> interval_cases hjval : j.val <;>
      simp [hthree, hival, hjval] at hijv ⊢
  rcases hadj with hadj | hadj
  · refine ⟨A.boundaryVertex f j, ?_, ?_⟩
    · rw [A.boundaryEdge_vertices]
      simp [hadj]
    · rw [A.boundaryEdge_vertices]
      simp
  · refine ⟨A.boundaryVertex f i, ?_, ?_⟩
    · rw [A.boundaryEdge_vertices]
      simp
    · rw [A.boundaryEdge_vertices]
      simp [hadj]

section Lines

universe uL

variable {Line : Type uL} [Fintype Line] [DecidableEq Line]
variable (L : A.FlankSystem Line)

/-- The owner of the edge opposite an evil's path edge. -/
def evilOppositeLine (e : A.EvilFace) : Line :=
  L.edgeLine
    (A.boundaryEdge (A.evilBadOppositeDart e).1
      (A.evilBadOppositeDart e).2)

/-- The owner of the edge opposite a helper's distinguished path edge. -/
def helperOppositeLine (h : A.HelpingPair) : Line :=
  L.edgeLine
    (A.boundaryEdge (A.helpingOppositeDart h).1
      (A.helpingOppositeDart h).2)

/-- The local strip lemma needed by the ABKPR path argument: whenever an
evil bad quadrangle and a zero-diagonal helper are consecutive along the
path line, their opposite edges have the same owner.  For the literal polar
cellulation this is a theorem to be proved from the red-chord geometry; it
is kept separate from the purely finite Hall extraction. -/
structure OppositeLineCoherence : Prop where
  eq_of_adj : ∀ e h, L.Adj e h →
    evilOppositeLine A L e = helperOppositeLine A L h

namespace OppositeLineCoherence

/-- The opposite-line owner is constant over one
evil--helper--evil step. -/
theorem evilOppositeLine_eq_of_evilLinked
    (K : OppositeLineCoherence A L)
    {e₀ e₁ : A.EvilFace} (hlink : EvilLinked L e₀ e₁) :
    evilOppositeLine A L e₀ = evilOppositeLine A L e₁ := by
  obtain ⟨h, h₀, h₁⟩ := hlink
  exact (K.eq_of_adj e₀ h h₀).trans (K.eq_of_adj e₁ h h₁).symm

/-- Hence the owner `ℓ'` propagates along every finite alternating
chain. -/
theorem evilOppositeLine_eq_of_reflTransGen_evilLinked
    (K : OppositeLineCoherence A L)
    {e₀ e₁ : A.EvilFace}
    (hpath : Relation.ReflTransGen (EvilLinked L) e₀ e₁) :
    evilOppositeLine A L e₀ = evilOppositeLine A L e₁ := by
  induction hpath with
  | refl => rfl
  | tail hpath hstep ih =>
      exact ih.trans (evilOppositeLine_eq_of_evilLinked A L K hstep)

end OppositeLineCoherence

/-- The generic deficient component's linked-evil relation is the concrete
flank system's alternating-step relation. -/
theorem linkedEvil_iff_evilLinked (e e' : A.EvilFace) :
    (L.toHelpingGraph).LinkedEvil e e' ↔ EvilLinked L e e' := by
  rfl

/-- In the canonical deficient path component, both evil endpoints have the
same path-line owner. -/
theorem deficientPath_endpoints_badEdgeLine_eq
    (hHall : ¬ L.toHelpingGraph.NoEvilEvilPath) (k : Fin 2) :
    L.edgeLine
        (A.boundaryEdge
          ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0).1
          (A.evilIndex
            ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0))) =
      L.edgeLine
        (A.boundaryEdge
          ((L.toHelpingGraph.deficientPathComponent hHall).endpoint k).1
          (A.evilIndex
            ((L.toHelpingGraph.deficientPathComponent hHall).endpoint k))) := by
  let H := L.toHelpingGraph.deficientPathComponent hHall
  have hpath := H.evils_reachable_from_first (H.endpoint k) (H.endpoint_mem k)
  have hmono : ∀ {x y : A.EvilFace},
      Relation.ReflTransGen L.toHelpingGraph.LinkedEvil x y →
        Relation.ReflTransGen (EvilLinked L) x y := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h hstep ih =>
        exact Relation.ReflTransGen.tail ih
          ((linkedEvil_iff_evilLinked A L _ _).mp hstep)
  have hpath' : Relation.ReflTransGen (EvilLinked L)
      (H.endpoint 0) (H.endpoint k) := hmono hpath
  exact badEdgeLine_eq_of_reflTransGen_evilLinked L hpath'

/-- Under the local opposite-edge strip lemma, both endpoints of the
canonical deficient path also determine the same opposite-line owner. -/
theorem OppositeLineCoherence.deficientPath_endpoints_oppositeLine_eq
    (K : OppositeLineCoherence A L)
    (hHall : ¬ L.toHelpingGraph.NoEvilEvilPath) (k : Fin 2) :
    evilOppositeLine A L
        ((L.toHelpingGraph.deficientPathComponent hHall).endpoint 0) =
      evilOppositeLine A L
        ((L.toHelpingGraph.deficientPathComponent hHall).endpoint k) := by
  let H := L.toHelpingGraph.deficientPathComponent hHall
  have hpath := H.evils_reachable_from_first (H.endpoint k) (H.endpoint_mem k)
  have hmono : ∀ {x y : A.EvilFace},
      Relation.ReflTransGen L.toHelpingGraph.LinkedEvil x y →
        Relation.ReflTransGen (EvilLinked L) x y := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h hstep ih =>
        exact Relation.ReflTransGen.tail ih
          ((linkedEvil_iff_evilLinked A L _ _).mp hstep)
  have hpath' : Relation.ReflTransGen (EvilLinked L)
      (H.endpoint 0) (H.endpoint k) := hmono hpath
  exact evilOppositeLine_eq_of_reflTransGen_evilLinked A L K hpath'

end Lines
end Data
end ABKPR

end
end Erdos735
