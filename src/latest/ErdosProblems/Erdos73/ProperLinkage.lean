/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.RootedTrees

/-!
# Proper linkages at rooted-tree separators

This completes the bramble form of the Leaf--Seymour rooted-tree construction,
using the sufficient order bound `2 * |T|`. The modified graph removes unused
boundary vertices and boundary edges. Two genuine corner separations and
haven antitonicity prove Menger's required lower bound. The output paths
belong to the original graph, avoid internal boundary vertices, and cannot
consist of one edge. Terminal sets may overlap.
-/

namespace Erdos73
open Erdos73Infrastructure.SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The graph used to find boundary-proper paths: unused boundary vertices
and vertices outside the right side are isolated, and boundary edges vanish. -/
def properLinkageGraph (G : SimpleGraph V) (B S X Y : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a ∈ B \ (S \ (X ∪ Y)) ∧ b ∈ B \ (S \ (X ∪ Y)) ∧
    ¬ (a ∈ S ∧ b ∈ S)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.2.1, h.2.1, fun hab ↦ h.2.2.2 hab.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1.ne rfl⟩

omit [Fintype V] in
lemma properLinkageGraph_le (B S X Y : Finset V) : properLinkageGraph G B S X Y ≤ G :=
  fun _ _ h ↦ h.1

omit [Fintype V] in
lemma properLinkageGraph_swap (B S X Y : Finset V) :
    properLinkageGraph G B S X Y = properLinkageGraph G B S Y X := by
  simp only [properLinkageGraph, Finset.union_comm X Y]

lemma properLinkageGraph_corner {A B X Y E F J : Finset V}
    (hAB : IsVertexSeparation G A B)
    (hEF : IsVertexSeparation (properLinkageGraph G B (A ∩ B) X Y) E F)
    (hXE : X ⊆ E) (hJ : E ∩ F = J) :
    let Z := (A ∩ B) \ (X ∪ Y)
    let L := (E ∩ B) ∪ Z
    let R := (F ∩ B) ∪ Z
    IsVertexSeparation G (A ∪ L) R ∧
      (A ∪ L) ∩ R ⊆ J ∪ ((A ∩ B) \ X) ∧
      R ⊆ B ∧ L ∪ R = B := by
  dsimp only
  let S := A ∩ B
  let Z := S \ (X ∪ Y)
  let L := (E ∩ B) ∪ Z
  let R := (F ∩ B) ∪ Z
  have hZS : Z ⊆ S := Finset.sdiff_subset
  have hZA : Z ⊆ A := hZS.trans Finset.inter_subset_left
  have hZB : Z ⊆ B := hZS.trans Finset.inter_subset_right
  have hRB : R ⊆ B := Finset.union_subset Finset.inter_subset_right hZB
  have hcover : L ∪ R = B := by
    ext v
    have hv := hEF.mem_left_or_right v
    have hZ := hZB (x := v)
    simp only [L, R, Finset.mem_union, Finset.mem_inter]
    tauto
  refine ⟨?_, ?_, hRB, hcover⟩
  · constructor
    · change (A ∪ L) ∪ R = Finset.univ
      rw [Finset.union_assoc, hcover, hAB.1]
    · intro a b ha haR hb hbAL hab
      have hbA : b ∉ A := fun h ↦ hbAL (Finset.mem_union.mpr (Or.inl h))
      have hbZ : b ∉ Z := fun h ↦ hbA (hZA h)
      have hbF : b ∈ F := (Finset.mem_inter.mp
        ((Finset.mem_union.mp hb).resolve_right hbZ)).1
      have hbB := hRB hb
      have hbE : b ∉ E := fun h ↦ hbAL (Finset.mem_union.mpr (Or.inr
        (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨h, hbB⟩)))))
      have haZ : a ∉ Z := fun h ↦ haR (Finset.mem_union.mpr (Or.inr h))
      by_cases haB : a ∈ B
      · have haF : a ∉ F := fun h ↦ haR
          (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨h, haB⟩)))
        have haE := (hEF.mem_left_or_right a).resolve_right haF
        exact hEF.2 haE haF hbF hbE ⟨hab, Finset.mem_sdiff.mpr ⟨haB, haZ⟩,
          Finset.mem_sdiff.mpr ⟨hbB, hbZ⟩, fun h ↦ hbA (Finset.mem_inter.mp h.2).1⟩
      · have haA := (hAB.mem_left_or_right a).resolve_right haB
        exact hAB.2 haA haB hbB hbA hab
  · intro v hv
    by_cases hvJ : v ∈ J
    · exact Finset.mem_union.mpr (Or.inl hvJ)
    · obtain ⟨hvAL, hvR⟩ := Finset.mem_inter.mp hv
      have hvB := hRB hvR
      have hvS : v ∈ S := by
        rcases Finset.mem_union.mp hvAL with hvA | hvL
        · exact Finset.mem_inter.mpr ⟨hvA, hvB⟩
        · rcases Finset.mem_union.mp hvL with hvEB | hvZ
          · rcases Finset.mem_union.mp hvR with hvFB | hvZ
            · exact (hvJ (hJ ▸ Finset.mem_inter.mpr
                ⟨(Finset.mem_inter.mp hvEB).1, (Finset.mem_inter.mp hvFB).1⟩)).elim
            · exact hZS hvZ
          · exact hZS hvZ
      have hvX : v ∉ X := by
        intro hvX
        have hvZ : v ∉ Z := fun hvZ ↦ (Finset.mem_sdiff.mp hvZ).2
          (Finset.mem_union.mpr (Or.inl hvX))
        have hvF := (Finset.mem_inter.mp ((Finset.mem_union.mp hvR).resolve_right hvZ)).1
        exact hvJ (hJ ▸ Finset.mem_inter.mpr ⟨hXE hvX, hvF⟩)
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hvS, hvX⟩))

theorem BrambleHaven.hasDisjointPaths_properLinkageGraph
    {β : Finset (Finset V)} {q : ℕ} (h : BrambleHaven G β q) {A B X Y : Finset V}
    (hAB : IsVertexSeparation G A B) (hpoint : h.PointsTo A B)
    (hmin : h.ForwardMinimal A B) (hX : X ⊆ A ∩ B) (hY : Y ⊆ A ∩ B)
    (hXY : X.card = Y.card) (hq : 2 * (A ∩ B).card ≤ q) :
    HasDisjointSTPaths (properLinkageGraph G B (A ∩ B) X Y) X Y X.card := by
  rcases Menger.finite_vertex_menger_sharp (properLinkageGraph G B (A ∩ B) X Y)
    X Y X.card with hpaths | ⟨J, hJcard, hJ⟩
  · exact hpaths
  obtain ⟨E, F, hEF, hEFJ, hXE, hYF⟩ := exists_vertexSeparation_of_STSeparator hJ
  let S := A ∩ B
  let Z := S \ (X ∪ Y)
  let L := (E ∩ B) ∪ Z
  let R := (F ∩ B) ∪ Z
  have hc₁ := properLinkageGraph_corner hAB hEF hXE hEFJ
  change IsVertexSeparation G (A ∪ L) R ∧ (A ∪ L) ∩ R ⊆ J ∪ (S \ X) ∧
    R ⊆ B ∧ L ∪ R = B at hc₁
  obtain ⟨hsep₁, hbound₁, hRB, hcover⟩ := hc₁
  have hEF' : IsVertexSeparation (properLinkageGraph G B S Y X) F E := by
    rw [← properLinkageGraph_swap B S X Y]
    exact hEF.flip
  have hc₂ := properLinkageGraph_corner hAB hEF' hYF
    (by rw [Finset.inter_comm, hEFJ])
  simp only [Finset.union_comm Y X] at hc₂
  change IsVertexSeparation G (A ∪ R) L ∧ (A ∪ R) ∩ L ⊆ J ∪ (S \ Y) ∧
    L ⊆ B ∧ R ∪ L = B at hc₂
  obtain ⟨hsep₂, hbound₂, hLB, _⟩ := hc₂
  have hcard₁ : ((A ∪ L) ∩ R).card < S.card := by
    have h₁ := (Finset.card_le_card hbound₁).trans (Finset.card_union_le _ _)
    rw [Finset.card_sdiff_of_subset hX] at h₁
    have hXcard := Finset.card_le_card hX
    change ((A ∪ L) ∩ R).card < (A ∩ B).card
    omega
  have hcard₂ : ((A ∪ R) ∩ L).card < S.card := by
    have h₂ := (Finset.card_le_card hbound₂).trans (Finset.card_union_le _ _)
    rw [Finset.card_sdiff_of_subset hY] at h₂
    have hYcard := Finset.card_le_card hY
    change ((A ∪ R) ∩ L).card < (A ∩ B).card
    omega
  obtain ⟨hsmall, hreg⟩ := hpoint
  have hsmall₁ : ((A ∪ L) ∩ R).card < q := hcard₁.trans hsmall
  have hsmall₂ : ((A ∪ R) ∩ L).card < q := hcard₂.trans hsmall
  have hleft₁ : h.region ⟨(A ∪ L) ∩ R, hsmall₁⟩ ⊆ (A ∪ L) \ R := by
    rcases connected_finset_subset_side_of_disjoint_separator hsep₁
      (h.connected ⟨(A ∪ L) ∩ R, hsmall₁⟩)
      (h.avoids ⟨(A ∪ L) ∩ R, hsmall₁⟩) with hleft | hright
    · exact hleft
    · have hle := hmin (A ∪ L) R hsep₁ Finset.subset_union_left hRB
        ⟨hsmall₁, hright.trans Finset.sdiff_subset⟩
      exact (hcard₁.not_ge hle).elim
  have hleft₂ : h.region ⟨(A ∪ R) ∩ L, hsmall₂⟩ ⊆ (A ∪ R) \ L := by
    rcases connected_finset_subset_side_of_disjoint_separator hsep₂
      (h.connected ⟨(A ∪ R) ∩ L, hsmall₂⟩)
      (h.avoids ⟨(A ∪ R) ∩ L, hsmall₂⟩) with hleft | hright
    · exact hleft
    · have hle := hmin (A ∪ R) L hsep₂ Finset.subset_union_left hLB
        ⟨hsmall₂, hright.trans Finset.sdiff_subset⟩
      exact (hcard₂.not_ge hle).elim
  let U := S ∪ J
  have hUcard : U.card < q := by
    have hU := Finset.card_union_le S J
    have hXcard : X.card ≤ S.card := Finset.card_le_card hX
    change 2 * S.card ≤ q at hq
    change (S ∪ J).card < q
    omega
  have hSU : S ⊆ U := Finset.subset_union_left
  have h₁U : (A ∪ L) ∩ R ⊆ U := hbound₁.trans (by
    intro v hv
    rcases Finset.mem_union.mp hv with hvJ | hvS
    · exact Finset.mem_union.mpr (Or.inr hvJ)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hvS).1))
  have h₂U : (A ∪ R) ∩ L ⊆ U := hbound₂.trans (by
    intro v hv
    rcases Finset.mem_union.mp hv with hvJ | hvS
    · exact Finset.mem_union.mpr (Or.inr hvJ)
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hvS).1))
  obtain ⟨u⟩ := (h.connected ⟨U, hUcard⟩).nonempty
  have huS := (h.pointsTo_exclusive hreg)
    (h.antitone ⟨S, hsmall⟩ ⟨U, hUcard⟩ hSU u.2)
  have hu₁ := Finset.mem_sdiff.mp (hleft₁
    (h.antitone ⟨(A ∪ L) ∩ R, hsmall₁⟩ ⟨U, hUcard⟩ h₁U u.2))
  have hu₂ := Finset.mem_sdiff.mp (hleft₂
    (h.antitone ⟨(A ∪ R) ∩ L, hsmall₂⟩ ⟨U, hUcard⟩ h₂U u.2))
  have huA := (Finset.mem_sdiff.mp huS).2
  exact (hu₂.2 ((Finset.mem_union.mp hu₁.1).resolve_left huA)).elim

omit [Fintype V] in
lemma properLinkageGraph_walk_support {B S X Y : Finset V} {a b : V}
    (p : (properLinkageGraph G B S X Y).Walk a b)
    (ha : a ∈ B \ (S \ (X ∪ Y))) : ∀ v ∈ p.support, v ∈ B \ (S \ (X ∪ Y)) := by
  induction p with
  | nil => simpa using ha
  | cons hab p ih =>
    simpa only [SimpleGraph.Walk.support_cons, List.mem_cons, forall_eq_or_imp] using
      And.intro ha (ih hab.2.2.1)

omit [Fintype V] in
lemma properLinkageGraph_walk_length_ne_one {B S X Y : Finset V} {a b : V}
    (p : (properLinkageGraph G B S X Y).Walk a b) (ha : a ∈ S) (hb : b ∈ S) :
    p.length ≠ 1 := by
  cases p with
  | nil => simp
  | cons hab p =>
    cases p with
    | nil => exact fun _ ↦ hab.2.2.2 ⟨ha, hb⟩
    | cons hbc p => simp

omit [Fintype V] in
lemma properLinkageGraph_path_properties {B S X Y : Finset V}
    (hSB : S ⊆ B) (hX : X ⊆ S) (hY : Y ⊆ S)
    (P : GraphPath (properLinkageGraph G B S X Y)) (hP : P.EndpointClean X Y) :
    P.vertexSet ⊆ B ∧ P.InternallyDisjointFromSet S ∧ P.walk.length ≠ 1 := by
  have hsource : P.source ∈ B \ (S \ (X ∪ Y)) := by
    refine Finset.mem_sdiff.mpr ⟨hSB (hX hP.source_mem), ?_⟩
    exact fun h ↦ (Finset.mem_sdiff.mp h).2 (Finset.mem_union.mpr (Or.inl hP.source_mem))
  have hsupport := properLinkageGraph_walk_support P.walk hsource
  have hsub : P.vertexSet ⊆ B \ (S \ (X ∪ Y)) := by
    intro v hv
    exact hsupport v (List.mem_toFinset.mp hv)
  refine ⟨hsub.trans Finset.sdiff_subset, ?_,
    properLinkageGraph_walk_length_ne_one P.walk (hX hP.source_mem) (hY hP.target_mem)⟩
  intro v hv hvS
  have hvXY : v ∈ X ∪ Y := by
    by_contra hvXY
    exact (Finset.mem_sdiff.mp (hsub hv)).2 (Finset.mem_sdiff.mpr ⟨hvS, hvXY⟩)
  rcases Finset.mem_union.mp hvXY with hvX | hvY
  · exact Or.inl (hP.left_eq_source hv hvX)
  · exact Or.inr (hP.right_eq_target hv hvY)

theorem BrambleHaven.exists_boundaryProperLinkage
    {β : Finset (Finset V)} {q : ℕ} (h : BrambleHaven G β q) {A B X Y : Finset V}
    (hAB : IsVertexSeparation G A B) (hpoint : h.PointsTo A B)
    (hmin : h.ForwardMinimal A B) (hX : X ⊆ A ∩ B) (hY : Y ⊆ A ∩ B)
    (hXY : X.card = Y.card) (hq : 2 * (A ∩ B).card ≤ q) :
    ∃ P : EndpointCleanPathPacking G X Y, P.card = X.card ∧
      ∀ i, (P.path i).vertexSet ⊆ B ∧
        (P.path i).InternallyDisjointFromSet (A ∩ B) ∧ (P.path i).walk.length ≠ 1 := by
  obtain ⟨P₀, hP₀⟩ := HasAtLeastDisjointPaths.exists_exact
    (h.hasDisjointPaths_properLinkageGraph hAB hpoint hmin hX hY hXY hq)
  let P := P₀.toEndpointClean
  let Q : EndpointCleanPathPacking G X Y := {
    Index := P.Index
    path := fun i ↦ (P.path i).mapLe (properLinkageGraph_le B (A ∩ B) X Y)
    endpoint_clean := by
      intro i
      refine ⟨(P.endpoint_clean i).source_mem, (P.endpoint_clean i).target_mem, ?_, ?_⟩
      · intro v hv hvX
        exact (P.endpoint_clean i).left_eq_source
          (by simpa only [GraphPath.mapLe_vertexSet] using hv) hvX
      · intro v hv hvY
        exact (P.endpoint_clean i).right_eq_target
          (by simpa only [GraphPath.mapLe_vertexSet] using hv) hvY
    node_disjoint := by
      intro i j hij
      simpa only [GraphPath.NodeDisjoint, GraphPath.mapLe_vertexSet] using P.node_disjoint hij
  }
  refine ⟨Q, hP₀, ?_⟩
  intro i
  have hprop := properLinkageGraph_path_properties Finset.inter_subset_right hX hY
    (P.path i) (P.endpoint_clean i)
  change ((P.path i).mapLe _).vertexSet ⊆ B ∧
    ((P.path i).mapLe _).InternallyDisjointFromSet (A ∩ B) ∧
    ((P.path i).mapLe _).walk.length ≠ 1
  rw [GraphPath.mapLe_vertexSet]
  refine ⟨hprop.1, ?_, ?_⟩
  · intro v hv hvAB
    exact hprop.2.1 (by simpa only [GraphPath.mapLe_vertexSet] using hv) hvAB
  · change ((P.path i).walk.mapLe (properLinkageGraph_le B (A ∩ B) X Y)).length ≠ 1
    simpa using hprop.2.2

/-- Proper linkedness in the sense of Leaf--Seymour: all terminal pairs
have a full disjoint linkage, avoiding the other boundary vertices and
excluding one-edge paths. Shared terminals are allowed. -/
def BoundaryProperLinked (G : SimpleGraph V) (B S : Finset V) : Prop :=
  ∀ X Y : Finset V, X ⊆ S → Y ⊆ S → X.card = Y.card →
    ∃ P : EndpointCleanPathPacking G X Y, P.card = X.card ∧
      ∀ i, (P.path i).vertexSet ⊆ B ∧
        (P.path i).InternallyDisjointFromSet S ∧ (P.path i).walk.length ≠ 1

/-- The bramble form of the rooted-tree/proper-linkage theorem, with the
convenient sufficient bound twice the number of tree vertices. -/
theorem exists_treeSeparation_properLinked {I : Type*} [Fintype I]
    (T : SimpleGraph I) (hT : T.IsTree) {β : Finset (Finset V)}
    (hβ : IsFiniteBramble G β) {q : ℕ} (horder : BrambleOrderAtLeast q β)
    (hq : 2 * Fintype.card I ≤ q) :
    ∃ A B : Finset V, IsVertexSeparation G A B ∧
      (A ∩ B).card = Fintype.card I ∧ Nonempty (LeftRootedModel T G A B) ∧
      (G.induce ((B \ A : Finset V) : Set V)).Connected ∧
      (∀ v ∈ A ∩ B, ∃ u ∈ B \ A, G.Adj v u) ∧ BoundaryProperLinked G B (A ∩ B) := by
  have : Nonempty I := hT.connected.nonempty
  have hpos := Fintype.card_pos (α := I)
  obtain ⟨h⟩ := exists_brambleHaven hβ horder
  obtain ⟨A, B, hAB, hcard, hpoint, hsat, hmodel⟩ := h.exists_saturated_treeModel T hT (by omega)
  have hprops := h.saturated_right_properties hAB hpoint hsat
  refine ⟨A, B, hAB, hcard, hmodel, hprops.1, hprops.2, ?_⟩
  intro X Y hX hY hXY
  exact h.exists_boundaryProperLinkage hAB hpoint (h.forwardSaturated_minimal hsat)
    hX hY hXY (by rw [hcard]; exact hq)

end
end Erdos73

#print axioms Erdos73.BrambleHaven.exists_boundaryProperLinkage
#print axioms Erdos73.exists_treeSeparation_properLinked
