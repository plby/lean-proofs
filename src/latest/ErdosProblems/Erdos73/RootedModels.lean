/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.Bramble

/-!
# Nested separators and rooted minor models

The finite-Menger argument moves an ordinary rooted minor model through a
nested interval of separations. This is the transport step in the proof of
Leaf--Seymour, Tree-width and planar minors, Theorem 4.3. The path containment
and all four branch-set intersection cases are checked explicitly.
-/

namespace Erdos73
open Erdos73Infrastructure.SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

lemma IsVertexSeparation.mem_left_or_right {A B : Finset V}
    (h : IsVertexSeparation G A B) (v : V) : v ∈ A ∨ v ∈ B := by
  have hv : v ∈ A ∪ B := by rw [h.1]; exact Finset.mem_univ v
  exact Finset.mem_union.mp hv

lemma IsVertexSeparation.adj_mem_left {A B : Finset V}
    (h : IsVertexSeparation G A B) {a b : V}
    (ha : a ∈ A) (haB : a ∉ B) (hab : G.Adj a b) : b ∈ A := by
  by_contra hbA
  exact h.2 ha haB ((h.mem_left_or_right b).resolve_left hbA) hbA hab

lemma IsVertexSeparation.join {A B C D : Finset V}
    (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D) :
    IsVertexSeparation G (A ∪ C) (B ∩ D) := by
  constructor
  · ext v
    have h₁ := hAB.mem_left_or_right v
    have h₂ := hCD.mem_left_or_right v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_univ, iff_true]
    tauto
  · intro a b ha haBD hb hbAC hab
    have hbA : b ∉ A := fun h ↦ hbAC (Finset.mem_union.mpr (Or.inl h))
    have hbC : b ∉ C := fun h ↦ hbAC (Finset.mem_union.mpr (Or.inr h))
    by_cases haB : a ∈ B
    · have haD : a ∉ D := fun h ↦ haBD (Finset.mem_inter.mpr ⟨haB, h⟩)
      exact hbC (hCD.adj_mem_left ((hCD.mem_left_or_right a).resolve_right haD)
        haD hab)
    · exact hbA (hAB.adj_mem_left ((hAB.mem_left_or_right a).resolve_right haB)
        haB hab)

lemma IsVertexSeparation.meet {A B C D : Finset V}
    (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D) :
    IsVertexSeparation G (A ∩ C) (B ∪ D) :=
  (hAB.flip.join hCD.flip).flip

lemma nested_separation_normalize {A B C D E F : Finset V}
    (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D)
    (hEF : IsVertexSeparation G E F) (hAC : A ⊆ C) (hDB : D ⊆ B)
    (hSE : A ∩ B ⊆ E) (hTF : C ∩ D ⊆ F) :
    ∃ E' F' : Finset V, IsVertexSeparation G E' F' ∧
      A ⊆ E' ∧ E' ⊆ C ∧ D ⊆ F' ∧ F' ⊆ B ∧
      E' ∩ F' ⊆ E ∩ F := by
  refine ⟨A ∪ (E ∩ C), B ∩ (F ∪ D), hAB.join (hEF.meet hCD),
    Finset.subset_union_left, ?_, ?_, Finset.inter_subset_left, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hA | hEC
    · exact hAC hA
    · exact (Finset.mem_inter.mp hEC).2
  · intro v hv
    exact Finset.mem_inter.mpr ⟨hDB hv, Finset.mem_union.mpr (Or.inr hv)⟩
  · intro v hv
    obtain ⟨hvAE, hvBF⟩ := Finset.mem_inter.mp hv
    obtain ⟨hvB, hvFD⟩ := Finset.mem_inter.mp hvBF
    have hvE : v ∈ E := by
      rcases Finset.mem_union.mp hvAE with hA | hEC
      · exact hSE (Finset.mem_inter.mpr ⟨hA, hvB⟩)
      · exact (Finset.mem_inter.mp hEC).1
    have hvC : v ∈ C := by
      rcases Finset.mem_union.mp hvAE with hA | hEC
      · exact hAC hA
      · exact (Finset.mem_inter.mp hEC).2
    have hvF : v ∈ F := by
      rcases Finset.mem_union.mp hvFD with hF | hD
      · exact hF
      · exact hTF (Finset.mem_inter.mpr ⟨hvC, hD⟩)
    exact Finset.mem_inter.mpr ⟨hvE, hvF⟩

theorem hasDisjointSTPaths_of_nested_separations {A B C D : Finset V}
    (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D)
    (hAC : A ⊆ C) (hDB : D ⊆ B) {k : ℕ}
    (hmin : ∀ E F : Finset V, IsVertexSeparation G E F →
      A ⊆ E → E ⊆ C → D ⊆ F → F ⊆ B → k ≤ (E ∩ F).card) :
    HasDisjointSTPaths G (A ∩ B) (C ∩ D) k := by
  rcases Menger.finite_vertex_menger_sharp G (A ∩ B) (C ∩ D) k with
    hpaths | ⟨J, hJ, hsep⟩
  · exact hpaths
  · obtain ⟨E, F, hEF, hJF, hSE, hTF⟩ := exists_vertexSeparation_of_STSeparator hsep
    obtain ⟨E', F', hEF', hAE, hEC, hDF, hFB, hsub⟩ :=
      nested_separation_normalize hAB hCD hEF hAC hDB hSE hTF
    have hle := (hmin E' F' hEF' hAE hEC hDF hFB).trans (Finset.card_le_card hsub)
    rw [hJF] at hle
    omega

lemma walk_support_subset_right_of_avoids_separator {A B : Finset V}
    (hAB : IsVertexSeparation G A B) {u v : V} (p : G.Walk u v)
    (hvB : v ∈ B) (havoid : ∀ x ∈ p.support, x ∉ A ∩ B) :
    ∀ x ∈ p.support, x ∈ B := by
  induction p with
  | nil => simpa using hvB
  | @cons a b c hab p ih =>
    have htail := ih hvB (fun x hx ↦ havoid x (by simp [hx]))
    have hbB := htail b p.start_mem_support
    have hbA : b ∉ A := fun hbA ↦
      havoid b (by simp [p.start_mem_support]) (Finset.mem_inter.mpr ⟨hbA, hbB⟩)
    have haB := hAB.flip.adj_mem_left hbB hbA hab.symm
    simpa only [SimpleGraph.Walk.support_cons, List.mem_cons, forall_eq_or_imp] using
      And.intro haB htail

lemma GraphPath.vertexSet_subset_right_of_clean_left {A B : Finset V}
    (hAB : IsVertexSeparation G A B) (P : GraphPath G)
    (hsource : P.source ∈ B) (htarget : P.target ∈ B)
    (hclean : ∀ v ∈ P.vertexSet, v ∈ A ∩ B → v = P.source) :
    P.vertexSet ⊆ B := by
  rcases P with ⟨s, t, p, hp⟩
  cases p with
  | nil => simpa [GraphPath.vertexSet] using hsource
  | cons h p =>
    have hnot := (SimpleGraph.Walk.cons_isPath_iff h p).mp hp |>.2
    have htail : ∀ v ∈ p.support, v ∈ B :=
      walk_support_subset_right_of_avoids_separator hAB p htarget (by
        intro v hv hvAB
        have hvs : v = s := hclean v (by simpa [GraphPath.vertexSet] using Or.inr hv) hvAB
        exact hnot (hvs ▸ hv))
    intro v hv
    have hv' : v = s ∨ v ∈ p.support := by simpa [GraphPath.vertexSet] using hv
    rcases hv' with rfl | hv
    · exact hsource
    · exact htail v hv

lemma GraphPath.endpointClean_staysIn_nested_interval {A B C D : Finset V}
    (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D)
    (hAC : A ⊆ C) (hDB : D ⊆ B) (P : GraphPath G)
    (hP : P.EndpointClean (A ∩ B) (C ∩ D)) : P.vertexSet ⊆ B ∩ C := by
  have hB : P.vertexSet ⊆ B := GraphPath.vertexSet_subset_right_of_clean_left hAB P
    (Finset.mem_inter.mp hP.source_mem).2 (hDB (Finset.mem_inter.mp hP.target_mem).2)
    (fun _ hv hs ↦ hP.left_eq_source hv hs)
  have hC : P.reverse.vertexSet ⊆ C :=
    GraphPath.vertexSet_subset_right_of_clean_left hCD.flip P.reverse
      (Finset.mem_inter.mp hP.target_mem).1 (hAC (Finset.mem_inter.mp hP.source_mem).1)
      (by
        intro v hv hvDC
        exact hP.right_eq_target (by simpa using hv)
          (by simpa only [Finset.inter_comm] using hvDC))
  intro v hv
  exact Finset.mem_inter.mpr ⟨hB hv, hC (by simpa using hv)⟩

theorem exists_clean_linkage_in_nested_interval {A B C D : Finset V}
    (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D)
    (hAC : A ⊆ C) (hDB : D ⊆ B) {k : ℕ}
    (hmin : ∀ E F : Finset V, IsVertexSeparation G E F →
      A ⊆ E → E ⊆ C → D ⊆ F → F ⊆ B → k ≤ (E ∩ F).card) :
    ∃ P : EndpointCleanPathPacking G (A ∩ B) (C ∩ D), P.card = k ∧
      ∀ i, (P.path i).vertexSet ⊆ B ∩ C := by
  obtain ⟨P, hP⟩ := HasAtLeastDisjointPaths.exists_exact
    (hasDisjointSTPaths_of_nested_separations hAB hCD hAC hDB hmin)
  refine ⟨P.toEndpointClean, hP, ?_⟩
  intro i
  exact GraphPath.endpointClean_staysIn_nested_interval
    hAB hCD hAC hDB (P.toEndpointClean.path i) (P.toEndpointClean.endpoint_clean i)

/-- An ordinary minor model on the left of a separation, with one root
in each branch set and with the roots covering the separator. -/
structure LeftRootedModel {I : Type*} (H : SimpleGraph I)
    (G : SimpleGraph V) (A B : Finset V) where
  branch : I → Finset V
  root : I → V
  connected : ∀ i, (G.induce (branch i : Set V)).Connected
  disjoint : Pairwise fun i j ↦ Disjoint (branch i) (branch j)
  subset_left : ∀ i, branch i ⊆ A
  boundary : ∀ i, branch i ∩ B = {root i}
  covers : ∀ v ∈ A ∩ B, ∃ i, root i = v
  edge : ∀ ⦃i j⦄, H.Adj i j →
    ∃ u ∈ branch i, ∃ v ∈ branch j, G.Adj u v

namespace LeftRootedModel
variable {I : Type*} {H : SimpleGraph I} {A B C D : Finset V}

omit [Fintype V] in
lemma root_mem (M : LeftRootedModel H G A B) (i : I) : M.root i ∈ M.branch i := by
  have hi : M.root i ∈ M.branch i ∩ B := by rw [M.boundary]; simp
  exact (Finset.mem_inter.mp hi).1

omit [Fintype V] in
lemma root_mem_separator (M : LeftRootedModel H G A B) (i : I) :
    M.root i ∈ A ∩ B := by
  have hi : M.root i ∈ M.branch i ∩ B := by rw [M.boundary]; simp
  exact Finset.mem_inter.mpr ⟨M.subset_left i (Finset.mem_inter.mp hi).1,
    (Finset.mem_inter.mp hi).2⟩

omit [Fintype V] in
lemma root_injective (M : LeftRootedModel H G A B) : Function.Injective M.root := by
  intro i j hij
  by_contra hne
  exact Finset.disjoint_left.mp (M.disjoint hne) (M.root_mem i) (by rw [hij]; exact M.root_mem j)

omit [Fintype V] in
lemma eq_root_of_mem_branch_of_mem_right (M : LeftRootedModel H G A B)
    {i : I} {v : V} (hv : v ∈ M.branch i) (hvB : v ∈ B) : v = M.root i := by
  have h := Finset.mem_inter.mpr ⟨hv, hvB⟩
  rw [M.boundary] at h
  exact Finset.mem_singleton.mp h

/-- Extend each branch set along its uniquely assigned clean path. -/
noncomputable def transport (M : LeftRootedModel H G A B)
    (hAC : A ⊆ C) (hDB : D ⊆ B)
    (P : EndpointCleanPathPacking G (A ∩ B) (C ∩ D))
    (hS : P.sourceSet = A ∩ B) (hT : P.targetSet = C ∩ D)
    (hstay : ∀ i, (P.path i).vertexSet ⊆ B ∩ C) : LeftRootedModel H G C D := by
  have hex (i : I) : ∃ j : P.Index, (P.path j).source = M.root i :=
    P.exists_index_source_eq_of_mem_sourceSet (by rw [hS]; exact M.root_mem_separator i)
  let f (i : I) : P.Index := Classical.choose (hex i)
  have hf (i : I) : (P.path (f i)).source = M.root i := Classical.choose_spec (hex i)
  have hfinj : Function.Injective f := by
    intro i j hij
    apply M.root_injective
    rw [← hf i, ← hf j, hij]
  have hfsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := M.covers _ (P.endpoint_clean j).source_mem
    exact ⟨i, P.source_injective ((hf i).trans hi)⟩
  have hpath_old (i j : I) (hne : i ≠ j) :
      Disjoint (P.path (f i)).vertexSet (M.branch j) := by
    rw [Finset.disjoint_left]
    intro v hvP hvM
    have hvAB : v ∈ A ∩ B := Finset.mem_inter.mpr
      ⟨M.subset_left j hvM, (Finset.mem_inter.mp (hstay (f i) hvP)).1⟩
    have heq : v = M.root i := ((P.endpoint_clean (f i)).left_eq_source hvP hvAB).trans (hf i)
    exact Finset.disjoint_left.mp (M.disjoint hne) (heq ▸ M.root_mem i) hvM
  refine {
    branch := fun i ↦ M.branch i ∪ (P.path (f i)).vertexSet
    root := fun i ↦ (P.path (f i)).target
    connected := ?_
    disjoint := ?_
    subset_left := ?_
    boundary := ?_
    covers := ?_
    edge := ?_
  }
  · intro i
    have hmeet : ((M.branch i : Set V) ∩ ((P.path (f i)).vertexSet : Set V)).Nonempty :=
      ⟨M.root i, M.root_mem i, by rw [← hf i]; exact GraphPath.source_mem_vertexSet _⟩
    rw [Finset.coe_union]
    exact SimpleGraph.induce_union_connected (M.connected i).preconnected
      (P.path (f i)).connected_induce_vertexSet.preconnected hmeet
  · intro i j hij
    exact Finset.disjoint_union_left.mpr ⟨
      Finset.disjoint_union_right.mpr ⟨M.disjoint hij, (hpath_old j i hij.symm).symm⟩,
      Finset.disjoint_union_right.mpr ⟨hpath_old i j hij,
        P.node_disjoint (fun h ↦ hij (hfinj h))⟩⟩
  · intro i v hv
    rcases Finset.mem_union.mp hv with hvM | hvP
    · exact hAC (M.subset_left i hvM)
    · exact (Finset.mem_inter.mp (hstay (f i) hvP)).2
  · intro i
    ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hvM | hvP, hvD⟩
      · have heq : v = M.root i := M.eq_root_of_mem_branch_of_mem_right hvM (hDB hvD)
        have hvP : v ∈ (P.path (f i)).vertexSet := by
          rw [heq, ← hf i]
          exact GraphPath.source_mem_vertexSet _
        exact (P.endpoint_clean (f i)).right_eq_target hvP
          (Finset.mem_inter.mpr ⟨hAC (M.subset_left i hvM), hvD⟩)
      · exact (P.endpoint_clean (f i)).right_eq_target hvP
          (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hstay (f i) hvP)).2, hvD⟩)
    · rintro rfl
      exact ⟨Or.inr (GraphPath.target_mem_vertexSet _),
        (Finset.mem_inter.mp (P.endpoint_clean (f i)).target_mem).2⟩
  · intro v hv
    obtain ⟨j, hj⟩ := P.exists_index_target_eq_of_mem_targetSet (by rw [hT]; exact hv)
    obtain ⟨i, rfl⟩ := hfsurj j
    exact ⟨i, hj⟩
  · intro i j hij
    obtain ⟨u, hu, v, hv, huv⟩ := M.edge hij
    exact ⟨u, Finset.mem_union.mpr (Or.inl hu), v,
      Finset.mem_union.mpr (Or.inl hv), huv⟩

theorem exists_transport_of_nested (M : LeftRootedModel H G A B)
    (hAB : IsVertexSeparation G A B) (hCD : IsVertexSeparation G C D)
    (hAC : A ⊆ C) (hDB : D ⊆ B) {k : ℕ}
    (hABcard : (A ∩ B).card = k) (hCDcard : (C ∩ D).card = k)
    (hmin : ∀ E F : Finset V, IsVertexSeparation G E F →
      A ⊆ E → E ⊆ C → D ⊆ F → F ⊆ B → k ≤ (E ∩ F).card) :
    Nonempty (LeftRootedModel H G C D) := by
  obtain ⟨P, hP, hstay⟩ := exists_clean_linkage_in_nested_interval hAB hCD hAC hDB hmin
  have hS : P.sourceSet = A ∩ B := Finset.eq_of_subset_of_card_le P.sourceSet_subset_left
    (by rw [P.sourceSet_card, hP, hABcard])
  have hT : P.targetSet = C ∩ D := Finset.eq_of_subset_of_card_le P.targetSet_subset_right
    (by rw [P.targetSet_card, hP, hCDcard])
  exact ⟨M.transport hAC hDB P hS hT hstay⟩

end LeftRootedModel

end
end Erdos73
