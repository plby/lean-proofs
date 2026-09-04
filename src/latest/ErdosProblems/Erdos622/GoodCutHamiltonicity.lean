/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import ErdosProblems.Erdos622.GoodCut
import ErdosProblems.Erdos622.Core
import ErdosProblems.Erdos622.Hamiltonicity
import ErdosProblems.Erdos622.Trichotomy
import ErdosProblems.Erdos622.BipartiteHamilton
import ErdosProblems.Erdos622.LinearForestPath

/-!
# Hamiltonicity from a good cut

This file contains the deterministic path-absorption argument in the
almost-bipartite case of the Draganić--Keevash--Müyesser proof.  The first
lemma below is the bookkeeping step used at the end of the argument: two
internally disjoint spanning paths with the same endpoints form a Hamilton
cycle.
-/

open Finset
open scoped SimpleGraph

namespace Erdos622.GoodCutHamiltonicity

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

open SimpleGraph

open Trichotomy

/-- Uniform-reservoir form of Hall's theorem.  If every demand has at least
as many available representatives as there are demands altogether, then the
representatives can be chosen distinctly. -/
theorem exists_injective_choice_of_card_le_all
    {I W : Type*} [Fintype I] [DecidableEq I] [DecidableEq W]
    (S : I → Finset W) (hlarge : ∀ i, Fintype.card I ≤ (S i).card) :
    ∃ f : I → W, Function.Injective f ∧ ∀ i, f i ∈ S i := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' S).mp
  intro T
  by_cases hT : T.Nonempty
  · obtain ⟨i, hiT⟩ := hT
    calc
      T.card ≤ Fintype.card I := Finset.card_le_univ T
      _ ≤ (S i).card := hlarge i
      _ ≤ (T.biUnion S).card := Finset.card_le_card (by
        intro w hw
        exact Finset.mem_biUnion.mpr ⟨i, hiT, hw⟩)
  · simpa [Finset.not_nonempty_iff_eq_empty.mp hT]

/-- The attachment demands at vertices of `T`: a vertex receives enough new
leaf edges to bring its degree in `F` up to two.  The definition is used only
when `F` has maximum degree at most two. -/
def AttachmentSlot (F : SimpleGraph V) (T : Finset V) :=
  Σ v : (T : Set V), Fin (2 - F.degree v.1)

noncomputable instance AttachmentSlot.instFintype
    (F : SimpleGraph V) (T : Finset V) : Fintype (AttachmentSlot F T) := by
  letI (v : (T : Set V)) : Fintype (Fin (2 - F.degree v.1)) :=
    Fin.fintype _
  exact Sigma.instFintype

noncomputable instance AttachmentSlot.instDecidableEq
    (F : SimpleGraph V) (T : Finset V) : DecidableEq (AttachmentSlot F T) :=
  Classical.decEq _

/-- Available crossing leaves for an attachment source.  Every chosen leaf
is kept outside `T`, so it is isolated in the original forest and distinct
representatives make it incident with only one new edge. -/
def attachmentCandidates
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y T : Finset V) (s : AttachmentSlot F T) : Finset V :=
  if s.1.1 ∈ X then (G.neighborFinset s.1.1 ∩ Y) \ T
  else (G.neighborFinset s.1.1 ∩ X) \ T

theorem mem_attachmentCandidates
    {X Y T : Finset V} {s : AttachmentSlot F T} {w : V} :
    w ∈ attachmentCandidates G X Y T s ↔
      w ∉ T ∧ G.Adj s.1.1 w ∧
        (if s.1.1 ∈ X then w ∈ Y else w ∈ X) := by
  by_cases hs : s.1.1 ∈ X
  · simp only [attachmentCandidates, hs, if_true, Finset.mem_sdiff,
      Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    tauto
  · simp only [attachmentCandidates, hs, if_false, Finset.mem_sdiff,
      Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    tauto

/-- Simultaneous distinct leaf selection for all degree deficits of a
linear forest.  This is the Hall-theoretic core of the first greedy step in
DKM Lemma 3.7. -/
theorem exists_injective_attachment
    {F : SimpleGraph V} {X Y T : Finset V}
    (hreservoir : ∀ s : AttachmentSlot F T,
      Fintype.card (AttachmentSlot F T) ≤
        (attachmentCandidates G X Y T s).card) :
    ∃ f : AttachmentSlot F T → V, Function.Injective f ∧
      ∀ s, f s ∉ T ∧ G.Adj s.1.1 (f s) ∧
        (if s.1.1 ∈ X then f s ∈ Y else f s ∈ X) := by
  obtain ⟨f, hf, hmem⟩ := exists_injective_choice_of_card_le_all
    (fun s : AttachmentSlot F T ↦ attachmentCandidates G X Y T s)
    hreservoir
  exact ⟨f, hf, fun s ↦ mem_attachmentCandidates.mp (hmem s)⟩

theorem card_le_attachmentCandidates_of_add_card_le
    {F : SimpleGraph V} {X Y T : Finset V} (s : AttachmentSlot F T)
    (hlarge : Fintype.card (AttachmentSlot F T) + T.card ≤
      (if s.1.1 ∈ X then (G.neighborFinset s.1.1 ∩ Y).card
       else (G.neighborFinset s.1.1 ∩ X).card)) :
    Fintype.card (AttachmentSlot F T) ≤
      (attachmentCandidates G X Y T s).card := by
  by_cases hs : s.1.1 ∈ X
  · simp only [hs, if_true] at hlarge
    simp only [attachmentCandidates, hs, if_true]
    have hsplit := Finset.card_sdiff_add_card_inter
      (G.neighborFinset s.1.1 ∩ Y) T
    have hinter : ((G.neighborFinset s.1.1 ∩ Y) ∩ T).card ≤ T.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hsub : (G.neighborFinset s.1.1 ∩ Y).card - T.card ≤
        ((G.neighborFinset s.1.1 ∩ Y) \ T).card := by omega
    exact (Nat.le_sub_of_add_le hlarge).trans hsub
  · simp only [hs, if_false] at hlarge
    simp only [attachmentCandidates, hs, if_false]
    have hsplit := Finset.card_sdiff_add_card_inter
      (G.neighborFinset s.1.1 ∩ X) T
    have hinter : ((G.neighborFinset s.1.1 ∩ X) ∩ T).card ≤ T.card :=
      Finset.card_le_card Finset.inter_subset_right
    have hsub : (G.neighborFinset s.1.1 ∩ X).card - T.card ≤
        ((G.neighborFinset s.1.1 ∩ X) \ T).card := by omega
    exact (Nat.le_sub_of_add_le hlarge).trans hsub

/-- Cross-degree lower bound, in the exact form used by the hierarchy of
constants, supplies all initial leaf attachments simultaneously. -/
theorem exists_injective_attachment_of_crossDegree
    {F : SimpleGraph V} {X Y T : Finset V}
    (hcross : ∀ v ∈ T,
      Fintype.card (AttachmentSlot F T) + T.card ≤
        (if v ∈ X then (G.neighborFinset v ∩ Y).card
         else (G.neighborFinset v ∩ X).card)) :
    ∃ f : AttachmentSlot F T → V, Function.Injective f ∧
      ∀ s, f s ∉ T ∧ G.Adj s.1.1 (f s) ∧
        (if s.1.1 ∈ X then f s ∈ Y else f s ∈ X) := by
  apply exists_injective_attachment
  intro s
  exact card_le_attachmentCandidates_of_add_card_le s (hcross s.1.1 s.1.2)

/-- The graph formed by the simultaneously chosen attachment edges. -/
def attachmentGraph (F : SimpleGraph V) (T : Finset V)
    (f : AttachmentSlot F T → V) : SimpleGraph V :=
  ⨆ s : AttachmentSlot F T, SimpleGraph.edge s.1.1 (f s)

@[simp]
theorem attachmentGraph_adj {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V} {u v : V} :
    (attachmentGraph F T f).Adj u v ↔
      ∃ s : AttachmentSlot F T,
        ((u = s.1.1 ∧ v = f s) ∨ (u = f s ∧ v = s.1.1)) ∧ u ≠ v := by
  simp only [attachmentGraph, SimpleGraph.iSup_adj, SimpleGraph.edge_adj]

/-- All selected attachment edges lie in the ambient graph. -/
theorem attachmentGraph_le
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V}
    (hadj : ∀ s, G.Adj s.1.1 (f s)) :
    attachmentGraph F T f ≤ G := by
  intro u v huv
  obtain ⟨s, h, -⟩ := attachmentGraph_adj.mp huv
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj s
  · exact (hadj s).symm

/-- Every new attachment vertex is incident with at most one attachment
edge, because representatives are chosen injectively and all sources lie in
`T` while all representatives lie outside `T`. -/
theorem attachmentGraph_degree_le_one_of_not_mem
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V} (hf : Function.Injective f)
    (hout : ∀ s, f s ∉ T) {w : V} (hw : w ∉ T) :
    (attachmentGraph F T f).degree w ≤ 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨sx, hx, -⟩ := attachmentGraph_adj.mp
    (by simpa only [SimpleGraph.mem_neighborFinset] using hx)
  obtain ⟨sy, hy, -⟩ := attachmentGraph_adj.mp
    (by simpa only [SimpleGraph.mem_neighborFinset] using hy)
  have hsource (s : AttachmentSlot F T) : s.1.1 ∈ T := s.1.2
  have hfx : w = f sx := by
    rcases hx with ⟨hws, -⟩ | ⟨hwf, -⟩
    · exact (hw (hws ▸ hsource sx)).elim
    · exact hwf
  have hfy : w = f sy := by
    rcases hy with ⟨hws, -⟩ | ⟨hwf, -⟩
    · exact (hw (hws ▸ hsource sy)).elim
    · exact hwf
  have hs : sx = sy := hf (hfx.symm.trans hfy)
  have hxval : x = sx.1.1 := by
    rcases hx with ⟨hws, -⟩ | ⟨-, hxs⟩
    · exact (hw (hws.symm ▸ hsource sx)).elim
    · exact hxs
  have hyval : y = sy.1.1 := by
    rcases hy with ⟨hws, -⟩ | ⟨-, hys⟩
    · exact (hw (hws.symm ▸ hsource sy)).elim
    · exact hys
  exact hxval.trans ((congrArg (fun s : AttachmentSlot F T ↦ s.1.1) hs).trans hyval.symm)

/-- Outside `T`, the original forest contributes no edges. -/
theorem forest_degree_eq_zero_of_support_subset
    {F : SimpleGraph V} {T : Finset V}
    (hsupp : F.support ⊆ (T : Set V)) {w : V} (hw : w ∉ T) :
    F.degree w = 0 := by
  rw [SimpleGraph.degree_eq_zero_iff_notMem_support]
  exact fun h ↦ hw (hsupp h)

/-- The selected leaves give every source exactly its requested number of
distinct attachment neighbours. -/
theorem attachmentGraph_degree_source
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V} (hf : Function.Injective f)
    (hout : ∀ s, f s ∉ T) (v : (T : Set V)) :
    (attachmentGraph F T f).degree v.1 = 2 - F.degree v.1 := by
  let e : Fin (2 - F.degree v.1) → V := fun i ↦ f ⟨v, i⟩
  have heinj : Function.Injective e := fun i j hij ↦ by
    cases hf hij
    rfl
  have hne : ∀ i, e i ≠ v.1 := by
    intro i hi
    apply hout ⟨v, i⟩
    change f ⟨v, i⟩ ∈ T
    change f ⟨v, i⟩ = v.1 at hi
    rw [hi]
    exact v.2
  have hneighbors :
      (attachmentGraph F T f).neighborFinset v.1 =
        Finset.univ.map ⟨e, heinj⟩ := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, attachmentGraph_adj,
      Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨s, h, -⟩
      rcases h with ⟨hvs, hw⟩ | ⟨hvf, hw⟩
      · subst w
        have hsv : s.1 = v := Subtype.ext hvs.symm
        subst hsv
        exact ⟨s.2, rfl⟩
      · exact (hout s (hvf ▸ v.2)).elim
    · rintro ⟨i, rfl⟩
      exact ⟨⟨v, i⟩, Or.inl ⟨rfl, rfl⟩, (hne i).symm⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hneighbors,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Attaching the chosen distinct leaves fills every degree deficit without
creating a cycle.  This packages the first absorption step as a genuine
linear forest rather than merely a family of chosen vertices. -/
theorem linearForest_sup_attachmentGraph
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V}
    (hlin : LinearForest F) (hsupp : F.support ⊆ (T : Set V))
    (hf : Function.Injective f) (hout : ∀ s, f s ∉ T) :
    LinearForest (F ⊔ attachmentGraph F T f) := by
  let P := F ⊔ attachmentGraph F T f
  let : DecidableRel P.Adj := Classical.decRel _
  have hdegree : ∀ v, P.degree v ≤ 2 := by
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_sup]
    calc
      (F.neighborFinset v ∪ (attachmentGraph F T f).neighborFinset v).card
          ≤ F.degree v + (attachmentGraph F T f).degree v := by
            simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
              Finset.card_union_le (F.neighborFinset v)
                ((attachmentGraph F T f).neighborFinset v)
      _ ≤ 2 := by
        by_cases hv : v ∈ T
        · let vT : (T : Set V) := ⟨v, hv⟩
          have hE := attachmentGraph_degree_source hf hout vT
          change (attachmentGraph F T f).degree v = 2 - F.degree v at hE
          rw [hE]
          exact (Nat.add_sub_of_le (hlin.2 v)).le
        · have hFzero := forest_degree_eq_zero_of_support_subset hsupp hv
          have hEle := attachmentGraph_degree_le_one_of_not_mem hf hout hv
          omega
  change LinearForest P
  refine ⟨?_, hdegree⟩
  intro u p hp
  have hvertices : ∀ v, v ∈ p.support → v ∈ T := by
    intro v hv
    by_contra hvT
    have hPdeg : P.degree v ≤ 1 := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.neighborFinset_sup]
      calc
        (F.neighborFinset v ∪ (attachmentGraph F T f).neighborFinset v).card
            ≤ F.degree v + (attachmentGraph F T f).degree v := by
              simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
                Finset.card_union_le (F.neighborFinset v)
                  ((attachmentGraph F T f).neighborFinset v)
        _ ≤ 1 := by
          have hFzero := forest_degree_eq_zero_of_support_subset hsupp hvT
          have hEle := attachmentGraph_degree_le_one_of_not_mem hf hout hvT
          omega
    have htwo := hp.ncard_neighborSet_toSubgraph_eq_two hv
    have hle : (p.toSubgraph.neighborSet v).ncard ≤
        (P.neighborSet v).ncard :=
      Set.ncard_le_ncard (p.toSubgraph.neighborSet_subset v)
    have hPcard : (P.neighborSet v).ncard = P.degree v := by
      rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    rw [htwo, hPcard] at hle
    omega
  have hedge : ∀ e, e ∈ p.edges → e ∈ F.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have habP : P.Adj a b := p.edges_subset_edgeSet he
      have haSupport : a ∈ p.support :=
        p.fst_mem_support_of_mem_edges he
      have hbSupport : b ∈ p.support :=
        p.snd_mem_support_of_mem_edges he
      have haT := hvertices a haSupport
      have hbT := hvertices b hbSupport
      rcases (SimpleGraph.sup_adj F (attachmentGraph F T f) a b).mp habP with habF | habE
      · exact habF
      · obtain ⟨s, hs, -⟩ := attachmentGraph_adj.mp habE
        rcases hs with ⟨-, hbf⟩ | ⟨haf, -⟩
        · exact (hout s (hbf ▸ hbT)).elim
        · exact (hout s (haf ▸ haT)).elim
  exact hlin.1 (p.transfer F hedge) (hp.transfer hedge)

/-- Attachment vertices, viewed as a finite set rather than the range of a
function. -/
noncomputable def attachmentVertices (F : SimpleGraph V) (T : Finset V)
    (f : AttachmentSlot F T → V) : Finset V :=
  Finset.univ.image f

@[simp]
theorem mem_attachmentVertices {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V} {w : V} :
    w ∈ attachmentVertices F T f ↔ ∃ s, f s = w := by
  simp [attachmentVertices]

/-- There are at most two attachment demands per source. -/
theorem card_attachmentSlot_le_two_mul (F : SimpleGraph V) (T : Finset V) :
    Fintype.card (AttachmentSlot F T) ≤ 2 * T.card := by
  change Fintype.card (Σ v : ↥(T : Set V), Fin (2 - F.degree v.1)) ≤ 2 * T.card
  rw [Fintype.card_sigma]
  calc
    (∑ v : ↥(T : Set V), Fintype.card (Fin (2 - F.degree v.1)))
        ≤ ∑ _v : ↥(T : Set V), 2 := by
          apply Finset.sum_le_sum
          intro v _
          simp only [Fintype.card_fin]
          exact Nat.sub_le 2 _
    _ = T.card * 2 := by simp
    _ = 2 * T.card := Nat.mul_comm _ _

/-- Every vertex used by the attached forest is either an old source or a
chosen representative. -/
theorem support_sup_attachmentGraph_subset
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V}
    (hsupp : F.support ⊆ (T : Set V)) :
    (F ⊔ attachmentGraph F T f).support ⊆
      (↑(T ∪ attachmentVertices F T f) : Set V) := by
  intro v hv
  obtain ⟨w, hvw⟩ := (SimpleGraph.mem_support _).mp hv
  rcases (SimpleGraph.sup_adj F (attachmentGraph F T f) v w).mp hvw with hvwF | hvwE
  · exact by
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inl (hsupp ((SimpleGraph.mem_support _).mpr ⟨w, hvwF⟩))
  · obtain ⟨s, hs, -⟩ := attachmentGraph_adj.mp hvwE
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
    rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl s.1.2
    · exact Or.inr (mem_attachmentVertices.mpr ⟨s, rfl⟩)

/-- The support of the initial attached forest has size at most three times
the number of sources. -/
theorem card_support_sup_attachmentGraph_le_three_mul
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V}
    (hsupp : F.support ⊆ (T : Set V)) :
    (F ⊔ attachmentGraph F T f).support.toFinset.card ≤ 3 * T.card := by
  have hsub : (F ⊔ attachmentGraph F T f).support.toFinset ⊆
      T ∪ attachmentVertices F T f := by
    intro v hv
    exact support_sup_attachmentGraph_subset hsupp (Set.mem_toFinset.mp hv)
  have himage : (attachmentVertices F T f).card ≤
      Fintype.card (AttachmentSlot F T) := by
    simpa only [attachmentVertices, Finset.card_univ] using
      (Finset.card_image_le :
        (Finset.univ.image f).card ≤
          (Finset.univ : Finset (AttachmentSlot F T)).card)
  calc
    (F ⊔ attachmentGraph F T f).support.toFinset.card
        ≤ (T ∪ attachmentVertices F T f).card := Finset.card_le_card hsub
    _ ≤ T.card + (attachmentVertices F T f).card := Finset.card_union_le _ _
    _ ≤ T.card + Fintype.card (AttachmentSlot F T) := Nat.add_le_add_left himage _
    _ ≤ T.card + 2 * T.card := Nat.add_le_add_left
      (card_attachmentSlot_le_two_mul F T) _
    _ = 3 * T.card := by omega

/-- At a source vertex the old and new neighbourhoods are disjoint, hence
the degree is exactly two after filling the deficit. -/
theorem degree_sup_attachmentGraph_source_eq_two
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V}
    (hlin : LinearForest F) (hsupp : F.support ⊆ (T : Set V))
    (hf : Function.Injective f) (hout : ∀ s, f s ∉ T)
    (v : (T : Set V)) :
    (F ⊔ attachmentGraph F T f).degree v.1 = 2 := by
  have hdisj : Disjoint (F.neighborFinset v.1)
      ((attachmentGraph F T f).neighborFinset v.1) := by
    rw [Finset.disjoint_left]
    intro w hwF hwE
    have hwAdj : F.Adj w v.1 := by
      have : F.Adj v.1 w := by
        simpa only [SimpleGraph.mem_neighborFinset] using hwF
      exact this.symm
    have hwT : w ∈ T := hsupp ((SimpleGraph.mem_support _).mpr ⟨v.1, hwAdj⟩)
    have hvwE : (attachmentGraph F T f).Adj v.1 w := by
      simpa only [SimpleGraph.mem_neighborFinset] using hwE
    obtain ⟨s, hs, -⟩ := attachmentGraph_adj.mp hvwE
    rcases hs with ⟨-, hw⟩ | ⟨hv, -⟩
    · exact hout s (hw ▸ hwT)
    · exact hout s (hv ▸ v.2)
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.neighborFinset_sup, Finset.card_union_of_disjoint hdisj]
  change F.degree v.1 + (attachmentGraph F T f).degree v.1 = 2
  rw [attachmentGraph_degree_source hf hout v]
  exact Nat.add_sub_of_le (hlin.2 v.1)

/-- In particular every endpoint of the attached forest is a newly chosen
vertex, and therefore lies outside the source set. -/
theorem endpoint_not_mem_of_sup_attachmentGraph
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V}
    (hlin : LinearForest F) (hsupp : F.support ⊆ (T : Set V))
    (hf : Function.Injective f) (hout : ∀ s, f s ∉ T)
    {v : V} (hdeg : (F ⊔ attachmentGraph F T f).degree v ≤ 1) :
    v ∉ T := by
  intro hv
  let vT : (T : Set V) := ⟨v, hv⟩
  have heq := degree_sup_attachmentGraph_source_eq_two hlin hsupp hf hout vT
  change (F ⊔ attachmentGraph F T f).degree v = 2 at heq
  omega

/-- Instance-independent form of the exact source-degree statement. -/
theorem ncard_neighborSet_sup_attachmentGraph_source_eq_two
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V}
    (hlin : LinearForest F) (hsupp : F.support ⊆ (T : Set V))
    (hf : Function.Injective f) (hout : ∀ s, f s ∉ T)
    (v : (T : Set V)) :
    ((F ⊔ attachmentGraph F T f).neighborSet v.1).ncard = 2 := by
  have hdeg := degree_sup_attachmentGraph_source_eq_two hlin hsupp hf hout v
  rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
  exact hdeg

/-- Every source actually occurs in the support of the attached forest. -/
theorem subset_support_sup_attachmentGraph
    {F : SimpleGraph V} {T : Finset V}
    {f : AttachmentSlot F T → V}
    (hlin : LinearForest F) (hsupp : F.support ⊆ (T : Set V))
    (hf : Function.Injective f)
    (hout : ∀ s, f s ∉ T) :
    T ⊆ (F ⊔ attachmentGraph F T f).support.toFinset := by
  intro v hv
  have hdeg := degree_sup_attachmentGraph_source_eq_two hlin
    hsupp hf hout (⟨v, hv⟩ : (T : Set V))
  apply Set.mem_toFinset.mpr
  apply (SimpleGraph.degree_pos_iff_mem_support _ _).mp
  exact hdeg ▸ Nat.zero_lt_succ 1

/-- Adding a fresh leaf to one component does not make that leaf reachable
from a different component.  This elementary fact lets the connector
construction apply `LinearForest.sup_edge_of_not_reachable` successively. -/
theorem not_reachable_sup_edge_fresh
    {P : SimpleGraph V} {u v w : V}
    (hv : v ∈ P.support) (hu : u ∈ P.support) (hw : w ∉ P.support)
    (huv : ¬ P.Reachable v u) :
    ¬ (P ⊔ SimpleGraph.edge u w).Reachable v w := by
  intro hr
  apply hr.elim_path
  intro q
  let p : (P ⊔ SimpleGraph.edge u w).Walk v w := q.1
  have hp : p.IsPath := q.2
  have hvw : v ≠ w := by
    intro h
    subst w
    exact hw hv
  have hqNotNil : ¬p.Nil :=
    SimpleGraph.Walk.not_nil_of_ne hvw
  have hlast := p.adj_penultimate hqNotNil
  have hpen : p.penultimate = u := by
    rcases (SimpleGraph.sup_adj P (SimpleGraph.edge u w) p.penultimate w).mp hlast with hP | he
    · exact (hw hP.mem_support_right).elim
    · simp only [SimpleGraph.edge_adj] at he
      rcases he.1 with h | h
      · exact h.1
      · exact (hw (h.2 ▸ hu)).elim
  have hwDrop : w ∉ p.dropLast.support := by
    intro hwd
    have hn := hp.support_nodup
    rw [SimpleGraph.Walk.support_eq_concat, List.nodup_concat] at hn
    exact hn.1 (by simpa [SimpleGraph.Walk.support_dropLast hqNotNil] using hwd)
  have hedge : ∀ e, e ∈ p.dropLast.edges → e ∈ P.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : (P ⊔ SimpleGraph.edge u w).Adj a b :=
        p.dropLast.edges_subset_edgeSet he
      rcases (SimpleGraph.sup_adj P (SimpleGraph.edge u w) a b).mp hab with habP | habE
      · exact habP
      · have ha : a ∈ p.dropLast.support :=
          p.dropLast.fst_mem_support_of_mem_edges he
        have hb : b ∈ p.dropLast.support :=
          p.dropLast.snd_mem_support_of_mem_edges he
        simp only [SimpleGraph.edge_adj] at habE
        rcases habE.1 with h | h
        · exact (hwDrop (h.2 ▸ hb)).elim
        · exact (hwDrop (h.1 ▸ ha)).elim
  have hwalk : P.Walk v p.penultimate := p.dropLast.transfer P hedge
  rw [hpen] at hwalk
  exact huv hwalk.reachable

/-- Pigeonhole form of the common-neighbour estimate.  Two subsets of a
finite reservoir whose total size exceeds the reservoir plus a forbidden set
have a common element outside the forbidden set. -/
theorem exists_mem_inter_not_mem_of_card_add_lt
    {A B U Z : Finset V} (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hcard : U.card + Z.card < A.card + B.card) :
    ∃ w, w ∈ A ∧ w ∈ B ∧ w ∉ Z := by
  by_contra h
  push_neg at h
  have hinter : A ∩ B ⊆ Z := by
    intro w hw
    exact h w (Finset.mem_inter.mp hw).1 (Finset.mem_inter.mp hw).2
  have hunion : A ∪ B ⊆ U := Finset.union_subset hAU hBU
  have hsum := Finset.card_union_add_card_inter A B
  have hu := Finset.card_le_card hunion
  have hi := Finset.card_le_card hinter
  omega

/-- Crossing neighbours of a vertex, oriented by the cut side containing
the vertex. -/
def crossNeighbors (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (v : V) : Finset V :=
  if v ∈ X then G.neighborFinset v ∩ Y else G.neighborFinset v ∩ X

@[simp]
theorem mem_crossNeighbors {X Y : Finset V} {v w : V} :
    w ∈ crossNeighbors G X Y v ↔
      G.Adj v w ∧ (if v ∈ X then w ∈ Y else w ∈ X) := by
  by_cases hv : v ∈ X <;> simp [crossNeighbors, hv, and_comm]

theorem crossNeighbors_swap {X Y : Finset V} (hcut : IsCut X Y) (v : V) :
    crossNeighbors G Y X v = crossNeighbors G X Y v := by
  by_cases hvX : v ∈ X
  · have hvY : v ∉ Y := (hcut.mem_left_iff v).mp hvX
    simp only [crossNeighbors, hvX, hvY, if_true, if_false]
  · have hvY : v ∈ Y := (hcut.mem_right_iff v).mpr hvX
    simp only [crossNeighbors, hvX, hvY, if_true, if_false]

theorem crossNeighbors_subset_right {X Y : Finset V} {v : V} (hv : v ∈ X) :
    crossNeighbors G X Y v ⊆ Y := by
  intro w hw
  simpa [hv] using (mem_crossNeighbors.mp hw).2

theorem crossNeighbors_subset_left {X Y : Finset V} {v : V} (hv : v ∉ X) :
    crossNeighbors G X Y v ⊆ X := by
  intro w hw
  simpa [hv] using (mem_crossNeighbors.mp hw).2

/-- Same-side high-degree endpoints have a fresh common crossing neighbour. -/
theorem exists_common_crossNeighbor_not_mem
    {X Y Z : Finset V} (hcut : IsCut X Y) {u v : V}
    (huX : u ∈ X) (hvX : v ∈ X)
    (hcard : Y.card + Z.card <
      (crossNeighbors G X Y u).card + (crossNeighbors G X Y v).card) :
    ∃ w, G.Adj u w ∧ G.Adj v w ∧ w ∈ Y ∧ w ∉ Z := by
  obtain ⟨w, hwu, hwv, hwZ⟩ := exists_mem_inter_not_mem_of_card_add_lt
    (crossNeighbors_subset_right (G := G) huX)
    (crossNeighbors_subset_right (G := G) hvX) hcard
  have hu := mem_crossNeighbors.mp hwu
  have hv := mem_crossNeighbors.mp hwv
  exact ⟨w, hu.1, hv.1, by simpa [huX] using hu.2, hwZ⟩

/-- Symmetric same-side common-neighbour statement on the right side. -/
theorem exists_common_crossNeighbor_not_mem_right
    {X Y Z : Finset V} (hcut : IsCut X Y) {u v : V}
    (huY : u ∈ Y) (hvY : v ∈ Y)
    (hcard : X.card + Z.card <
      (crossNeighbors G X Y u).card + (crossNeighbors G X Y v).card) :
    ∃ w, G.Adj u w ∧ G.Adj v w ∧ w ∈ X ∧ w ∉ Z := by
  have huX : u ∉ X := (hcut.mem_right_iff u).mp huY
  have hvX : v ∉ X := (hcut.mem_right_iff v).mp hvY
  obtain ⟨w, hwu, hwv, hwZ⟩ := exists_mem_inter_not_mem_of_card_add_lt
    (crossNeighbors_subset_left (G := G) huX)
    (crossNeighbors_subset_left (G := G) hvX) hcard
  have hu := mem_crossNeighbors.mp hwu
  have hv := mem_crossNeighbors.mp hwv
  exact ⟨w, hu.1, hv.1, by simpa [huX] using hu.2, hwZ⟩

/-- A graph of maximum degree two has no more edges than supported
vertices.  This weak form is exactly what the absorber resource inequality
needs. -/
theorem card_edgeFinset_le_card_support_of_degree_le_two
    {P : SimpleGraph V} (hdeg : ∀ v, P.degree v ≤ 2) :
    P.edgeFinset.card ≤ P.support.toFinset.card := by
  have hsum := P.sum_degrees_support_eq_twice_card_edges
  have hle : ∑ v ∈ P.support.toFinset, P.degree v ≤
      ∑ _v ∈ P.support.toFinset, 2 := by
    apply Finset.sum_le_sum
    intro v _
    exact hdeg v
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at hle
  omega

/-- Every supported vertex contributes at least one to the degree sum. -/
theorem ncard_support_le_twice_card_edgeFinset (P : SimpleGraph V) :
    P.support.ncard ≤ 2 * P.edgeFinset.card := by
  have hle : P.support.toFinset.card ≤
      ∑ v ∈ P.support.toFinset, P.degree v := by
    calc
      P.support.toFinset.card = ∑ _v ∈ P.support.toFinset, 1 := by simp
      _ ≤ ∑ v ∈ P.support.toFinset, P.degree v := by
        apply Finset.sum_le_sum
        intro v hv
        exact (P.degree_pos_iff_mem_support v).mpr (Set.mem_toFinset.mp hv)
  have hsum := P.sum_degrees_support_eq_twice_card_edges
  have hsuppEq : P.support.ncard = P.support.toFinset.card := by
    have h := Set.ncard_coe_finset P.support.toFinset
    rw [Set.coe_toFinset] at h
    exact h
  rw [hsuppEq]
  exact hle.trans_eq hsum

/-- Admissible partial absorber forests.  Besides the structural and cut
conditions, the last inequality is the resource potential preserved by the
one- and two-vertex connector operations. -/
def AdmissibleForest (G F : SimpleGraph V) (X Y L : Finset V)
    (budget : ℕ) (P : SimpleGraph V) : Prop :=
  F ≤ P ∧ P ≤ G ∧ LinearForest P ∧
    (F.support ∪ (L : Set V)) ⊆ P.support ∧
    (∀ v, v ∈ P.support → (P.neighborSet v).ncard ≤ 1 → v ∉ L) ∧
    (∀ ⦃u v⦄, P.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X))) ∧
    3 * P.support.ncard ≤ budget + 2 * P.edgeSet.ncard

namespace AdmissibleForest

theorem linearForest {F X Y L budget P}
    (h : AdmissibleForest G F X Y L budget P) : LinearForest P := h.2.2.1

theorem support_card_le_budget {F X Y L budget P}
    (h : AdmissibleForest G F X Y L budget P) :
    P.support.ncard ≤ budget := by
  have hedge := card_edgeFinset_le_card_support_of_degree_le_two
    (h.linearForest.2)
  have hedge' : P.edgeSet.ncard ≤ P.support.ncard := by
    have hedgeEq : P.edgeSet.ncard = P.edgeFinset.card := by
      rw [← P.coe_edgeFinset, Set.ncard_coe_finset]
    have hsuppEq : P.support.ncard = P.support.toFinset.card := by
      have h := Set.ncard_coe_finset P.support.toFinset
      rw [Set.coe_toFinset] at h
      exact h
    omega
  have hresource := h.2.2.2.2.2.2
  omega

end AdmissibleForest

/-- Hall selection supplies a nonempty family of admissible forests.  The
budget `9|T|` is three times the initial support bound `3|T|`; later connector
steps preserve the associated potential. -/
theorem exists_initial_admissibleForest
    {F : SimpleGraph V} {X Y L : Finset V}
    (hcut : IsCut X Y) (hFG : F ≤ G) (hlin : LinearForest F)
    (hsuppX : F.support ⊆ (X : Set V))
    (hcross : ∀ v ∈ F.support.toFinset ∪ L,
      Fintype.card (AttachmentSlot F (F.support.toFinset ∪ L)) +
          (F.support.toFinset ∪ L).card ≤
        (crossNeighbors G X Y v).card) :
    ∃ P : SimpleGraph V,
      AdmissibleForest G F X Y L
        (9 * (F.support.toFinset ∪ L).card) P := by
  let T := F.support.toFinset ∪ L
  have hsuppT : F.support ⊆ (T : Set V) := by
    intro v hv
    change v ∈ T
    exact Finset.mem_union.mpr (Or.inl (Set.mem_toFinset.mpr hv))
  have hchoice : ∃ f : AttachmentSlot F T → V, Function.Injective f ∧
      ∀ s, f s ∉ T ∧ G.Adj s.1.1 (f s) ∧
        (if s.1.1 ∈ X then f s ∈ Y else f s ∈ X) := by
    apply exists_injective_attachment_of_crossDegree
    intro v hv
    by_cases hvX : v ∈ X
    · simpa only [T, crossNeighbors, hvX, if_true] using hcross v hv
    · simpa only [T, crossNeighbors, hvX, if_false] using hcross v hv
  obtain ⟨f, hf, hfprop⟩ := hchoice
  let P := F ⊔ attachmentGraph F T f
  let : DecidableRel P.Adj := Classical.decRel _
  have hEle : attachmentGraph F T f ≤ G :=
    attachmentGraph_le (fun s ↦ (hfprop s).2.1)
  have hPlinear : LinearForest P := by
    simpa only [P] using linearForest_sup_attachmentGraph hlin hsuppT hf
      (fun s ↦ (hfprop s).1)
  refine ⟨P, ?_⟩
  refine ⟨?_, ?_, hPlinear, ?_, ?_, ?_, ?_⟩
  · exact le_sup_left
  · exact sup_le hFG hEle
  · intro v hv
    change v ∈ F.support ∨ v ∈ (L : Set V) at hv
    rcases hv with hvF | hvL
    · exact SimpleGraph.support_mono le_sup_left hvF
    · have hvT : v ∈ T := by
        change v ∈ F.support.toFinset ∪ L
        exact Finset.mem_union.mpr (Or.inr hvL)
      let vT : (T : Set V) := ⟨v, hvT⟩
      have hncard := ncard_neighborSet_sup_attachmentGraph_source_eq_two
        hlin hsuppT hf (fun s ↦ (hfprop s).1) vT
      have hpos : 0 < ((F ⊔ attachmentGraph F T f).neighborSet v).ncard := by
        change ((F ⊔ attachmentGraph F T f).neighborSet v).ncard = 2 at hncard
        omega
      obtain ⟨w, hw⟩ :=
        (Set.ncard_pos (s := (F ⊔ attachmentGraph F T f).neighborSet v)).mp hpos
      exact (SimpleGraph.mem_support _).mpr ⟨w, hw⟩
  · intro v hvP hdegN hvL
    have hvL' : v ∈ L := hvL
    have hvT : v ∈ T := by
      change v ∈ F.support.toFinset ∪ L
      exact Finset.mem_union.mpr (Or.inr hvL')
    let vT : (T : Set V) := ⟨v, hvT⟩
    have hncard := ncard_neighborSet_sup_attachmentGraph_source_eq_two hlin hsuppT hf
      (fun s ↦ (hfprop s).1) vT
    change ((F ⊔ attachmentGraph F T f).neighborSet v).ncard ≤ 1 at hdegN
    change ((F ⊔ attachmentGraph F T f).neighborSet v).ncard = 2 at hncard
    exact (by omega)
  · intro u v huv
    rcases (SimpleGraph.sup_adj F (attachmentGraph F T f) u v).mp huv with huvF | huvE
    · exact Or.inl huvF
    · right
      obtain ⟨s, hs, -⟩ := attachmentGraph_adj.mp huvE
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · by_cases hsX : s.1.1 ∈ X
        · exact Or.inl ⟨hsX, by simpa [hsX] using (hfprop s).2.2⟩
        · have hsY : s.1.1 ∈ Y := (hcut.mem_right_iff s.1.1).mpr hsX
          exact Or.inr ⟨hsY, by simpa [hsX] using (hfprop s).2.2⟩
      · by_cases hsX : s.1.1 ∈ X
        · exact Or.inr ⟨by simpa [hsX] using (hfprop s).2.2, hsX⟩
        · have hsY : s.1.1 ∈ Y := (hcut.mem_right_iff s.1.1).mpr hsX
          exact Or.inl ⟨by simpa [hsX] using (hfprop s).2.2, hsY⟩
  · have hsub := support_sup_attachmentGraph_subset
      (F := F) (T := T) (f := f) hsuppT
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_coe_finset] at hle
    have himage : (attachmentVertices F T f).card ≤
        Fintype.card (AttachmentSlot F T) := by
      simpa only [attachmentVertices, Finset.card_univ] using
        (Finset.card_image_le :
          (Finset.univ.image f).card ≤
            (Finset.univ : Finset (AttachmentSlot F T)).card)
    have hunion := Finset.card_union_le T (attachmentVertices F T f)
    have hslots := card_attachmentSlot_le_two_mul F T
    have hsuppN : P.support.ncard ≤ 3 * T.card := by
      change (F ⊔ attachmentGraph F T f).support.ncard ≤ 3 * T.card
      omega
    have hbase : 3 * P.support.ncard ≤ 9 * T.card := by omega
    exact hbase.trans (Nat.le_add_right _ _)

/-- Passing to a connected-component subtype does not change the cardinality
of a vertex neighbourhood: every neighbour remains in the same component. -/
theorem ncard_neighborSet_toSimpleGraph_connectedComponent
    {P : SimpleGraph V} (C : P.ConnectedComponent) (v : C) :
    (C.toSimpleGraph.neighborSet v).ncard = (P.neighborSet v.1).ncard := by
  apply Set.ncard_congr (fun z _ ↦ z.1)
  · intro z hz
    exact (C.toSimpleGraph_adj v.2 z.2).mp hz
  · intro a b ha hb hab
    exact Subtype.ext hab
  · intro w hw
    have hwC : w ∈ C.supp := (C.mem_supp_congr_adj hw).mp v.2
    let z : C := ⟨w, hwC⟩
    refine ⟨z, (C.toSimpleGraph_adj v.2 z.2).mpr hw, rfl⟩

/-- Every supported component of a finite linear forest has a leaf. -/
theorem LinearForest.exists_leaf_reachable
    {P : SimpleGraph V} (hP : LinearForest P) {x : V}
    (hx : x ∈ P.support) :
    ∃ u, P.Reachable x u ∧ (P.neighborSet u).ncard = 1 := by
  let C := P.connectedComponentMk x
  have hxC : x ∈ C.supp := by
    exact (C.mem_supp_iff x).mpr rfl
  obtain ⟨y, hxy⟩ := (SimpleGraph.mem_support P).mp hx
  have hyC : y ∈ C.supp := (C.mem_supp_congr_adj hxy).mp hxC
  let xC : C := ⟨x, hxC⟩
  let yC : C := ⟨y, hyC⟩
  have hxyC : xC ≠ yC := by
    intro h
    exact hxy.ne (congrArg Subtype.val h)
  let : Nontrivial C := ⟨⟨xC, yC, hxyC⟩⟩
  let H := C.toSimpleGraph
  let : DecidableRel H.Adj := Classical.decRel _
  have htree : H.IsTree := by
    simpa only [H, C] using hP.1.isTree_connectedComponent C
  obtain ⟨u, hu⟩ := htree.exists_vert_degree_one_of_nontrivial
  refine ⟨u.1, ?_, ?_⟩
  · apply SimpleGraph.ConnectedComponent.exact
    exact (C.mem_supp_iff u.1).mp u.2 |>.symm
  · rw [← ncard_neighborSet_toSimpleGraph_connectedComponent C u,
      ← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    exact hu

/-- Since the ambient vertex type is finite, an admissible forest with a
maximum number of edges exists whenever the admissible family is nonempty. -/
theorem exists_edge_maximal_admissibleForest
    {F : SimpleGraph V} {X Y L : Finset V} {budget : ℕ}
    (hex : ∃ P, AdmissibleForest G F X Y L budget P) :
    ∃ P, AdmissibleForest G F X Y L budget P ∧
      ∀ Q, AdmissibleForest G F X Y L budget Q →
        Q.edgeSet.ncard ≤ P.edgeSet.ncard := by
  classical
  let C : Finset (SimpleGraph V) :=
    Finset.univ.filter (AdmissibleForest G F X Y L budget)
  have hC : C.Nonempty := by
    obtain ⟨P, hP⟩ := hex
    exact ⟨P, by simp [C, hP]⟩
  obtain ⟨P, hPC, hmax⟩ := C.exists_max_image
    (fun Q : SimpleGraph V ↦ Q.edgeSet.ncard) hC
  refine ⟨P, ?_, ?_⟩
  · simpa [C] using hPC
  · intro Q hQ
    exact hmax Q (by simp [C, hQ])

theorem ncard_edgeSet_eq_card_edgeFinset (P : SimpleGraph V) :
    P.edgeSet.ncard = P.edgeFinset.card := by
  rw [← P.coe_edgeFinset, Set.ncard_coe_finset]

theorem ncard_edgeSet_sup_edge {P : SimpleGraph V} {u v : V}
    (hn : ¬P.Adj u v) (hne : u ≠ v) :
    (P ⊔ SimpleGraph.edge u v).edgeSet.ncard = P.edgeSet.ncard + 1 := by
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne hne]
  have hedge : s(u, v) ∉ P.edgeSet := by
    simpa only [SimpleGraph.mem_edgeSet] using hn
  rw [Set.union_singleton, Set.ncard_insert_of_notMem hedge]

/-- The support after adjoining a two-edge connector uses at most its one
fresh middle vertex in addition to the old support. -/
theorem support_sup_two_edge_subset
    {P : SimpleGraph V} {u v w : V} (hu : u ∈ P.support)
    (hv : v ∈ P.support) :
    ((P ⊔ SimpleGraph.edge u w) ⊔ SimpleGraph.edge w v).support ⊆
      P.support ∪ {w} := by
  intro x hx
  obtain ⟨y, hxy⟩ := (SimpleGraph.mem_support _).mp hx
  rcases (SimpleGraph.sup_adj (P ⊔ SimpleGraph.edge u w)
      (SimpleGraph.edge w v) x y).mp hxy with hxy1 | hxy2
  · rcases (SimpleGraph.sup_adj P (SimpleGraph.edge u w) x y).mp hxy1 with hxyP | hxye
    · exact Or.inl hxyP.mem_support_left
    · simp only [SimpleGraph.edge_adj] at hxye
      rcases hxye.1 with h | h
      · exact h.1 ▸ Or.inl hu
      · exact h.1 ▸ Or.inr rfl
  · simp only [SimpleGraph.edge_adj] at hxy2
    rcases hxy2.1 with h | h
    · exact h.1 ▸ Or.inr rfl
    · exact h.1 ▸ Or.inl hv

/-- A fresh two-edge connector between distinct components preserves the
linear-forest property. -/
theorem LinearForest.sup_two_edge_connector
    {P : SimpleGraph V} (hP : LinearForest P) {u v w : V}
    (hu : u ∈ P.support) (hv : v ∈ P.support) (hw : w ∉ P.support)
    (huv : ¬ P.Reachable u v)
    (hdu : (P.neighborSet u).ncard ≤ 1)
    (hdv : (P.neighborSet v).ncard ≤ 1) :
    LinearForest ((P ⊔ SimpleGraph.edge u w) ⊔ SimpleGraph.edge w v) := by
  have huw : ¬ P.Reachable u w := by
    intro h
    have huwne : u ≠ w := fun huw ↦ hw (huw ▸ hu)
    exact hw (SimpleGraph.mem_support_of_reachable huwne.symm h.symm)
  have hdu' : P.degree u ≤ 1 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    exact hdu
  have hdv' : P.degree v ≤ 1 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    exact hdv
  have hdw0 : P.degree w = 0 :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support P w).mpr hw
  let P1 := P ⊔ SimpleGraph.edge u w
  have hP1 : LinearForest P1 := by
    simpa only [P1] using hP.sup_edge_of_not_reachable huw hdu' (by omega)
  have hvw1 : ¬ P1.Reachable v w := by
    simpa only [P1] using not_reachable_sup_edge_fresh hv hu hw
      (fun h ↦ huv h.symm)
  have hdw1 : P1.degree w ≤ 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_sup]
    calc
      (P.neighborFinset w ∪ (SimpleGraph.edge u w).neighborFinset w).card
          ≤ P.degree w + (SimpleGraph.edge u w).degree w := by
            simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
              Finset.card_union_le (P.neighborFinset w)
                ((SimpleGraph.edge u w).neighborFinset w)
      _ ≤ 1 := by
        have hedge : (SimpleGraph.edge u w).degree w ≤ 1 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          apply Finset.card_le_one.mpr
          intro a ha b hb
          simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj] at ha hb
          grind
        omega
  have hvu : v ≠ u := by
    intro h
    subst v
    exact huv (SimpleGraph.Reachable.refl u)
  have hvw : v ≠ w := fun h ↦ hw (h ▸ hv)
  have hdv1 : P1.degree v ≤ 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_sup]
    have hedge : (SimpleGraph.edge u w).neighborFinset v = ∅ := by
      ext z
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj,
        Finset.notMem_empty, iff_false]
      grind
    rw [hedge, Finset.union_empty, SimpleGraph.card_neighborFinset_eq_degree]
    exact hdv'
  have hdvN : (P1.neighborSet v).ncard ≤ 1 := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    exact hdv1
  have hdwN : (P1.neighborSet w).ncard ≤ 1 := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    exact hdw1
  have hres : LinearForest (P1 ⊔ SimpleGraph.edge v w) :=
    hP1.sup_edge_of_not_reachable hvw1 (by
      rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
      exact hdvN) (by
      rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
      exact hdwN)
  simpa only [P1, SimpleGraph.edge_comm v w] using hres

/-- Adding a fresh two-edge crossing connector between two components
preserves admissibility and raises the edge count by exactly two. -/
theorem AdmissibleForest.sup_two_edge_connector
    {F P : SimpleGraph V} {X Y L : Finset V} {budget : ℕ}
    (hP : AdmissibleForest G F X Y L budget P) {u v w : V}
    (hu : u ∈ P.support) (hv : v ∈ P.support)
    (hdu : (P.neighborSet u).ncard ≤ 1)
    (hdv : (P.neighborSet v).ncard ≤ 1)
    (huv : ¬P.Reachable u v) (hw : w ∉ P.support)
    (huw : G.Adj u w) (hvw : G.Adj w v)
    (huwCut : (u ∈ X ∧ w ∈ Y) ∨ (u ∈ Y ∧ w ∈ X))
    (hwvCut : (w ∈ X ∧ v ∈ Y) ∨ (w ∈ Y ∧ v ∈ X)) :
    let H := (P ⊔ SimpleGraph.edge u w) ⊔ SimpleGraph.edge w v
    AdmissibleForest G F X Y L budget H ∧
      H.edgeSet.ncard = P.edgeSet.ncard + 2 := by
  let P1 := P ⊔ SimpleGraph.edge u w
  let H := P1 ⊔ SimpleGraph.edge w v
  have huwP : ¬P.Adj u w := fun h ↦ hw h.mem_support_right
  have huwne : u ≠ w := fun h ↦ hw (h ▸ hu)
  have hvwne : v ≠ w := fun h ↦ hw (h ▸ hv)
  have huvne : u ≠ v := by
    intro h
    subst v
    exact huv (SimpleGraph.Reachable.refl u)
  have hvw1 : ¬P1.Reachable v w := by
    simpa only [P1] using not_reachable_sup_edge_fresh hv hu hw
      (fun h ↦ huv h.symm)
  have hwvP1 : ¬P1.Adj w v := fun h ↦ hvw1 h.symm.reachable
  have hP1card : P1.edgeSet.ncard = P.edgeSet.ncard + 1 := by
    simpa only [P1] using ncard_edgeSet_sup_edge huwP huwne
  have hHcard : H.edgeSet.ncard = P1.edgeSet.ncard + 1 := by
    simpa only [H] using ncard_edgeSet_sup_edge hwvP1 hvwne.symm
  have hedgeN : H.edgeSet.ncard = P.edgeSet.ncard + 2 := by
    omega
  have hlinH : LinearForest H := by
    simpa only [H, P1] using LinearForest.sup_two_edge_connector hP.linearForest
      hu hv hw huv hdu hdv
  have hPH : P ≤ H := le_trans le_sup_left le_sup_left
  have hHG : H ≤ G := by
    apply sup_le
    · exact sup_le hP.2.1 ((SimpleGraph.edge_le_iff G).2 (Or.inr huw))
    · exact (SimpleGraph.edge_le_iff G).2 (Or.inr hvw)
  have hsuppSub : H.support ⊆ P.support ∪ {w} := by
    simpa only [H, P1] using support_sup_two_edge_subset hu hv
  have hsuppN : H.support.ncard ≤ P.support.ncard + 1 := by
    have hle := Set.ncard_le_ncard hsuppSub
    have huN := Set.ncard_union_le P.support ({w} : Set V)
    simp only [Set.ncard_singleton] at huN
    omega
  refine ⟨?_, hedgeN⟩
  refine ⟨hP.1.trans hPH, hHG, hlinH, ?_, ?_, ?_, ?_⟩
  · exact hP.2.2.2.1.trans (SimpleGraph.support_mono hPH)
  · intro x hxH hdxH hxL
    by_cases hxP : x ∈ P.support
    · apply hP.2.2.2.2.1 x hxP
      have hsub : P.neighborSet x ⊆ H.neighborSet x := by
        intro z hxz
        exact hPH hxz
      exact (Set.ncard_le_ncard hsub).trans hdxH
      exact hxL
    · have hxw : x = w := by
        have := hsuppSub hxH
        rcases this with hx | hx
        · exact (hxP hx).elim
        · simpa only [Set.mem_singleton_iff] using hx
      have huH : H.Adj w u := by
        apply (SimpleGraph.sup_adj P1 (SimpleGraph.edge w v) w u).mpr
        left
        apply (SimpleGraph.sup_adj P (SimpleGraph.edge u w) w u).mpr
        exact Or.inr (by
          simp [SimpleGraph.edge_adj, huwne, Ne.symm huwne])
      have hvH : H.Adj w v := by
        apply (SimpleGraph.sup_adj P1 (SimpleGraph.edge w v) w v).mpr
        exact Or.inr (by
          simp [SimpleGraph.edge_adj, hvwne, Ne.symm hvwne])
      have hpair : ({u, v} : Set V) ⊆ H.neighborSet w := by
        simpa only [Set.insert_subset_iff, Set.singleton_subset_iff,
          SimpleGraph.mem_neighborSet] using And.intro huH hvH
      have htwo : ({u, v} : Set V).ncard = 2 := by
        simp [huvne]
      have := Set.ncard_le_ncard hpair
      rw [hxw] at hdxH
      change (H.neighborSet w).ncard ≤ 1 at hdxH
      omega
  · intro a b hab
    rcases (SimpleGraph.sup_adj P1 (SimpleGraph.edge w v) a b).mp hab with hab1 | hab2
    · rcases (SimpleGraph.sup_adj P (SimpleGraph.edge u w) a b).mp hab1 with habP | habE
      · exact hP.2.2.2.2.2.1 habP
      · right
        simp only [SimpleGraph.edge_adj] at habE
        rcases habE.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact huwCut
        · exact huwCut.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
            (fun h ↦ Or.inl ⟨h.2, h.1⟩)
    · right
      simp only [SimpleGraph.edge_adj] at hab2
      rcases hab2.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hwvCut
      · exact hwvCut.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
          (fun h ↦ Or.inl ⟨h.2, h.1⟩)
  · have hres := hP.2.2.2.2.2.2
    change 3 * H.support.ncard ≤ budget + 2 * H.edgeSet.ncard
    omega

/-- The support of a three-edge connector uses only its two new internal
vertices in addition to the old support. -/
theorem support_sup_three_edge_subset
    {P : SimpleGraph V} {u v w z : V} (hu : u ∈ P.support)
    (hv : v ∈ P.support) :
    (((P ⊔ SimpleGraph.edge u w) ⊔ SimpleGraph.edge w z) ⊔
      SimpleGraph.edge z v).support ⊆ P.support ∪ ({w, z} : Set V) := by
  intro x hx
  obtain ⟨y, hxy⟩ := (SimpleGraph.mem_support _).mp hx
  rcases (SimpleGraph.sup_adj
      ((P ⊔ SimpleGraph.edge u w) ⊔ SimpleGraph.edge w z)
      (SimpleGraph.edge z v) x y).mp hxy with hxy2 | hxy3
  · rcases (SimpleGraph.sup_adj (P ⊔ SimpleGraph.edge u w)
      (SimpleGraph.edge w z) x y).mp hxy2 with hxy1 | hxye2
    · rcases (SimpleGraph.sup_adj P (SimpleGraph.edge u w) x y).mp hxy1 with
        hxyP | hxye1
      · exact Or.inl hxyP.mem_support_left
      · simp only [SimpleGraph.edge_adj] at hxye1
        rcases hxye1.1 with h | h
        · exact h.1 ▸ Or.inl hu
        · exact h.1 ▸ Or.inr (by simp)
    · simp only [SimpleGraph.edge_adj] at hxye2
      rcases hxye2.1 with h | h
      · exact h.1 ▸ Or.inr (by simp)
      · exact h.1 ▸ Or.inr (by simp)
  · simp only [SimpleGraph.edge_adj] at hxy3
    rcases hxy3.1 with h | h
    · exact h.1 ▸ Or.inr (by simp)
    · exact h.1 ▸ Or.inl hv

/-- Joining two different components of a linear forest by a fresh
three-edge path preserves the linear-forest property. -/
theorem LinearForest.sup_three_edge_connector
    {P : SimpleGraph V} (hP : LinearForest P) {u v w z : V}
    (hu : u ∈ P.support) (hv : v ∈ P.support)
    (hw : w ∉ P.support) (hz : z ∉ P.support) (hwz : w ≠ z)
    (huv : ¬ P.Reachable u v)
    (hdu : (P.neighborSet u).ncard ≤ 1)
    (hdv : (P.neighborSet v).ncard ≤ 1) :
    LinearForest (((P ⊔ SimpleGraph.edge u w) ⊔
      SimpleGraph.edge w z) ⊔ SimpleGraph.edge z v) := by
  let P1 := P ⊔ SimpleGraph.edge u w
  have huwne : u ≠ w := fun h ↦ hw (h ▸ hu)
  have huwReach : ¬P.Reachable u w := by
    intro h
    exact hw (SimpleGraph.mem_support_of_reachable huwne.symm h.symm)
  have hdu' : P.degree u ≤ 1 := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    exact hdu
  have hdw0 : P.degree w = 0 :=
    (SimpleGraph.degree_eq_zero_iff_notMem_support P w).mpr hw
  have hP1 : LinearForest P1 := by
    simpa only [P1] using hP.sup_edge_of_not_reachable huwReach hdu' (by omega)
  have hwP1 : w ∈ P1.support := by
    apply SimpleGraph.Adj.mem_support_right
    apply (SimpleGraph.sup_adj P (SimpleGraph.edge u w) u w).mpr
    exact Or.inr (by simp [SimpleGraph.edge_adj, huwne])
  have hvP1 : v ∈ P1.support :=
    SimpleGraph.support_mono le_sup_left hv
  have hzP1 : z ∉ P1.support := by
    intro hz'
    obtain ⟨a, hza⟩ := (SimpleGraph.mem_support P1).mp hz'
    rcases (SimpleGraph.sup_adj P (SimpleGraph.edge u w) z a).mp hza with
      hzaP | hzaE
    · exact hz hzaP.mem_support_left
    · simp only [SimpleGraph.edge_adj] at hzaE
      rcases hzaE.1 with h | h
      · exact hz (h.1 ▸ hu)
      · exact hwz (h.1.symm)
  have hvw1 : ¬P1.Reachable v w := by
    simpa only [P1] using not_reachable_sup_edge_fresh hv hu hw
      (fun h ↦ huv h.symm)
  have hwv1 : ¬P1.Reachable w v := fun h ↦ hvw1 h.symm
  have hdw1 : (P1.neighborSet w).ncard ≤ 1 := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_sup]
    calc
      (P.neighborFinset w ∪
          (SimpleGraph.edge u w).neighborFinset w).card
          ≤ P.degree w + (SimpleGraph.edge u w).degree w := by
            simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
              Finset.card_union_le (P.neighborFinset w)
                ((SimpleGraph.edge u w).neighborFinset w)
      _ ≤ 1 := by
        have hedge : (SimpleGraph.edge u w).degree w ≤ 1 := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          apply Finset.card_le_one.mpr
          intro a ha b hb
          simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj] at ha hb
          grind
        omega
  have hvu : v ≠ u := by
    intro h
    subst v
    exact huv (SimpleGraph.Reachable.refl u)
  have hvw : v ≠ w := fun h ↦ hw (h ▸ hv)
  have hdv1 : (P1.neighborSet v).ncard ≤ 1 := by
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_sup]
    have hedge : (SimpleGraph.edge u w).neighborFinset v = ∅ := by
      ext a
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj,
        Finset.notMem_empty, iff_false]
      grind
    rw [hedge, Finset.union_empty, SimpleGraph.card_neighborFinset_eq_degree]
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    exact hdv
  have hres := LinearForest.sup_two_edge_connector hP1 hwP1 hvP1 hzP1
    hwv1 hdw1 hdv1
  simpa only [P1] using hres

/-- Adding a fresh three-edge crossing connector between two components
preserves admissibility and raises the edge count by exactly three. -/
theorem AdmissibleForest.sup_three_edge_connector
    {F P : SimpleGraph V} {X Y L : Finset V} {budget : ℕ}
    (hP : AdmissibleForest G F X Y L budget P) {u v w z : V}
    (hu : u ∈ P.support) (hv : v ∈ P.support)
    (hdu : (P.neighborSet u).ncard ≤ 1)
    (hdv : (P.neighborSet v).ncard ≤ 1)
    (huv : ¬P.Reachable u v)
    (hw : w ∉ P.support) (hz : z ∉ P.support) (hwz : w ≠ z)
    (huw : G.Adj u w) (hwzG : G.Adj w z) (hzv : G.Adj z v)
    (huwCut : (u ∈ X ∧ w ∈ Y) ∨ (u ∈ Y ∧ w ∈ X))
    (hwzCut : (w ∈ X ∧ z ∈ Y) ∨ (w ∈ Y ∧ z ∈ X))
    (hzvCut : (z ∈ X ∧ v ∈ Y) ∨ (z ∈ Y ∧ v ∈ X)) :
    let H := (((P ⊔ SimpleGraph.edge u w) ⊔
      SimpleGraph.edge w z) ⊔ SimpleGraph.edge z v)
    AdmissibleForest G F X Y L budget H ∧
      H.edgeSet.ncard = P.edgeSet.ncard + 3 := by
  let P1 := P ⊔ SimpleGraph.edge u w
  let P2 := P1 ⊔ SimpleGraph.edge w z
  let H := P2 ⊔ SimpleGraph.edge z v
  have huwne : u ≠ w := fun h ↦ hw (h ▸ hu)
  have huzne : u ≠ z := fun h ↦ hz (h ▸ hu)
  have hvwne : v ≠ w := fun h ↦ hw (h ▸ hv)
  have hvzne : v ≠ z := fun h ↦ hz (h ▸ hv)
  have huvne : u ≠ v := by
    intro h
    subst v
    exact huv (SimpleGraph.Reachable.refl u)
  have huwP : ¬P.Adj u w := fun h ↦ hw h.mem_support_right
  have hwP1 : w ∈ P1.support := by
    apply SimpleGraph.Adj.mem_support_right
    apply (SimpleGraph.sup_adj P (SimpleGraph.edge u w) u w).mpr
    exact Or.inr (by simp [SimpleGraph.edge_adj, huwne])
  have hvP1 : v ∈ P1.support := SimpleGraph.support_mono le_sup_left hv
  have hzP1 : z ∉ P1.support := by
    intro hz'
    obtain ⟨a, hza⟩ := (SimpleGraph.mem_support P1).mp hz'
    rcases (SimpleGraph.sup_adj P (SimpleGraph.edge u w) z a).mp hza with
      hzaP | hzaE
    · exact hz hzaP.mem_support_left
    · simp only [SimpleGraph.edge_adj] at hzaE
      rcases hzaE.1 with h | h
      · exact hz (h.1 ▸ hu)
      · exact hwz h.1.symm
  have hwzP1 : ¬P1.Adj w z := fun h ↦ hzP1 h.mem_support_right
  have hvw1 : ¬P1.Reachable v w := by
    simpa only [P1] using not_reachable_sup_edge_fresh hv hu hw
      (fun h ↦ huv h.symm)
  have hvz2 : ¬P2.Reachable v z := by
    simpa only [P2] using not_reachable_sup_edge_fresh hvP1 hwP1 hzP1 hvw1
  have hzvP2 : ¬P2.Adj z v := fun h ↦ hvz2 h.symm.reachable
  have hP1card : P1.edgeSet.ncard = P.edgeSet.ncard + 1 := by
    simpa only [P1] using ncard_edgeSet_sup_edge huwP huwne
  have hP2card : P2.edgeSet.ncard = P1.edgeSet.ncard + 1 := by
    simpa only [P2] using ncard_edgeSet_sup_edge hwzP1 hwz
  have hHcard : H.edgeSet.ncard = P2.edgeSet.ncard + 1 := by
    simpa only [H] using ncard_edgeSet_sup_edge hzvP2 hvzne.symm
  have hedgeN : H.edgeSet.ncard = P.edgeSet.ncard + 3 := by omega
  have hlinH : LinearForest H := by
    simpa only [H, P2, P1] using
      LinearForest.sup_three_edge_connector hP.linearForest hu hv hw hz hwz
        huv hdu hdv
  have hPH : P ≤ H := le_trans (le_trans le_sup_left le_sup_left) le_sup_left
  have hHG : H ≤ G := by
    apply sup_le
    · apply sup_le
      · exact sup_le hP.2.1 ((SimpleGraph.edge_le_iff G).2 (Or.inr huw))
      · exact (SimpleGraph.edge_le_iff G).2 (Or.inr hwzG)
    · exact (SimpleGraph.edge_le_iff G).2 (Or.inr hzv)
  have hsuppSub : H.support ⊆ P.support ∪ ({w, z} : Set V) := by
    simpa only [H, P2, P1] using support_sup_three_edge_subset hu hv
  have hsuppN : H.support.ncard ≤ P.support.ncard + 2 := by
    have hle := Set.ncard_le_ncard hsuppSub
    have huN := Set.ncard_union_le P.support ({w, z} : Set V)
    have hpair : ({w, z} : Set V).ncard = 2 := by simp [hwz]
    omega
  refine ⟨?_, hedgeN⟩
  refine ⟨hP.1.trans hPH, hHG, hlinH, ?_, ?_, ?_, ?_⟩
  · exact hP.2.2.2.1.trans (SimpleGraph.support_mono hPH)
  · intro x hxH hdxH hxL
    by_cases hxP : x ∈ P.support
    · apply hP.2.2.2.2.1 x hxP
      have hsub : P.neighborSet x ⊆ H.neighborSet x := by
        intro a hxa
        exact hPH hxa
      exact (Set.ncard_le_ncard hsub).trans hdxH
      exact hxL
    · have hxnew : x = w ∨ x = z := by
        have hx := hsuppSub hxH
        rcases hx with hx | hx
        · exact (hxP hx).elim
        · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
      rcases hxnew with hxw | hxz
      · have hwu : H.Adj w u := by
          apply (SimpleGraph.sup_adj P2 (SimpleGraph.edge z v) w u).mpr
          left
          apply (SimpleGraph.sup_adj P1 (SimpleGraph.edge w z) w u).mpr
          left
          apply (SimpleGraph.sup_adj P (SimpleGraph.edge u w) w u).mpr
          exact Or.inr (by simp [SimpleGraph.edge_adj, huwne, huwne.symm])
        have hwzH : H.Adj w z := by
          apply (SimpleGraph.sup_adj P2 (SimpleGraph.edge z v) w z).mpr
          left
          apply (SimpleGraph.sup_adj P1 (SimpleGraph.edge w z) w z).mpr
          exact Or.inr (by simp [SimpleGraph.edge_adj, hwz])
        have hpair : ({u, z} : Set V) ⊆ H.neighborSet w := by
          simpa only [Set.insert_subset_iff, Set.singleton_subset_iff,
            SimpleGraph.mem_neighborSet] using And.intro hwu hwzH
        have htwo : ({u, z} : Set V).ncard = 2 := by simp [huzne]
        have := Set.ncard_le_ncard hpair
        rw [hxw] at hdxH
        change (H.neighborSet w).ncard ≤ 1 at hdxH
        omega
      · have hzw : H.Adj z w := by
          apply (SimpleGraph.sup_adj P2 (SimpleGraph.edge z v) z w).mpr
          left
          apply (SimpleGraph.sup_adj P1 (SimpleGraph.edge w z) z w).mpr
          exact Or.inr (by simp [SimpleGraph.edge_adj, hwz, hwz.symm])
        have hzvH : H.Adj z v := by
          apply (SimpleGraph.sup_adj P2 (SimpleGraph.edge z v) z v).mpr
          exact Or.inr (by simp [SimpleGraph.edge_adj, hvzne, hvzne.symm])
        have hpair : ({w, v} : Set V) ⊆ H.neighborSet z := by
          simpa only [Set.insert_subset_iff, Set.singleton_subset_iff,
            SimpleGraph.mem_neighborSet] using And.intro hzw hzvH
        have htwo : ({w, v} : Set V).ncard = 2 := by simp [hvwne.symm]
        have := Set.ncard_le_ncard hpair
        rw [hxz] at hdxH
        change (H.neighborSet z).ncard ≤ 1 at hdxH
        omega
  · intro a b hab
    rcases (SimpleGraph.sup_adj P2 (SimpleGraph.edge z v) a b).mp hab with
      hab2 | hab3
    · rcases (SimpleGraph.sup_adj P1 (SimpleGraph.edge w z) a b).mp hab2 with
        hab1 | habE2
      · rcases (SimpleGraph.sup_adj P (SimpleGraph.edge u w) a b).mp hab1 with
          habP | habE1
        · exact hP.2.2.2.2.2.1 habP
        · right
          simp only [SimpleGraph.edge_adj] at habE1
          rcases habE1.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact huwCut
          · exact huwCut.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
              (fun h ↦ Or.inl ⟨h.2, h.1⟩)
      · right
        simp only [SimpleGraph.edge_adj] at habE2
        rcases habE2.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hwzCut
        · exact hwzCut.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
            (fun h ↦ Or.inl ⟨h.2, h.1⟩)
    · right
      simp only [SimpleGraph.edge_adj] at hab3
      rcases hab3.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hzvCut
      · exact hzvCut.elim (fun h ↦ Or.inr ⟨h.2, h.1⟩)
          (fun h ↦ Or.inl ⟨h.2, h.1⟩)
  · have hres := hP.2.2.2.2.2.2
    change 3 * H.support.ncard ≤ budget + 2 * H.edgeSet.ncard
    omega

/-- Deficiency of the crossing-edge count from the complete bipartite
rectangle controls the number of vertices of crossing degree at most `d`.
This is the exact counting estimate used to show that the low-crossing-degree
set in the DKM absorbing argument is small. -/
theorem card_lowCrossSet_mul_gap_le_deficiency
    (G : SimpleGraph V) (X Y : Finset V) (d : ℝ) :
    ((lowCrossSet G X Y d).card : ℝ) * ((Y.card : ℝ) - d) ≤
      (X.card : ℝ) * Y.card - edgeCount G X Y := by
  let L := lowCrossSet G X Y d
  let R := X \ L
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    exact (Finset.mem_sdiff.mp hvR).2 hvL
  have hunion : L ∪ R = X := by
    exact Finset.union_sdiff_of_subset (lowCrossSet_subset G X Y d)
  have hL : ∀ v ∈ L, degreeInto G v Y ≤ d := by
    intro v hv
    exact (mem_lowCrossSet.mp hv).2
  have hR : ∀ v ∈ R, degreeInto G v Y ≤ (Y.card : ℝ) := by
    intro v hv
    exact degreeInto_le_card G v Y
  have hupp := edgeCount_le_of_partition hdisj hunion hL hR
  have hcards : L.card + R.card = X.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hcardsReal : (L.card : ℝ) + R.card = X.card := by
    exact_mod_cast hcards
  dsimp [L, R] at hupp hcardsReal ⊢
  nlinarith

/-- Strict numerical form of `card_lowCrossSet_mul_gap_le_deficiency`. -/
theorem card_lowCrossSet_lt_of_deficiency_lt
    (G : SimpleGraph V) (X Y : Finset V) {d K : ℝ}
    (hgap : 0 < (Y.card : ℝ) - d)
    (hdef : (X.card : ℝ) * Y.card - edgeCount G X Y <
      K * ((Y.card : ℝ) - d)) :
    ((lowCrossSet G X Y d).card : ℝ) < K := by
  have h := card_lowCrossSet_mul_gap_le_deficiency G X Y d
  nlinarith

/-- The numerical specialization used by DKM: near-half parts and a crossing
graph missing few edges have few vertices of crossing degree at most
`3 N / 10`.  All rounding and hierarchy requirements are exposed in the
single final scalar inequality. -/
theorem card_lowCrossSet_three_tenths_lt
    (G : SimpleGraph V) (X Y : Finset V) {N delta eps K : ℝ}
    (hN : 0 ≤ N) (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (hXupper : (X.card : ℝ) ≤ N / 2 + delta)
    (hYlower : N / 2 - delta ≤ (Y.card : ℝ))
    (hYupper : (Y.card : ℝ) ≤ N / 2 + delta)
    (hdense : N ^ 2 / 4 - eps * N ^ 2 ≤ edgeCount G X Y)
    (hgap : 0 < N / 5 - delta)
    (hnumeric : delta * N + delta ^ 2 + eps * N ^ 2 <
      K * (N / 5 - delta)) :
    ((lowCrossSet G X Y (3 * N / 10)).card : ℝ) < K := by
  apply card_lowCrossSet_lt_of_deficiency_lt G X Y
  · nlinarith
  · have hXY : (X.card : ℝ) * Y.card ≤ (N / 2 + delta) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ X.card by positivity,
        show (0 : ℝ) ≤ Y.card by positivity]
    have hdef : (X.card : ℝ) * Y.card - edgeCount G X Y ≤
        delta * N + delta ^ 2 + eps * N ^ 2 := by
      nlinarith
    nlinarith

/-- The spanning bipartite subgraph consisting of the edges of `G` which
cross the ordered cut `(X,Y)`. -/
def crossingSubgraph (G : SimpleGraph V) (X Y : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧
    ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X))
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.elim
      (fun huv ↦ Or.inr ⟨huv.2, huv.1⟩)
      (fun huv ↦ Or.inl ⟨huv.2, huv.1⟩)⟩
  loopless := by
    constructor
    intro u h
    exact G.loopless.irrefl u h.1

noncomputable instance crossingSubgraph.instDecidableRel
    (G : SimpleGraph V) [DecidableRel G.Adj] (X Y : Finset V) :
    DecidableRel (crossingSubgraph G X Y).Adj :=
  Classical.decRel _

@[simp]
theorem crossingSubgraph_adj {X Y : Finset V} {u v : V} :
    (crossingSubgraph G X Y).Adj u v ↔ G.Adj u v ∧
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)) :=
  Iff.rfl

theorem crossingSubgraph_le (G : SimpleGraph V) (X Y : Finset V) :
    crossingSubgraph G X Y ≤ G := by
  intro u v huv
  exact huv.1

/-- The crossing subgraph is bipartite with the two sides of a cut. -/
theorem crossingSubgraph_isBipartiteWith {X Y : Finset V}
    (hcut : IsCut X Y) :
    (crossingSubgraph G X Y).IsBipartiteWith (X : Set V) (Y : Set V) := by
  refine ⟨by simpa using hcut.1, ?_⟩
  intro u v huv
  exact huv.2

/-- Vertices of `X` retained in the finite subtype cut out by `R`. -/
def restrictedPart (R X : Finset V) : Finset (R : Set V) :=
  R.attach.filter fun v ↦ v.1 ∈ X

@[simp]
theorem mem_restrictedPart {R X : Finset V} {v : (R : Set V)} :
    v ∈ restrictedPart R X ↔ v.1 ∈ X := by
  simp [restrictedPart]

/-- Restricting a cut to an arbitrary set of retained vertices gives a cut
of the subtype of retained vertices. -/
theorem restrictedParts_isCut {X Y R : Finset V} (hcut : IsCut X Y) :
    IsCut (restrictedPart R X) (restrictedPart R Y) := by
  constructor
  · rw [Finset.disjoint_left]
    intro v hvX hvY
    exact Finset.disjoint_left.mp hcut.1
      (mem_restrictedPart.mp hvX) (mem_restrictedPart.mp hvY)
  · ext v
    simp only [Finset.mem_union, mem_restrictedPart, Finset.mem_univ, iff_true]
    have hv : v.1 ∈ X ∪ Y := by rw [hcut.2]; simp
    simpa only [Finset.mem_union] using hv

/-- The crossing graph induced by retained vertices is bipartite with the
restricted parts. -/
theorem induce_crossingSubgraph_isBipartiteWith
    {X Y R : Finset V} (hcut : IsCut X Y) :
    ((crossingSubgraph G X Y).induce (R : Set V)).IsBipartiteWith
      (restrictedPart R X : Set (R : Set V))
      (restrictedPart R Y : Set (R : Set V)) := by
  refine ⟨by simpa using (restrictedParts_isCut hcut).1, ?_⟩
  intro u v huv
  rcases (SimpleGraph.induce_adj.mp huv).2 with huvXY | huvYX
  · exact Or.inl ⟨mem_restrictedPart.mpr huvXY.1,
      mem_restrictedPart.mpr huvXY.2⟩
  · exact Or.inr ⟨mem_restrictedPart.mpr huvYX.1,
      mem_restrictedPart.mpr huvYX.2⟩

/-- The interior vertices of a path: both endpoints are deliberately
excluded. -/
def pathInterior {a b : V} (p : G.Walk a b) : Finset V :=
  p.support.tail.dropLast.toFinset

/-- The vertices retained after deleting the interior of an absorbing path. -/
def pathRemainder {a b : V} (p : G.Walk a b) : Finset V :=
  Finset.univ \ pathInterior p

@[simp]
theorem mem_pathRemainder {a b v : V} {p : G.Walk a b} :
    v ∈ pathRemainder p ↔ v ∉ pathInterior p := by
  simp [pathRemainder]

theorem start_mem_pathRemainder {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) : a ∈ pathRemainder p := by
  rw [mem_pathRemainder]
  simp only [pathInterior, List.mem_toFinset, not_false_eq_true]
  intro ha
  have haTail : a ∈ p.support.tail :=
    List.dropLast_subset p.support.tail ha
  have hn := hp.support_nodup
  rw [SimpleGraph.Walk.support_eq_cons] at hn
  exact (List.nodup_cons.mp hn).1 haTail

theorem end_mem_pathRemainder {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) : b ∈ pathRemainder p := by
  rw [mem_pathRemainder]
  simp only [pathInterior, List.mem_toFinset, not_false_eq_true]
  intro hb
  have hbDrop : b ∈ p.support.dropLast := by
    -- `tail.dropLast` is contained in `support.dropLast`.
    cases hs : p.support with
    | nil => simp at hs
    | cons c l =>
        simp only [hs, List.tail_cons] at hb
        cases l with
        | nil => simp at hb
        | cons d l =>
            rw [List.dropLast_cons_cons]
            exact List.mem_cons_of_mem c hb
  have hn := hp.support_nodup
  rw [SimpleGraph.Walk.support_eq_concat, List.nodup_concat] at hn
  exact hn.1 hbDrop

theorem mem_pathInterior_of_mem_support_of_ne_endpoints
    {a b v : V} {p : G.Walk a b} (hp : p.IsPath)
    (hv : v ∈ p.support) (hva : v ≠ a) (hvb : v ≠ b) :
    v ∈ pathInterior p := by
  simp only [pathInterior, List.mem_toFinset]
  have hvDrop : v ∈ p.support.dropLast := by
    apply List.mem_dropLast_of_mem_of_ne_getLast hv
    simpa using hvb
  cases hs : p.support with
  | nil => simp at hs
  | cons c l =>
      have hca : c = a := by
        have hcons := p.cons_tail_support
        rw [hs] at hcons
        exact (List.cons.inj hcons).1.symm
      subst c
      simp only [hs, List.tail_cons]
      cases l with
      | nil =>
          rw [hs] at hvDrop
          simp at hvDrop
      | cons d l =>
          rw [hs, List.dropLast_cons_cons, List.mem_cons] at hvDrop
          exact hvDrop.resolve_left hva

/-- A simple absorbing path meets its remainder exactly at its two
endpoints. -/
theorem support_inter_pathRemainder {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) (hab : a ≠ b) :
    p.support.toFinset ∩ pathRemainder p = {a, b} := by
  ext v
  simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hvp, hvR⟩
    by_cases hva : v = a
    · exact Or.inl hva
    by_cases hvb : v = b
    · exact Or.inr hvb
    exact (mem_pathRemainder.mp hvR
      (mem_pathInterior_of_mem_support_of_ne_endpoints hp hvp hva hvb)).elim
  · intro hv
    rcases hv with rfl | rfl
    · exact ⟨p.start_mem_support, start_mem_pathRemainder hp⟩
    · exact ⟨p.end_mem_support, end_mem_pathRemainder hp⟩

/-- The path together with the vertices left after deleting its interior
covers the ambient type. -/
theorem support_union_pathRemainder {a b : V} (p : G.Walk a b) :
    p.support.toFinset ∪ pathRemainder p = Finset.univ := by
  ext v
  simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_univ, iff_true]
  by_cases hv : v ∈ p.support
  · exact Or.inl hv
  · right
    rw [mem_pathRemainder]
    intro hvInterior
    apply hv
    exact List.mem_of_mem_tail
      (List.dropLast_subset _ (List.mem_toFinset.mp hvInterior))

/-- Two paths with the same endpoints, no other common vertex, and whose
supports cover the ambient finite type close to a Hamilton cycle.  This is
the exact walk-level gluing operation needed after the absorbing path has
been removed and the balanced bipartite remainder has been traversed. -/
theorem isHamiltonianCycle_append_reverse_of_complementary_paths
    {a b : V} {p q : G.Walk a b} (hab : a ≠ b)
    (hV : 3 ≤ Fintype.card V)
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : p.support.toFinset ∩ q.support.toFinset = {a, b})
    (hcover : p.support.toFinset ∪ q.support.toFinset = Finset.univ) :
    (p.append q.reverse).IsHamiltonianCycle := by
  have haNotP : a ∉ p.support.tail := by
    have hn := hp.support_nodup
    rw [SimpleGraph.Walk.support_eq_cons] at hn
    exact (List.nodup_cons.mp hn).1
  have hbNotQrev : b ∉ q.reverse.support.tail := by
    have hn := hq.reverse.support_nodup
    rw [SimpleGraph.Walk.support_eq_cons] at hn
    exact (List.nodup_cons.mp hn).1
  have hdisj : p.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro v hvp hvq
    have hvp' : v ∈ p.support.toFinset := by
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail hvp)
    have hvq' : v ∈ q.support.toFinset := by
      exact List.mem_toFinset.mpr (by
        have : v ∈ q.reverse.support := List.mem_of_mem_tail hvq
        simpa using this)
    have hvab : v ∈ ({a, b} : Finset V) := by
      rw [← hinter]
      exact Finset.mem_inter.mpr ⟨hvp', hvq'⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvab
    rcases hvab with rfl | rfl
    · exact haNotP hvp
    · exact hbNotQrev hvq
  have hpCard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup,
      SimpleGraph.Walk.length_support]
  have hqCard : q.support.toFinset.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup hq.support_nodup,
      SimpleGraph.Walk.length_support]
  have hinterCard :
      (p.support.toFinset ∩ q.support.toFinset).card = 2 := by
    rw [hinter, Finset.card_pair hab]
  have hcoverCard :
      (p.support.toFinset ∪ q.support.toFinset).card = Fintype.card V := by
    rw [hcover, Finset.card_univ]
  have hcardIdentity := Finset.card_union_add_card_inter
    p.support.toFinset q.support.toFinset
  rw [hcoverCard, hinterCard, hpCard, hqCard] at hcardIdentity
  have hsum : p.length + q.length = Fintype.card V := by omega
  have hcycle : (p.append q.reverse).IsCycle := by
    apply hp.isCycle_append hq.reverse hdisj
    simpa only [SimpleGraph.Walk.length_reverse] using
      (show 1 < p.length ∨ 1 < q.length by omega)
  rw [SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨hcycle, ?_⟩
  simp only [SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse]
  exact hsum

/-- Once a short absorbing path has been constructed, balanced bipartite
Hamilton-connectivity of the remainder closes it to a Hamilton cycle.

The degree hypothesis is stated directly in the induced crossing graph on
the retained vertices.  In the DKM application it follows because every
vertex left outside the absorber has crossing degree above `3N/10`, while
the absorber deletes only `O(epsilon N)` vertices. -/
theorem isHamiltonian_of_absorbing_path
    {X Y : Finset V} (hcut : IsCut X Y)
    {a b : V} (ha : a ∈ X) (hb : b ∈ Y) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath)
    (hV : 3 ≤ Fintype.card V)
    (hbalance :
      (restrictedPart (pathRemainder p) X).card =
        (restrictedPart (pathRemainder p) Y).card)
    (hdegree : ∀ z : (pathRemainder p : Set V),
      (restrictedPart (pathRemainder p) X).card + 2 ≤
        2 * ((crossingSubgraph G X Y).induce
          (pathRemainder p : Set V)).degree z) :
    G.IsHamiltonian := by
  let R := pathRemainder p
  let H := (crossingSubgraph G X Y).induce (R : Set V)
  let A := restrictedPart R X
  let B := restrictedPart R Y
  have haR : a ∈ R := by
    simpa [R] using start_mem_pathRemainder hp
  have hbR : b ∈ R := by
    simpa [R] using end_mem_pathRemainder hp
  let aR : (R : Set V) := ⟨a, haR⟩
  let bR : (R : Set V) := ⟨b, hbR⟩
  have haA : aR ∈ A := by
    exact mem_restrictedPart.mpr ha
  have hbB : bR ∈ B := by
    exact mem_restrictedPart.mpr hb
  have hHBi : H.IsBipartiteWith (A : Set (R : Set V)) (B : Set (R : Set V)) := by
    simpa [H, A, B, R] using
      (induce_crossingSubgraph_isBipartiteWith (G := G) hcut)
  have hABcover : A ∪ B = Finset.univ := by
    simpa [A, B, R] using (restrictedParts_isCut (R := pathRemainder p) hcut).2
  have hABcard : A.card = B.card := by
    simpa [A, B, R] using hbalance
  have hHdegree : ∀ z : (R : Set V), A.card + 2 ≤ 2 * H.degree z := by
    simpa [H, A, R] using hdegree
  obtain ⟨q, hqPath, hqHam⟩ :=
    BipartiteHamilton.exists_hamiltonian_path_of_balanced_bipartite
      hHBi hABcover hABcard hHdegree haA hbB
  let eR : H →g crossingSubgraph G X Y :=
    (SimpleGraph.Embedding.induce (R : Set V)).toHom
  let eG : crossingSubgraph G X Y →g G :=
    SimpleGraph.Hom.ofLE (crossingSubgraph_le G X Y)
  let qG0 : G.Walk a b := ((q.map eR).map eG).copy rfl rfl
  have hqGPath : qG0.IsPath := by
    have hqR : (q.map eR).IsPath := by
      exact hqPath.map (SimpleGraph.Embedding.induce
        (G := crossingSubgraph G X Y) (R : Set V)).injective
    have hqG : ((q.map eR).map eG).IsPath := by
      exact hqR.map Function.injective_id
    change (((q.map eR).map eG).copy rfl rfl).IsPath
    rw [SimpleGraph.Walk.isPath_copy]
    exact hqG
  have hqGSupport : qG0.support.toFinset = R := by
    ext v
    constructor
    · intro hv
      have hvList : v ∈ qG0.support := List.mem_toFinset.mp hv
      change v ∈ (((q.map eR).map eG).copy rfl rfl).support at hvList
      simp only [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_map, List.mem_map] at hvList
      obtain ⟨w, hw, hwv⟩ := hvList
      obtain ⟨z, hz, hzw⟩ := hw
      change z.1 = w at hzw
      change w = v at hwv
      subst w
      subst v
      exact z.2
    · intro hv
      let z : (R : Set V) := ⟨v, hv⟩
      have hz : z ∈ q.support := hqHam.mem_support z
      apply List.mem_toFinset.mpr
      change v ∈ (((q.map eR).map eG).copy rfl rfl).support
      simp only [SimpleGraph.Walk.support_copy,
        SimpleGraph.Walk.support_map, List.mem_map]
      refine ⟨z.1, ?_, rfl⟩
      exact ⟨z, hz, rfl⟩
  have hinter : p.support.toFinset ∩ qG0.support.toFinset = {a, b} := by
    rw [hqGSupport]
    exact support_inter_pathRemainder hp hab
  have hcover : p.support.toFinset ∪ qG0.support.toFinset = Finset.univ := by
    rw [hqGSupport]
    exact support_union_pathRemainder p
  exact fun _ ↦ ⟨a, p.append qG0.reverse,
    isHamiltonianCycle_append_reverse_of_complementary_paths
      hab hV hp hqGPath hinter hcover⟩

theorem neighborFinset_crossingSubgraph_eq_crossNeighbors
    {X Y : Finset V} (hcut : IsCut X Y) (v : V) :
    (crossingSubgraph G X Y).neighborFinset v = crossNeighbors G X Y v := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, crossingSubgraph_adj,
    mem_crossNeighbors]
  by_cases hvX : v ∈ X
  · have hvY : v ∉ Y := (hcut.mem_left_iff v).mp hvX
    simp [hvX, hvY]
  · have hvY : v ∈ Y := (hcut.mem_right_iff v).mpr hvX
    simp [hvX, hvY]

theorem crossNeighbors_card_le_degree_induce_add_pathInterior
    {X Y : Finset V} (hcut : IsCut X Y)
    {a b : V} (p : G.Walk a b) (z : (pathRemainder p : Set V)) :
    (crossNeighbors G X Y z.1).card ≤
      ((crossingSubgraph G X Y).induce
        (pathRemainder p : Set V)).degree z + (pathInterior p).card := by
  let H := crossingSubgraph G X Y
  let C := H.neighborFinset z.1 ∩ pathRemainder p
  have hdeg : (H.induce (pathRemainder p : Set V)).degree z = C.card := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    calc
      ((H.induce (pathRemainder p : Set V)).neighborSet z).ncard =
          ((C : Finset V) : Set V).ncard := by
        apply Set.ncard_congr (fun q _ ↦ q.1)
        · intro q hq
          change H.Adj z.1 q.1 at hq
          change q.1 ∈ C
          exact Finset.mem_inter.mpr
            ⟨(H.mem_neighborFinset z.1 q.1).mpr hq, q.2⟩
        · intro q r _ _ h
          exact Subtype.ext h
        · intro w hw
          change w ∈ C at hw
          have hw' : H.Adj z.1 w ∧ w ∈ pathRemainder p := by
            simpa only [C, Finset.mem_inter, SimpleGraph.mem_neighborFinset] using hw
          let q : (pathRemainder p : Set V) := ⟨w, hw'.2⟩
          exact ⟨q, hw'.1, rfl⟩
      _ = C.card := Set.ncard_coe_finset C
  have hcross : H.neighborFinset z.1 = crossNeighbors G X Y z.1 :=
    neighborFinset_crossingSubgraph_eq_crossNeighbors hcut z.1
  have hR : crossNeighbors G X Y z.1 ∩ pathRemainder p =
      crossNeighbors G X Y z.1 \ pathInterior p := by
    ext w
    simp [pathRemainder]
  change (crossNeighbors G X Y z.1).card ≤
    (H.induce (pathRemainder p : Set V)).degree z + (pathInterior p).card
  rw [hdeg]
  change (crossNeighbors G X Y z.1).card ≤
    (H.neighborFinset z.1 ∩ pathRemainder p).card + (pathInterior p).card
  rw [hcross, hR]
  have hsplit := Finset.card_sdiff_add_card_inter
    (crossNeighbors G X Y z.1) (pathInterior p)
  have hinter : (crossNeighbors G X Y z.1 ∩ pathInterior p).card ≤
      (pathInterior p).card := Finset.card_le_card Finset.inter_subset_right
  omega

theorem exists_mem_crossNeighbors_not_mem_of_card_lt
    {X Y Z : Finset V} {v : V}
    (hcard : Z.card < (crossNeighbors G X Y v).card) :
    ∃ w, w ∈ crossNeighbors G X Y v ∧ w ∉ Z := by
  by_contra h
  push_neg at h
  have hsub : crossNeighbors G X Y v ⊆ Z := by
    intro w hw
    exact h w hw
  exact (not_le_of_gt hcard) (Finset.card_le_card hsub)

/-- Under the numerical connector inequalities, an edge-maximal admissible
forest is connected on its support. -/
theorem preconnected_support_of_edge_maximal_admissibleForest
    {F P : SimpleGraph V} {X Y L : Finset V} {budget d : ℕ}
    (hcut : IsCut X Y)
    (hP : AdmissibleForest G F X Y L budget P)
    (hmax : ∀ Q, AdmissibleForest G F X Y L budget Q →
      Q.edgeSet.ncard ≤ P.edgeSet.ncard)
    (hdegree : ∀ v, v ∉ L → d < (crossNeighbors G X Y v).card)
    (hfirst : budget + L.card < d + 1)
    (hcommon : max X.card Y.card + budget + 1 < 2 * (d + 1)) :
    ∀ {x y}, x ∈ P.support → y ∈ P.support → P.Reachable x y := by
  intro x y hx hy
  by_contra hxy
  obtain ⟨u, hxu, hdu⟩ := LinearForest.exists_leaf_reachable hP.linearForest hx
  obtain ⟨v, hyv, hdv⟩ := LinearForest.exists_leaf_reachable hP.linearForest hy
  have huP : u ∈ P.support := by
    by_cases h : x = u
    · simpa [h] using hx
    · exact SimpleGraph.mem_support_of_reachable (Ne.symm h) hxu.symm
  have hvP : v ∈ P.support := by
    by_cases h : y = v
    · simpa [h] using hy
    · exact SimpleGraph.mem_support_of_reachable (Ne.symm h) hyv.symm
  have huv : ¬P.Reachable u v := by
    intro huv
    exact hxy (hxu.trans (huv.trans hyv.symm))
  have huL : u ∉ L := hP.2.2.2.2.1 u huP (by omega)
  have hvL : v ∉ L := hP.2.2.2.2.1 v hvP (by omega)
  have hduHigh := hdegree u huL
  have hdvHigh := hdegree v hvL
  have hsupp : P.support.toFinset.card ≤ budget := by
    have hsuppEq : P.support.ncard = P.support.toFinset.card := by
      have h := Set.ncard_coe_finset P.support.toFinset
      rw [Set.coe_toFinset] at h
      exact h
    rw [← hsuppEq]
    exact hP.support_card_le_budget
  by_cases huX : u ∈ X
  · by_cases hvX : v ∈ X
    · have hcard : Y.card + P.support.toFinset.card <
          (crossNeighbors G X Y u).card +
            (crossNeighbors G X Y v).card := by
        have hside : Y.card ≤ max X.card Y.card := Nat.le_max_right _ _
        omega
      obtain ⟨w, huw, hvw, hwY, hwP⟩ :=
        exists_common_crossNeighbor_not_mem (G := G) hcut huX hvX hcard
      have hnew := AdmissibleForest.sup_two_edge_connector hP huP hvP
        (by omega) (by omega) huv
        (by simpa using hwP) huw hvw.symm
        (Or.inl ⟨huX, hwY⟩) (Or.inr ⟨hwY, hvX⟩)
      have hle := hmax _ hnew.1
      omega
    · have hvY : v ∈ Y := (hcut.mem_right_iff v).mpr hvX
      let Z := P.support.toFinset ∪ L
      have hZcard : Z.card < (crossNeighbors G X Y u).card := by
        have hZle := Finset.card_union_le P.support.toFinset L
        dsimp [Z]
        omega
      obtain ⟨w, hwCross, hwZ⟩ :=
        exists_mem_crossNeighbors_not_mem_of_card_lt (G := G) hZcard
      have huw := (mem_crossNeighbors.mp hwCross).1
      have hwY : w ∈ Y := by
        simpa [huX] using (mem_crossNeighbors.mp hwCross).2
      have hwP : w ∉ P.support := by
        intro hw
        exact hwZ (Finset.mem_union.mpr (Or.inl (Set.mem_toFinset.mpr hw)))
      have hwL : w ∉ L := by
        intro hw
        exact hwZ (Finset.mem_union.mpr (Or.inr hw))
      have hdwHigh := hdegree w hwL
      let Z2 := insert w P.support.toFinset
      have hZ2card : X.card + Z2.card <
          (crossNeighbors G X Y w).card +
            (crossNeighbors G X Y v).card := by
        have hZle : Z2.card ≤ P.support.toFinset.card + 1 := by
          exact Finset.card_insert_le _ _
        have hside : X.card ≤ max X.card Y.card := Nat.le_max_left _ _
        omega
      obtain ⟨z, hwz, hvz, hzX, hzZ2⟩ :=
        exists_common_crossNeighbor_not_mem_right (G := G) hcut hwY hvY hZ2card
      have hzP : z ∉ P.support := by
        intro hz
        exact hzZ2 (Finset.mem_insert_of_mem (Set.mem_toFinset.mpr hz))
      have hwzNe : w ≠ z := by
        intro h
        subst z
        exact hzZ2 (Finset.mem_insert_self w P.support.toFinset)
      have hnew := AdmissibleForest.sup_three_edge_connector hP huP hvP
        (by omega) (by omega) huv hwP hzP hwzNe huw hwz hvz.symm
        (Or.inl ⟨huX, hwY⟩) (Or.inr ⟨hwY, hzX⟩)
        (Or.inl ⟨hzX, hvY⟩)
      have hle := hmax _ hnew.1
      omega
  · have huY : u ∈ Y := (hcut.mem_right_iff u).mpr huX
    by_cases hvX : v ∈ X
    · let Z := P.support.toFinset ∪ L
      have hZcard : Z.card < (crossNeighbors G X Y u).card := by
        have hZle := Finset.card_union_le P.support.toFinset L
        dsimp [Z]
        omega
      obtain ⟨w, hwCross, hwZ⟩ :=
        exists_mem_crossNeighbors_not_mem_of_card_lt (G := G) hZcard
      have huw := (mem_crossNeighbors.mp hwCross).1
      have hwX : w ∈ X := by
        simpa [huX] using (mem_crossNeighbors.mp hwCross).2
      have hwP : w ∉ P.support := by
        intro hw
        exact hwZ (Finset.mem_union.mpr (Or.inl (Set.mem_toFinset.mpr hw)))
      have hwL : w ∉ L := by
        intro hw
        exact hwZ (Finset.mem_union.mpr (Or.inr hw))
      have hdwHigh := hdegree w hwL
      let Z2 := insert w P.support.toFinset
      have hZ2card : Y.card + Z2.card <
          (crossNeighbors G X Y w).card +
            (crossNeighbors G X Y v).card := by
        have hZle : Z2.card ≤ P.support.toFinset.card + 1 := by
          exact Finset.card_insert_le _ _
        have hside : Y.card ≤ max X.card Y.card := Nat.le_max_right _ _
        omega
      obtain ⟨z, hwz, hvz, hzY, hzZ2⟩ :=
        exists_common_crossNeighbor_not_mem (G := G) hcut hwX hvX hZ2card
      have hzP : z ∉ P.support := by
        intro hz
        exact hzZ2 (Finset.mem_insert_of_mem (Set.mem_toFinset.mpr hz))
      have hwzNe : w ≠ z := by
        intro h
        subst z
        exact hzZ2 (Finset.mem_insert_self w P.support.toFinset)
      have hnew := AdmissibleForest.sup_three_edge_connector hP huP hvP
        (by omega) (by omega) huv hwP hzP hwzNe huw hwz hvz.symm
        (Or.inr ⟨huY, hwX⟩) (Or.inl ⟨hwX, hzY⟩)
        (Or.inr ⟨hzY, hvX⟩)
      have hle := hmax _ hnew.1
      omega
    · have hvY : v ∈ Y := (hcut.mem_right_iff v).mpr hvX
      have hcard : X.card + P.support.toFinset.card <
          (crossNeighbors G X Y u).card +
            (crossNeighbors G X Y v).card := by
        have hside : X.card ≤ max X.card Y.card := Nat.le_max_left _ _
        omega
      obtain ⟨w, huw, hvw, hwX, hwP⟩ :=
        exists_common_crossNeighbor_not_mem_right (G := G) hcut huY hvY hcard
      have hnew := AdmissibleForest.sup_two_edge_connector hP huP hvP
        (by omega) (by omega) huv
        (by simpa using hwP) huw hvw.symm
        (Or.inr ⟨huY, hwX⟩) (Or.inl ⟨hwX, hvY⟩)
      have hle := hmax _ hnew.1
      omega

variable {P F : SimpleGraph V} [DecidableRel P.Adj]

private def vertexSign (X : Finset V) (v : V) : ℤ :=
  if v ∈ X then 1 else -1

private def edgeSign (X : Finset V) (e : Sym2 V) : ℤ :=
  e.lift ⟨fun u v ↦ vertexSign X u + vertexSign X v, by
    intro u v
    simp only [add_comm]⟩

private theorem two_mul_sum_vertexSign_support
    {a b : V} (p : P.Walk a b) (X : Finset V) :
    2 * (p.support.map (vertexSign X)).sum =
      vertexSign X a + vertexSign X b +
        (p.edges.map (edgeSign X)).sum := by
  induction p with
  | nil => simp; omega
  | @cons a c b hac p ih =>
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.edges_cons,
        List.map_cons, List.sum_cons, edgeSign, Sym2.lift_mk]
      omega

private theorem edgeSign_eq_indicator
    {X Y : Finset V} (hcut : IsCut X Y)
    (hsuppF : F.support ⊆ (X : Set V))
    (hclass : ∀ ⦃u v⦄, P.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)))
    {a b : V} (p : P.Walk a b) {e : Sym2 V} (he : e ∈ p.edges) :
    edgeSign X e = if e ∈ F.edgeFinset then 2 else 0 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huvP : P.Adj u v := p.adj_of_mem_edges he
      by_cases huvF : F.Adj u v
      · have huX : u ∈ X := hsuppF huvF.mem_support_left
        have hvX : v ∈ X := hsuppF huvF.mem_support_right
        simp [edgeSign, vertexSign, huvF, huX, hvX,
          SimpleGraph.mem_edgeFinset]
      · have hcross := (hclass huvP).resolve_left huvF
        rcases hcross with ⟨huX, hvY⟩ | ⟨huY, hvX⟩
        · have hvXn : v ∉ X := (hcut.mem_right_iff v).mp hvY
          simp [edgeSign, vertexSign, huvF, huX, hvXn,
            SimpleGraph.mem_edgeFinset]
        · have huXn : u ∉ X := (hcut.mem_right_iff u).mp huY
          simp [edgeSign, vertexSign, huvF, huXn, hvX,
            SimpleGraph.mem_edgeFinset]

private theorem list_sum_eq_two_mul_filter_length
    {E : Type*} [DecidableEq E] (s : Finset E) (f : E → ℤ)
    (l : List E) (hpoint : ∀ e ∈ l, f e = if e ∈ s then 2 else 0) :
    (l.map f).sum = 2 * (l.filter fun e ↦ e ∈ s).length := by
  induction l with
  | nil => simp
  | cons e l ih =>
      have he := hpoint e (by simp)
      have htail : ∀ z ∈ l, f z = if z ∈ s then 2 else 0 := by
        intro z hz
        exact hpoint z (by simp [hz])
      rw [List.map_cons, List.sum_cons, ih htail]
      by_cases heS : e ∈ s <;> simp [heS] at he ⊢ <;> omega

private theorem sum_edgeSign_eq_two_mul_filter_length
    {X Y : Finset V} (hcut : IsCut X Y)
    (hsuppF : F.support ⊆ (X : Set V))
    (hclass : ∀ ⦃u v⦄, P.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)))
    {a b : V} (p : P.Walk a b) :
    (p.edges.map (edgeSign X)).sum =
      2 * (p.edges.filter fun e ↦ e ∈ F.edgeFinset).length := by
  apply list_sum_eq_two_mul_filter_length F.edgeFinset
  intro e he
  exact edgeSign_eq_indicator hcut hsuppF hclass p he

private theorem edgeFinset_subset_walk_edges
    (hlinP : LinearForest P) (hFP : F ≤ P)
    {a b : V} (p : P.Walk a b)
    (hsupport : p.support.toFinset = P.support.toFinset) :
    F.edgeFinset ⊆ p.edges.toFinset := by
  intro e heF
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huvF : F.Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heF
      have huvP : P.Adj u v := hFP huvF
      have huSuppP : u ∈ P.support := huvP.mem_support_left
      have hvSuppP : v ∈ P.support := huvP.mem_support_right
      have huSupp : u ∈ p.support := by
        apply List.mem_toFinset.mp
        rw [hsupport]
        exact Set.mem_toFinset.mpr huSuppP
      have hvSupp : v ∈ p.support := by
        apply List.mem_toFinset.mp
        rw [hsupport]
        exact Set.mem_toFinset.mpr hvSuppP
      have huVerts : u ∈ p.toSubgraph.verts :=
        p.mem_verts_toSubgraph.mpr huSupp
      have hvVerts : v ∈ p.toSubgraph.verts :=
        p.mem_verts_toSubgraph.mpr hvSupp
      obtain ⟨q, hq⟩ :=
        (SimpleGraph.Subgraph.preconnected_iff_forall_exists_walk_subgraph
          p.toSubgraph).mp p.toSubgraph_connected.preconnected huVerts hvVerts
      have hbridge : P.IsBridge s(u, v) :=
        (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hlinP.1)
          (by simpa only [SimpleGraph.mem_edgeSet] using huvP)
      have heq : s(u, v) ∈ q.edges :=
        (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp hbridge) q
      have heq' : s(u, v) ∈ q.toSubgraph.edgeSet :=
        q.mem_edges_toSubgraph.mpr heq
      exact List.mem_toFinset.mpr
        (p.mem_edges_toSubgraph.mp (SimpleGraph.Subgraph.edgeSet_mono hq heq'))

private theorem filter_walk_edges_length_eq_card
    {a b : V} {p : P.Walk a b} (hp : p.IsPath)
    (hsub : F.edgeFinset ⊆ p.edges.toFinset) :
    (p.edges.filter fun e ↦ e ∈ F.edgeFinset).length = F.edgeFinset.card := by
  have hnodup : (p.edges.filter fun e ↦ e ∈ F.edgeFinset).Nodup :=
    hp.isTrail.edges_nodup.filter _
  have heq : (p.edges.filter fun e ↦ e ∈ F.edgeFinset).toFinset =
      F.edgeFinset := by
    ext e
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      and_iff_right_iff_imp]
    exact fun he ↦ List.mem_toFinset.mp (hsub he)
  rw [← List.toFinset_card_of_nodup hnodup, heq]

private theorem list_sum_eq_finset_sum_of_nodup
    (f : V → ℤ) {l : List V} (hl : l.Nodup) :
    (l.map f).sum = ∑ v ∈ l.toFinset, f v := by
  induction l with
  | nil => simp
  | cons v l ih =>
      have hv : v ∉ l := (List.nodup_cons.mp hl).1
      have hln : l.Nodup := (List.nodup_cons.mp hl).2
      simp [hv, ih hln]

private theorem sum_vertexSign_support_eq_card_sub
    {X Y : Finset V} (hcut : IsCut X Y)
    {a b : V} {p : P.Walk a b} (hp : p.IsPath) :
    (p.support.map (vertexSign X)).sum =
      ((p.support.toFinset.filter fun v ↦ v ∈ X).card : ℤ) -
        ((p.support.toFinset.filter fun v ↦ v ∈ Y).card : ℤ) := by
  rw [list_sum_eq_finset_sum_of_nodup (vertexSign X) hp.support_nodup]
  let S := p.support.toFinset
  have hnot : (S.filter fun v ↦ v ∉ X) = S.filter fun v ↦ v ∈ Y := by
    ext v
    simp only [Finset.mem_filter]
    exact and_congr_right fun _ ↦ (hcut.mem_right_iff v).symm
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v ↦ v ∈ X)]
  rw [hnot]
  have hsumX : (∑ x ∈ S.filter (fun v ↦ v ∈ X), vertexSign X x) =
      ((S.filter fun v ↦ v ∈ X).card : ℤ) := by
    calc
      _ = ∑ _x ∈ S.filter (fun v ↦ v ∈ X), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxX := (Finset.mem_filter.mp hx).2
        simp [vertexSign, hxX]
      _ = ((S.filter fun v ↦ v ∈ X).card : ℤ) := by simp
  have hsumY : (∑ x ∈ S.filter (fun v ↦ v ∈ Y), vertexSign X x) =
      -((S.filter fun v ↦ v ∈ Y).card : ℤ) := by
    calc
      _ = ∑ _x ∈ S.filter (fun v ↦ v ∈ Y), (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxY := (Finset.mem_filter.mp hx).2
        have hxX : x ∉ X := (hcut.mem_right_iff x).mp hxY
        simp [vertexSign, hxX]
      _ = -((S.filter fun v ↦ v ∈ Y).card : ℤ) := by simp
  rw [hsumX, hsumY]
  change ((S.filter fun v ↦ v ∈ X).card : ℤ) +
      -((S.filter fun v ↦ v ∈ Y).card : ℤ) = _
  rw [sub_eq_add_neg]

theorem support_part_card_eq_add_forest_edges
    {X Y : Finset V} (hcut : IsCut X Y)
    (hlinP : LinearForest P) (hFP : F ≤ P)
    (hsuppF : F.support ⊆ (X : Set V))
    (hclass : ∀ ⦃u v⦄, P.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)))
    {a b : V} (p : P.Walk a b) (hp : p.IsPath)
    (hsupport : p.support.toFinset = P.support.toFinset)
    (ha : a ∈ X) (hb : b ∈ Y) :
    (p.support.toFinset.filter fun v ↦ v ∈ X).card =
      (p.support.toFinset.filter fun v ↦ v ∈ Y).card + F.edgeFinset.card := by
  have hsub : F.edgeFinset ⊆ p.edges.toFinset :=
    edgeFinset_subset_walk_edges hlinP hFP p hsupport
  have hfilter :
      (p.edges.filter fun e ↦ e ∈ F.edgeFinset).length = F.edgeFinset.card :=
    filter_walk_edges_length_eq_card hp hsub
  have htel := two_mul_sum_vertexSign_support p X
  rw [sum_vertexSign_support_eq_card_sub hcut hp,
    sum_edgeSign_eq_two_mul_filter_length hcut hsuppF hclass p,
    hfilter] at htel
  have hbX : b ∉ X := (hcut.mem_right_iff b).mp hb
  simp only [vertexSign, if_pos ha, if_neg hbX] at htel
  omega

theorem card_restrictedPart_eq_filter (R X : Finset V) :
    (restrictedPart R X).card = (R.filter fun v ↦ v ∈ X).card := by
  apply Finset.card_bij (fun x _ ↦ x.1)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.2, mem_restrictedPart.mp hx⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro y hy
    exact ⟨⟨y, (Finset.mem_filter.mp hy).1⟩,
      mem_restrictedPart.mpr (Finset.mem_filter.mp hy).2, rfl⟩

theorem restrictedParts_pathRemainder_card_eq
    {X Y : Finset V} (hcut : IsCut X Y) (hYX : Y.card ≤ X.card)
    (hlinP : LinearForest P) (hFP : F ≤ P)
    (hsuppF : F.support ⊆ (X : Set V))
    (hforestCard : F.edgeFinset.card = X.card - Y.card)
    (hclass : ∀ ⦃u v⦄, P.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)))
    {a b : V} (p : P.Walk a b) (hp : p.IsPath)
    (hsupport : p.support.toFinset = P.support.toFinset)
    (ha : a ∈ X) (hb : b ∈ Y) :
    (restrictedPart (pathRemainder p) X).card =
      (restrictedPart (pathRemainder p) Y).card := by
  have hab : a ≠ b := by
    intro hab
    subst b
    exact Finset.disjoint_left.mp hcut.1 ha hb
  let S := p.support.toFinset
  let R := pathRemainder p
  let SX := S.filter fun v ↦ v ∈ X
  let SY := S.filter fun v ↦ v ∈ Y
  let RX := R.filter fun v ↦ v ∈ X
  let RY := R.filter fun v ↦ v ∈ Y
  have hsupportBalance : SX.card = SY.card + F.edgeFinset.card := by
    simpa only [SX, SY, S] using
      support_part_card_eq_add_forest_edges hcut hlinP hFP hsuppF hclass
        p hp hsupport ha hb
  have hglobalBalance : X.card = Y.card + F.edgeFinset.card := by
    rw [hforestCard]
    omega
  have hSRinter : S ∩ R = {a, b} := by
    simpa only [S, R] using support_inter_pathRemainder hp hab
  have hSRunion : S ∪ R = Finset.univ := by
    simpa only [S, R] using support_union_pathRemainder p
  have hbX : b ∉ X := (hcut.mem_right_iff b).mp hb
  have haY : a ∉ Y := (hcut.mem_left_iff a).mp ha
  have hunionX : SX ∪ RX = X := by
    ext v
    simp only [SX, RX, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨_, hvX⟩ | ⟨_, hvX⟩) <;> exact hvX
    · intro hvX
      have hvSR : v ∈ S ∪ R := by rw [hSRunion]; simp
      rcases Finset.mem_union.mp hvSR with hvS | hvR
      · exact Or.inl ⟨hvS, hvX⟩
      · exact Or.inr ⟨hvR, hvX⟩
  have hinterX : SX ∩ RX = {a} := by
    ext v
    simp only [SX, RX, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hvS, hvX⟩, hvR, _⟩
      have hvab : v ∈ ({a, b} : Finset V) := by
        rw [← hSRinter]
        exact Finset.mem_inter.mpr ⟨hvS, hvR⟩
      rcases Finset.mem_insert.mp hvab with hva | hvb
      · exact hva
      · have : v = b := Finset.mem_singleton.mp hvb
        subst v
        exact (hbX hvX).elim
    · rintro rfl
      exact ⟨⟨List.mem_toFinset.mpr p.start_mem_support, ha⟩,
        start_mem_pathRemainder hp, ha⟩
  have hunionY : SY ∪ RY = Y := by
    ext v
    simp only [SY, RY, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨_, hvY⟩ | ⟨_, hvY⟩) <;> exact hvY
    · intro hvY
      have hvSR : v ∈ S ∪ R := by rw [hSRunion]; simp
      rcases Finset.mem_union.mp hvSR with hvS | hvR
      · exact Or.inl ⟨hvS, hvY⟩
      · exact Or.inr ⟨hvR, hvY⟩
  have hinterY : SY ∩ RY = {b} := by
    ext v
    simp only [SY, RY, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hvS, hvY⟩, hvR, _⟩
      have hvab : v ∈ ({a, b} : Finset V) := by
        rw [← hSRinter]
        exact Finset.mem_inter.mpr ⟨hvS, hvR⟩
      rcases Finset.mem_insert.mp hvab with hva | hvb
      · subst v
        exact (haY hvY).elim
      · exact Finset.mem_singleton.mp hvb
    · rintro rfl
      exact ⟨⟨List.mem_toFinset.mpr p.end_mem_support, hb⟩,
        end_mem_pathRemainder hp, hb⟩
  have hcardX := Finset.card_union_add_card_inter SX RX
  have hcardY := Finset.card_union_add_card_inter SY RY
  rw [hunionX, hinterX, Finset.card_singleton] at hcardX
  rw [hunionY, hinterY, Finset.card_singleton] at hcardY
  have hrem : RX.card = RY.card := by omega
  rw [card_restrictedPart_eq_filter, card_restrictedPart_eq_filter]
  simpa only [RX, RY, R] using hrem


theorem isHamiltonian_of_balanced_absorbing_path_of_crossDegree
    {X Y T : Finset V} (hcut : IsCut X Y)
    {a b : V} (ha : a ∈ X) (hb : b ∈ Y) (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath)
    (hV : 3 ≤ Fintype.card V)
    (hbalance :
      (restrictedPart (pathRemainder p) X).card =
        (restrictedPart (pathRemainder p) Y).card)
    {d m : ℕ}
    (hprotected : ∀ v, v ∈ pathRemainder p → v ∉ T)
    (hhigh : ∀ v, v ∉ T → d < (crossNeighbors G X Y v).card)
    (hinterior : (pathInterior p).card ≤ m)
    (hnumeric : max X.card Y.card + 2 + 2 * m ≤ 2 * (d + 1)) :
    G.IsHamiltonian := by
  apply isHamiltonian_of_absorbing_path hcut ha hb hab p hp hV hbalance
  intro z
  have hzR : z.1 ∈ pathRemainder p := z.2
  have hcrossHigh := hhigh z.1 (hprotected z.1 hzR)
  have hloss := crossNeighbors_card_le_degree_induce_add_pathInterior
    (G := G) hcut p z
  have hpart : (restrictedPart (pathRemainder p) X).card ≤ X.card := by
    rw [card_restrictedPart_eq_filter]
    apply Finset.card_le_card
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hside : X.card ≤ max X.card Y.card := Nat.le_max_left _ _
  omega

theorem exists_balanced_extension_of_endpoints_mem_left
    {X Y : Finset V} (hcut : IsCut X Y) (hYX : Y.card ≤ X.card)
    (hlinP : LinearForest P) (hFP : F ≤ P) (hPG : P ≤ G)
    (hsuppF : F.support ⊆ (X : Set V))
    (hforestCard : F.edgeFinset.card = X.card - Y.card)
    (hclass : ∀ ⦃u v⦄, P.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)))
    {a b w : V} (p : P.Walk a b) (hp : p.IsPath)
    (hsupport : p.support.toFinset = P.support.toFinset)
    (ha : a ∈ X) (hb : b ∈ X) (hwY : w ∈ Y)
    (hwfresh : w ∉ P.support) (hleaf : (P.neighborSet a).ncard ≤ 1)
    (hwaG : G.Adj w a) :
    let H := P ⊔ SimpleGraph.edge w a
    ∃ q : H.Walk b w, H ≤ G ∧ q.IsPath ∧
      q.support.toFinset = H.support.toFinset ∧
      (restrictedPart (pathRemainder q) X).card =
        (restrictedPart (pathRemainder q) Y).card := by
  let H := P ⊔ SimpleGraph.edge w a
  have haw : a ≠ w := by
    intro haw
    subst w
    exact Finset.disjoint_left.mp hcut.1 ha hwY
  have hwa : w ≠ a := haw.symm
  have haP : a ∈ P.support := by
    apply Set.mem_toFinset.mp
    rw [← hsupport]
    exact List.mem_toFinset.mpr p.start_mem_support
  have hwNotP : w ∉ p.support := by
    intro hwp
    apply hwfresh
    apply Set.mem_toFinset.mp
    rw [← hsupport]
    exact List.mem_toFinset.mpr hwp
  have hnotreach : ¬P.Reachable a w := by
    intro hawReach
    exact hwfresh (SimpleGraph.mem_support_of_reachable hwa hawReach.symm)
  have hforestNcard : F.edgeSet.ncard = X.card - Y.card := by
    rw [← F.coe_edgeFinset, Set.ncard_coe_finset]
    exact hforestCard
  have hlinH : LinearForest H := by
    let pClassical : DecidableRel P.Adj := Classical.decRel _
    have hdegreeA : P.degree a ≤ 1 := by
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        Set.fintypeCard_eq_ncard]
      exact hleaf
    have hdegreeW : P.degree w ≤ 1 := by
      have hdw0 : P.degree w = 0 :=
        (SimpleGraph.degree_eq_zero_iff_notMem_support P w).mpr hwfresh
      omega
    simpa only [H, SimpleGraph.edge_comm w a] using
      hlinP.sup_edge_of_not_reachable hnotreach hdegreeA hdegreeW
  have hwaH : H.Adj w a := by
    apply (SimpleGraph.sup_adj P (SimpleGraph.edge w a) w a).mpr
    exact Or.inr (by simp [SimpleGraph.edge_adj, hwa])
  have hHG : H ≤ G := by
    apply sup_le hPG
    exact (SimpleGraph.edge_le_iff G).2 (Or.inr hwaG)
  let pH : H.Walk a b := p.mapLe le_sup_left
  have hpH : pH.IsPath := hp.map Function.injective_id
  let q0 : H.Walk w b := pH.cons hwaH
  have hq0 : q0.IsPath := by
    apply hpH.cons
    simpa only [pH, SimpleGraph.Walk.support_mapLe_eq_support] using hwNotP
  let q : H.Walk b w := q0.reverse
  have hq : q.IsPath := hq0.reverse
  have hHsupport : H.support = P.support ∪ {w} := by
    apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨z, hvz⟩ := (SimpleGraph.mem_support H).mp hv
      rcases (SimpleGraph.sup_adj P (SimpleGraph.edge w a) v z).mp hvz with
        hvzP | hvzE
      · exact Or.inl hvzP.mem_support_left
      · simp only [SimpleGraph.edge_adj] at hvzE
        rcases hvzE.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl haP
    · intro v hv
      rcases hv with hvP | rfl
      · exact SimpleGraph.support_mono le_sup_left hvP
      · exact hwaH.mem_support_left
  have hqSupport : q.support.toFinset = H.support.toFinset := by
    have hqS : q.support.toFinset = insert w p.support.toFinset := by
      simp only [q, q0, pH, SimpleGraph.Walk.support_reverse,
        SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_mapLe_eq_support, List.toFinset_reverse,
        List.toFinset_cons]
    have hHS : H.support.toFinset = insert w P.support.toFinset := by
      ext v
      simp only [Set.mem_toFinset, hHsupport, Set.mem_union,
        Set.mem_singleton_iff, Finset.mem_insert, or_comm]
    rw [hqS, hHS, hsupport]
  have hclassH : ∀ ⦃u v⦄, H.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)) := by
    intro u v huv
    rcases (SimpleGraph.sup_adj P (SimpleGraph.edge w a) u v).mp huv with
      huvP | huvE
    · exact hclass huvP
    · right
      simp only [SimpleGraph.edge_adj] at huvE
      rcases huvE.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr ⟨hwY, ha⟩
      · exact Or.inl ⟨ha, hwY⟩
  let fClassical : DecidableRel F.Adj := Classical.decRel _
  have hforestCard' : F.edgeFinset.card = X.card - Y.card :=
    (ncard_edgeSet_eq_card_edgeFinset F).symm.trans hforestNcard
  have hbalance := restrictedParts_pathRemainder_card_eq
    (P := H) (F := F) hcut hYX hlinH (hFP.trans le_sup_left)
      hsuppF hforestCard' hclassH q hq hqSupport hb hwY
  exact ⟨q, hHG, hq, hqSupport, hbalance⟩

theorem exists_balanced_extension_of_endpoints_mem_right
    {X Y : Finset V} (hcut : IsCut X Y) (hYX : Y.card ≤ X.card)
    (hlinP : LinearForest P) (hFP : F ≤ P) (hPG : P ≤ G)
    (hsuppF : F.support ⊆ (X : Set V))
    (hforestCard : F.edgeFinset.card = X.card - Y.card)
    (hclass : ∀ ⦃u v⦄, P.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)))
    {a b w : V} (p : P.Walk a b) (hp : p.IsPath)
    (hsupport : p.support.toFinset = P.support.toFinset)
    (ha : a ∈ Y) (hb : b ∈ Y) (hwX : w ∈ X)
    (hwfresh : w ∉ P.support) (hleaf : (P.neighborSet a).ncard ≤ 1)
    (hwaG : G.Adj w a) :
    let H := P ⊔ SimpleGraph.edge w a
    ∃ q : H.Walk w b, H ≤ G ∧ q.IsPath ∧
      q.support.toFinset = H.support.toFinset ∧
      (restrictedPart (pathRemainder q) X).card =
        (restrictedPart (pathRemainder q) Y).card := by
  let H := P ⊔ SimpleGraph.edge w a
  have hwa : w ≠ a := by
    intro hwa
    subst a
    exact Finset.disjoint_left.mp hcut.1 hwX ha
  have haP : a ∈ P.support := by
    apply Set.mem_toFinset.mp
    rw [← hsupport]
    exact List.mem_toFinset.mpr p.start_mem_support
  have hwNotP : w ∉ p.support := by
    intro hwp
    apply hwfresh
    apply Set.mem_toFinset.mp
    rw [← hsupport]
    exact List.mem_toFinset.mpr hwp
  have hnotreach : ¬P.Reachable a w := by
    intro hawReach
    exact hwfresh (SimpleGraph.mem_support_of_reachable hwa hawReach.symm)
  have hforestNcard : F.edgeSet.ncard = X.card - Y.card := by
    rw [← F.coe_edgeFinset, Set.ncard_coe_finset]
    exact hforestCard
  have hlinH : LinearForest H := by
    let pClassical : DecidableRel P.Adj := Classical.decRel _
    have hdegreeA : P.degree a ≤ 1 := by
      rw [← SimpleGraph.card_neighborSet_eq_degree,
        Set.fintypeCard_eq_ncard]
      exact hleaf
    have hdegreeW : P.degree w ≤ 1 := by
      have hdw0 : P.degree w = 0 :=
        (SimpleGraph.degree_eq_zero_iff_notMem_support P w).mpr hwfresh
      omega
    simpa only [H, SimpleGraph.edge_comm w a] using
      hlinP.sup_edge_of_not_reachable hnotreach hdegreeA hdegreeW
  have hwaH : H.Adj w a := by
    apply (SimpleGraph.sup_adj P (SimpleGraph.edge w a) w a).mpr
    exact Or.inr (by simp [SimpleGraph.edge_adj, hwa])
  have hHG : H ≤ G := by
    apply sup_le hPG
    exact (SimpleGraph.edge_le_iff G).2 (Or.inr hwaG)
  let pH : H.Walk a b := p.mapLe le_sup_left
  have hpH : pH.IsPath := hp.map Function.injective_id
  let q : H.Walk w b := pH.cons hwaH
  have hq : q.IsPath := by
    apply hpH.cons
    simpa only [pH, SimpleGraph.Walk.support_mapLe_eq_support] using hwNotP
  have hHsupport : H.support = P.support ∪ {w} := by
    apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨z, hvz⟩ := (SimpleGraph.mem_support H).mp hv
      rcases (SimpleGraph.sup_adj P (SimpleGraph.edge w a) v z).mp hvz with
        hvzP | hvzE
      · exact Or.inl hvzP.mem_support_left
      · simp only [SimpleGraph.edge_adj] at hvzE
        rcases hvzE.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl haP
    · intro v hv
      rcases hv with hvP | rfl
      · exact SimpleGraph.support_mono le_sup_left hvP
      · exact hwaH.mem_support_left
  have hqSupport : q.support.toFinset = H.support.toFinset := by
    have hqS : q.support.toFinset = insert w p.support.toFinset := by
      simp only [q, pH, SimpleGraph.Walk.support_cons,
        SimpleGraph.Walk.support_mapLe_eq_support, List.toFinset_cons]
    have hHS : H.support.toFinset = insert w P.support.toFinset := by
      ext v
      simp only [Set.mem_toFinset, hHsupport, Set.mem_union,
        Set.mem_singleton_iff, Finset.mem_insert, or_comm]
    rw [hqS, hHS, hsupport]
  have hclassH : ∀ ⦃u v⦄, H.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)) := by
    intro u v huv
    rcases (SimpleGraph.sup_adj P (SimpleGraph.edge w a) u v).mp huv with
      huvP | huvE
    · exact hclass huvP
    · right
      simp only [SimpleGraph.edge_adj] at huvE
      rcases huvE.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hwX, ha⟩
      · exact Or.inr ⟨ha, hwX⟩
  let fClassical : DecidableRel F.Adj := Classical.decRel _
  have hforestCard' : F.edgeFinset.card = X.card - Y.card :=
    (ncard_edgeSet_eq_card_edgeFinset F).symm.trans hforestNcard
  have hbalance := restrictedParts_pathRemainder_card_eq
    (P := H) (F := F) hcut hYX hlinH (hFP.trans le_sup_left)
      hsuppF hforestCard' hclassH q hq hqSupport hwX hb
  exact ⟨q, hHG, hq, hqSupport, hbalance⟩

/-- Adding an edge from a supported vertex to one new vertex enlarges the
support by at most that new vertex. -/
theorem support_sup_edge_subset {P : SimpleGraph V} {w a : V}
    (ha : a ∈ P.support) :
    (P ⊔ SimpleGraph.edge w a).support ⊆ P.support ∪ {w} := by
  intro v hv
  obtain ⟨z, hvz⟩ := (SimpleGraph.mem_support _).mp hv
  rcases (SimpleGraph.sup_adj P (SimpleGraph.edge w a) v z).mp hvz with
    hvzP | hvzE
  · exact Or.inl hvzP.mem_support_left
  · simp only [SimpleGraph.edge_adj] at hvzE
    rcases hvzE.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ha

theorem ncard_support_sup_edge_le {P : SimpleGraph V} {w a : V}
    (ha : a ∈ P.support) :
    (P ⊔ SimpleGraph.edge w a).support.ncard ≤ P.support.ncard + 1 := by
  have hsub := support_sup_edge_subset (P := P) (w := w) ha
  exact (Set.ncard_le_ncard hsub).trans <| by
    simpa using Set.ncard_union_le P.support ({w} : Set V)

theorem pathInterior_card_le_support {a b : V} (p : G.Walk a b) :
    (pathInterior p).card ≤ p.support.toFinset.card := by
  apply Finset.card_le_card
  intro v hv
  apply List.mem_toFinset.mpr
  have hv' : v ∈ p.support.tail.dropLast := List.mem_toFinset.mp hv
  exact List.mem_of_mem_tail (List.dropLast_subset _ hv')

/-- Close a balanced spanning absorber path in a subgraph.  This is the
common final step for both the already-opposite and the one-edge-extension
endpoint cases. -/
theorem isHamiltonian_of_balanced_spanning_path
    {H : SimpleGraph V} (hHG : H ≤ G) {X Y T : Finset V}
    (hcut : IsCut X Y) {a b : V} (ha : a ∈ X) (hb : b ∈ Y)
    (q : H.Walk a b) (hq : q.IsPath)
    (hqSpans : ∀ v, v ∈ q.support ↔ v ∈ H.support)
    (hbalance :
      (restrictedPart (pathRemainder q) X).card =
        (restrictedPart (pathRemainder q) Y).card)
    (hTsupport : (T : Set V) ⊆ H.support)
    (haT : a ∉ T) (hbT : b ∉ T) (hHcard : H.support.ncard ≤ m)
    (hV : 3 ≤ Fintype.card V)
    (hhigh : ∀ v, v ∉ T → d < (crossNeighbors G X Y v).card)
    (hnumeric : max X.card Y.card + 2 + 2 * m ≤ 2 * (d + 1)) :
    G.IsHamiltonian := by
  let qG : G.Walk a b := q.mapLe hHG
  have hqG : qG.IsPath := hq.map Function.injective_id
  have hqGSpans : ∀ v, v ∈ qG.support ↔ v ∈ H.support := by
    intro v
    simpa only [qG, SimpleGraph.Walk.support_mapLe_eq_support] using hqSpans v
  have hab : a ≠ b := by
    intro hab
    subst b
    exact Finset.disjoint_left.mp hcut.1 ha hb
  have hprotected : ∀ v, v ∈ pathRemainder qG → v ∉ T := by
    intro v hvR hvT
    have hvH : v ∈ H.support := hTsupport hvT
    have hvq : v ∈ qG.support := by
      exact (hqGSpans v).mpr hvH
    have hva : v ≠ a := by
      intro hva
      subst v
      exact haT hvT
    have hvb : v ≠ b := by
      intro hvb
      subst v
      exact hbT hvT
    exact mem_pathRemainder.mp hvR
      (mem_pathInterior_of_mem_support_of_ne_endpoints hqG hvq hva hvb)
  have hqCard : qG.support.toFinset.card ≤ m := by
    have hsupportEq : qG.support.toFinset = H.support.toFinset := by
      ext v
      simpa only [List.mem_toFinset, Set.mem_toFinset] using hqGSpans v
    rw [hsupportEq]
    have hEq : H.support.toFinset.card = H.support.ncard := by
      have h := Set.ncard_coe_finset H.support.toFinset
      rw [Set.coe_toFinset] at h
      exact h.symm
    rw [hEq]
    exact hHcard
  have hinterior : (pathInterior qG).card ≤ m :=
    (pathInterior_card_le_support qG).trans hqCard
  have hbalanceG :
      (restrictedPart (pathRemainder qG) X).card =
        (restrictedPart (pathRemainder qG) Y).card := by
    have hs : qG.support = q.support := by
      exact SimpleGraph.Walk.support_mapLe_eq_support hHG q
    change
      (restrictedPart (Finset.univ \ qG.support.tail.dropLast.toFinset) X).card =
        (restrictedPart (Finset.univ \ qG.support.tail.dropLast.toFinset) Y).card
    rw [hs]
    exact hbalance
  exact isHamiltonian_of_balanced_absorbing_path_of_crossDegree hcut ha hb hab
    qG hqG hV hbalanceG hprotected hhigh hinterior hnumeric

/-- Deterministic good-cut Hamiltonicity.  The forest `F` corrects the cut
imbalance, `T` is the protected exceptional set (and contains the forest
support), and Hall attachments plus maximal connector absorption produce the
balanced spanning path closed by the bipartite endpoint theorem. -/
theorem isHamiltonian_of_oriented_goodCut
    {F : SimpleGraph V} {X Y T : Finset V} {d : ℕ}
    (hcut : IsCut X Y) (hYX : Y.card ≤ X.card)
    (hFG : F ≤ G) (hlinF : LinearForest F)
    (hsuppF : F.support ⊆ (X : Set V))
    (hforestCard : F.edgeFinset.card = X.card - Y.card)
    (hFT : F.support.toFinset ⊆ T) (hT : T.Nonempty)
    (hattach : ∀ v ∈ T,
      Fintype.card (AttachmentSlot F T) + T.card ≤
        (crossNeighbors G X Y v).card)
    (hhigh : ∀ v, v ∉ T → d < (crossNeighbors G X Y v).card)
    (hfirst : 9 * T.card + T.card < d + 1)
    (hcommon : max X.card Y.card + 9 * T.card + 1 < 2 * (d + 1))
    (hclose : max X.card Y.card + 2 + 2 * (9 * T.card + 1) ≤
      2 * (d + 1))
    (hV : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
  have hUnion : F.support.toFinset ∪ T = T :=
    Finset.union_eq_right.mpr hFT
  have hattach' : ∀ v ∈ F.support.toFinset ∪ T,
      Fintype.card (AttachmentSlot F (F.support.toFinset ∪ T)) +
          (F.support.toFinset ∪ T).card ≤
        (crossNeighbors G X Y v).card := by
    simpa only [hUnion] using hattach
  obtain ⟨P, hPadm0⟩ := exists_initial_admissibleForest
    (G := G) (F := F) (X := X) (Y := Y) (L := T)
      hcut hFG hlinF hsuppF hattach'
  have hPadm : AdmissibleForest G F X Y T (9 * T.card) P := by
    simpa only [hUnion] using hPadm0
  obtain ⟨P, hP, hmax⟩ :=
    exists_edge_maximal_admissibleForest (G := G) ⟨P, hPadm⟩
  have hconn : ∀ {x y}, x ∈ P.support → y ∈ P.support →
      P.Reachable x y :=
    preconnected_support_of_edge_maximal_admissibleForest
      (G := G) hcut hP hmax hhigh hfirst hcommon
  have hPnonempty : P.support.Nonempty := by
    obtain ⟨t, ht⟩ := hT
    exact ⟨t, hP.2.2.2.1 (Or.inr ht)⟩
  obtain ⟨a, b, p, hp, hspan, haLeaf, hbLeaf⟩ :=
    LinearForest.exists_spanning_path_of_preconnected_support
      hP.linearForest hPnonempty hconn
  have hpSpans : ∀ v, v ∈ p.support ↔ v ∈ P.support := by
    intro v
    rw [← Set.mem_toFinset, ← hspan, List.mem_toFinset]
  have haP : a ∈ P.support := by
    apply Set.mem_toFinset.mp
    rw [← hspan]
    exact List.mem_toFinset.mpr p.start_mem_support
  have hbP : b ∈ P.support := by
    apply Set.mem_toFinset.mp
    rw [← hspan]
    exact List.mem_toFinset.mpr p.end_mem_support
  have haT : a ∉ T := hP.2.2.2.2.1 a haP (by omega)
  have hbT : b ∉ T := hP.2.2.2.2.1 b hbP (by omega)
  have hTP : (T : Set V) ⊆ P.support := by
    intro v hv
    exact hP.2.2.2.1 (Or.inr hv)
  have hPcard : P.support.ncard ≤ 9 * T.card := hP.support_card_le_budget
  have hFP : F ≤ P := hP.1
  have hPG : P ≤ G := hP.2.1
  have hclass : ∀ ⦃u v⦄, P.Adj u v → F.Adj u v ∨
      ((u ∈ X ∧ v ∈ Y) ∨ (u ∈ Y ∧ v ∈ X)) :=
    hP.2.2.2.2.2.1
  by_cases haX : a ∈ X
  · by_cases hbX : b ∈ X
    · have hcrossHigh := hhigh a haT
      have hPfinCard : P.support.toFinset.card ≤ 9 * T.card := by
        have hEq : P.support.toFinset.card = P.support.ncard := by
          have h := Set.ncard_coe_finset P.support.toFinset
          rw [Set.coe_toFinset] at h
          exact h.symm
        rw [hEq]
        exact hPcard
      have hcard : P.support.toFinset.card <
          (crossNeighbors G X Y a).card := by omega
      obtain ⟨w, hwCross, hwfreshFin⟩ :=
        exists_mem_crossNeighbors_not_mem_of_card_lt (G := G) hcard
      have hwaG : G.Adj w a := (mem_crossNeighbors.mp hwCross).1.symm
      have hwY : w ∈ Y := by
        simpa only [crossNeighbors, haX, if_true] using
          (mem_crossNeighbors.mp hwCross).2
      have hwfresh : w ∉ P.support := by
        intro hw
        exact hwfreshFin (Set.mem_toFinset.mpr hw)
      obtain ⟨q, hHG, hq, hqspan, hbalance⟩ :=
        exists_balanced_extension_of_endpoints_mem_left
          (G := G) (P := P) (F := F) hcut hYX hP.linearForest hFP hPG
            hsuppF hforestCard hclass p hp hspan haX hbX hwY hwfresh
            (by omega) hwaG
      have hqSpans : ∀ v, v ∈ q.support ↔
          v ∈ (P ⊔ SimpleGraph.edge w a).support := by
        intro v
        rw [← Set.mem_toFinset, ← hqspan, List.mem_toFinset]
      have hwT : w ∉ T := fun hw ↦ hwfresh (hTP hw)
      have hTH : (T : Set V) ⊆ (P ⊔ SimpleGraph.edge w a).support :=
        hTP.trans (SimpleGraph.support_mono le_sup_left)
      have hHcard : (P ⊔ SimpleGraph.edge w a).support.ncard ≤
          9 * T.card + 1 :=
        (ncard_support_sup_edge_le haP).trans (Nat.add_le_add_right hPcard 1)
      exact isHamiltonian_of_balanced_spanning_path
        (G := G) (H := P ⊔ SimpleGraph.edge w a) (T := T)
        (d := d) (m := 9 * T.card + 1) hHG hcut hbX hwY q hq
          hqSpans hbalance hTH hbT hwT hHcard hV hhigh hclose
    · have hbY : b ∈ Y := (hcut.mem_right_iff b).mpr hbX
      have hbalance := restrictedParts_pathRemainder_card_eq
        (P := P) (F := F) hcut hYX hP.linearForest hFP hsuppF
          hforestCard hclass p hp hspan haX hbY
      have hPcard' : P.support.ncard ≤ 9 * T.card + 1 := by omega
      exact isHamiltonian_of_balanced_spanning_path
        (G := G) (H := P) (T := T) (d := d) (m := 9 * T.card + 1)
          hPG hcut haX hbY p hp hpSpans hbalance hTP haT hbT hPcard' hV
          hhigh hclose
  · have haY : a ∈ Y := (hcut.mem_right_iff a).mpr haX
    by_cases hbX : b ∈ X
    · let q : P.Walk b a := p.reverse
      have hq : q.IsPath := hp.reverse
      have hqspan : q.support.toFinset = P.support.toFinset := by
        simpa only [q, SimpleGraph.Walk.support_reverse,
          List.toFinset_reverse] using hspan
      have hqSpans : ∀ v, v ∈ q.support ↔ v ∈ P.support := by
        intro v
        rw [← Set.mem_toFinset, ← hqspan, List.mem_toFinset]
      have hbalance := restrictedParts_pathRemainder_card_eq
        (P := P) (F := F) hcut hYX hP.linearForest hFP hsuppF
          hforestCard hclass q hq hqspan hbX haY
      have hPcard' : P.support.ncard ≤ 9 * T.card + 1 := by omega
      exact isHamiltonian_of_balanced_spanning_path
        (G := G) (H := P) (T := T) (d := d) (m := 9 * T.card + 1)
          hPG hcut hbX haY q hq hqSpans hbalance hTP hbT haT hPcard' hV
          hhigh hclose
    · have hbY : b ∈ Y := (hcut.mem_right_iff b).mpr hbX
      have hcrossHigh := hhigh a haT
      have hPfinCard : P.support.toFinset.card ≤ 9 * T.card := by
        have hEq : P.support.toFinset.card = P.support.ncard := by
          have h := Set.ncard_coe_finset P.support.toFinset
          rw [Set.coe_toFinset] at h
          exact h.symm
        rw [hEq]
        exact hPcard
      have hcard : P.support.toFinset.card <
          (crossNeighbors G X Y a).card := by omega
      obtain ⟨w, hwCross, hwfreshFin⟩ :=
        exists_mem_crossNeighbors_not_mem_of_card_lt (G := G) hcard
      have hwaG : G.Adj w a := (mem_crossNeighbors.mp hwCross).1.symm
      have hwX : w ∈ X := by
        simpa only [crossNeighbors, haX, if_false] using
          (mem_crossNeighbors.mp hwCross).2
      have hwfresh : w ∉ P.support := by
        intro hw
        exact hwfreshFin (Set.mem_toFinset.mpr hw)
      obtain ⟨q, hHG, hq, hqspan, hbalance⟩ :=
        exists_balanced_extension_of_endpoints_mem_right
          (G := G) (P := P) (F := F) hcut hYX hP.linearForest hFP hPG
            hsuppF hforestCard hclass p hp hspan haY hbY hwX hwfresh
            (by omega) hwaG
      have hqSpans : ∀ v, v ∈ q.support ↔
          v ∈ (P ⊔ SimpleGraph.edge w a).support := by
        intro v
        rw [← Set.mem_toFinset, ← hqspan, List.mem_toFinset]
      have hwT : w ∉ T := fun hw ↦ hwfresh (hTP hw)
      have hTH : (T : Set V) ⊆ (P ⊔ SimpleGraph.edge w a).support :=
        hTP.trans (SimpleGraph.support_mono le_sup_left)
      have hHcard : (P ⊔ SimpleGraph.edge w a).support.ncard ≤
          9 * T.card + 1 :=
        (ncard_support_sup_edge_le haP).trans (Nat.add_le_add_right hPcard 1)
      exact isHamiltonian_of_balanced_spanning_path
        (G := G) (H := P ⊔ SimpleGraph.edge w a) (T := T)
        (d := d) (m := 9 * T.card + 1) hHG hcut hwX hbY q hq
          hqSpans hbalance hTH hwT hbT hHcard hV hhigh hclose

 /-- The numerical and neighbourhood data needed after an exact imbalance
 forest has been selected on the larger side of an oriented cut. -/
 def OrientedGoodCutCertificate (G F : SimpleGraph V) [DecidableRel G.Adj]
     (X Y : Finset V) : Prop :=
   ∃ (T : Finset V) (d : ℕ),
     F.support.toFinset ⊆ T ∧ T.Nonempty ∧
     (∀ v ∈ T,
       Fintype.card (AttachmentSlot F T) + T.card ≤
         (crossNeighbors G X Y v).card) ∧
     (∀ v, v ∉ T → d < (crossNeighbors G X Y v).card) ∧
     9 * T.card + T.card < d + 1 ∧
     max X.card Y.card + 9 * T.card + 1 < 2 * (d + 1) ∧
     max X.card Y.card + 2 + 2 * (9 * T.card + 1) ≤ 2 * (d + 1)

 theorem OrientedGoodCutCertificate.of_bounds
     {F : SimpleGraph V} {X Y T : Finset V} {d : ℕ}
     (hFT : F.support.toFinset ⊆ T) (hT : T.Nonempty)
     (hprotectedDegree : ∀ v ∈ T,
       3 * T.card ≤ (crossNeighbors G X Y v).card)
     (hhigh : ∀ v, v ∉ T → d < (crossNeighbors G X Y v).card)
     (hfirst : 9 * T.card + T.card < d + 1)
     (hcommon : max X.card Y.card + 9 * T.card + 1 < 2 * (d + 1))
     (hclose : max X.card Y.card + 2 + 2 * (9 * T.card + 1) ≤
       2 * (d + 1)) :
     OrientedGoodCutCertificate G F X Y := by
   refine ⟨T, d, hFT, hT, ?_, hhigh, hfirst, hcommon, hclose⟩
   intro v hv
   have hslots := card_attachmentSlot_le_two_mul F T
   have hdeg := hprotectedDegree v hv
   omega

 /-- Construct the protected set automatically from the exact imbalance
 forest, a specified low-cross-degree set, and one anchor vertex.  The
 parameter `t` is only an upper bound: callers never need to expose the
 resulting protected set. -/
 theorem isHamiltonian_of_oriented_goodCut_of_lowSet
     {F : SimpleGraph V} {X Y L : Finset V} {anchor : V} {t d : ℕ}
     (hcut : IsCut X Y) (hYX : Y.card ≤ X.card)
     (hFG : F ≤ G) (hlinF : LinearForest F)
     (hsuppF : F.support ⊆ (X : Set V))
     (hforestCard : F.edgeFinset.card = X.card - Y.card)
     (hsize : 2 * (X.card - Y.card) + L.card + 1 ≤ t)
     (hminCross : ∀ v, 3 * t ≤ (crossNeighbors G X Y v).card)
     (hhigh : ∀ v, v ∉ L → d < (crossNeighbors G X Y v).card)
     (hfirst : 10 * t < d + 1)
     (hcommon : max X.card Y.card + 9 * t + 1 < 2 * (d + 1))
     (hclose : max X.card Y.card + 2 + 2 * (9 * t + 1) ≤
       2 * (d + 1))
     (hV : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
   let T := insert anchor (F.support.toFinset ∪ L)
   have hsuppCard : F.support.toFinset.card ≤ 2 * (X.card - Y.card) := by
     have hsuppN := ncard_support_le_twice_card_edgeFinset F
     have hsuppEq : F.support.toFinset.card = F.support.ncard := by
       have h := Set.ncard_coe_finset F.support.toFinset
       rw [Set.coe_toFinset] at h
       exact h.symm
     calc
       F.support.toFinset.card = F.support.ncard := hsuppEq
       _ ≤ 2 * F.edgeFinset.card := hsuppN
       _ = 2 * (X.card - Y.card) := by rw [hforestCard]
   have hTcard : T.card ≤ t := by
     have hu := Finset.card_union_le F.support.toFinset L
     have hi := Finset.card_insert_le anchor (F.support.toFinset ∪ L)
     dsimp only [T]
     omega
   have hFT : F.support.toFinset ⊆ T := by
     intro v hv
     exact Finset.mem_insert_of_mem (Finset.mem_union_left L hv)
   have hT : T.Nonempty := ⟨anchor, Finset.mem_insert_self _ _⟩
   have hprotectedDegree : ∀ v ∈ T,
       3 * T.card ≤ (crossNeighbors G X Y v).card := by
     intro v _
     have := hminCross v
     omega
   have hhighT : ∀ v, v ∉ T → d < (crossNeighbors G X Y v).card := by
     intro v hv
     apply hhigh v
     intro hvL
     exact hv (Finset.mem_insert_of_mem (Finset.mem_union_right _ hvL))
   have hfirstT : 9 * T.card + T.card < d + 1 := by omega
   have hcommonT : max X.card Y.card + 9 * T.card + 1 <
       2 * (d + 1) := by omega
   have hcloseT : max X.card Y.card + 2 + 2 * (9 * T.card + 1) ≤
       2 * (d + 1) := by omega
   have hcertificate : OrientedGoodCutCertificate G F X Y :=
     OrientedGoodCutCertificate.of_bounds hFT hT hprotectedDegree hhighT
       hfirstT hcommonT hcloseT
   obtain ⟨T', d', hFT', hT', hattach, hhigh', hfirst', hcommon', hclose'⟩ :=
     hcertificate
   exact isHamiltonian_of_oriented_goodCut (G := G) hcut hYX hFG hlinF
     hsuppF hforestCard hFT' hT' hattach hhigh' hfirst' hcommon' hclose' hV

 /-- Symmetric automatic-low-set form.  The crossing-neighbour hypotheses
 are stated once in the original orientation and transported across the cut
 when the good-cut witness lies on the other side. -/
 theorem IsKGoodCut.isHamiltonian_of_lowSet {k : ℕ}
     (hgood : IsKGoodCut G X Y k) (L : Finset V) (anchor : V) {t d : ℕ}
     (hsizeLeft : 2 * (X.card - Y.card) + L.card + 1 ≤ t)
     (hsizeRight : 2 * (Y.card - X.card) + L.card + 1 ≤ t)
     (hminCross : ∀ v, 3 * t ≤ (crossNeighbors G X Y v).card)
     (hhigh : ∀ v, v ∉ L → d < (crossNeighbors G X Y v).card)
     (hfirst : 10 * t < d + 1)
     (hcommon : max X.card Y.card + 9 * t + 1 < 2 * (d + 1))
     (hclose : max X.card Y.card + 2 + 2 * (9 * t + 1) ≤
       2 * (d + 1))
     (hV : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
   rcases hgood.good.exists_exact with hF | hF
   · obtain ⟨F, hYX, hFG, hlinF, hsuppF, hcard0⟩ := hF
     have hcard : F.edgeFinset.card = X.card - Y.card := by
       simpa only [Nat.zero_add] using hcard0
     exact isHamiltonian_of_oriented_goodCut_of_lowSet
       (G := G) (anchor := anchor) hgood.1 hYX hFG hlinF hsuppF hcard
         hsizeLeft hminCross hhigh hfirst hcommon hclose hV
   · obtain ⟨F, hXY, hFG, hlinF, hsuppF, hcard0⟩ := hF
     have hcard : F.edgeFinset.card = Y.card - X.card := by
       simpa only [Nat.zero_add] using hcard0
     have hminCross' : ∀ v, 3 * t ≤ (crossNeighbors G Y X v).card := by
       intro v
       rw [crossNeighbors_swap (G := G) hgood.1]
       exact hminCross v
     have hhigh' : ∀ v, v ∉ L → d < (crossNeighbors G Y X v).card := by
       intro v hv
       rw [crossNeighbors_swap (G := G) hgood.1]
       exact hhigh v hv
     have hcommon' : max Y.card X.card + 9 * t + 1 < 2 * (d + 1) := by
       simpa only [max_comm] using hcommon
     have hclose' : max Y.card X.card + 2 + 2 * (9 * t + 1) ≤
         2 * (d + 1) := by
       simpa only [max_comm] using hclose
     exact isHamiltonian_of_oriented_goodCut_of_lowSet
       (G := G) (anchor := anchor) hgood.1.symm hXY hFG hlinF hsuppF hcard
         hsizeRight hminCross' hhigh' hfirst hcommon' hclose' hV

 /-- Consumer form for a sharp two-sided low-degree estimate.  Unlike the
 separate deficiency bounds below, this theorem uses the cardinality of the
 union directly and therefore loses no factor of two. -/
 theorem IsKGoodCut.isHamiltonian_of_lowCrossUnion_bound
     {k ell t d : ℕ} (hgood : IsKGoodCut G X Y k) (anchor : V)
     {q : ℝ}
     (hLcard :
       (lowCrossSet G X Y q ∪ lowCrossSet G Y X q).card ≤ ell)
     (hsizeLeft : 2 * (X.card - Y.card) + ell + 1 ≤ t)
     (hsizeRight : 2 * (Y.card - X.card) + ell + 1 ≤ t)
     (hd : (d : ℝ) ≤ q)
     (hminCross : ∀ v, 3 * t ≤ (crossNeighbors G X Y v).card)
     (hfirst : 10 * t < d + 1)
     (hcommon : max X.card Y.card + 9 * t + 1 < 2 * (d + 1))
     (hclose : max X.card Y.card + 2 + 2 * (9 * t + 1) ≤
       2 * (d + 1))
     (hV : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
   let LX := lowCrossSet G X Y q
   let LY := lowCrossSet G Y X q
   let L := LX ∪ LY
   have hLcard' : L.card ≤ ell := by
     simpa only [L, LX, LY] using hLcard
   have hsizeLeft' : 2 * (X.card - Y.card) + L.card + 1 ≤ t := by omega
   have hsizeRight' : 2 * (Y.card - X.card) + L.card + 1 ≤ t := by omega
   have hhigh : ∀ v, v ∉ L → d < (crossNeighbors G X Y v).card := by
     intro v hvL
     by_cases hvX : v ∈ X
     · have hvLX : v ∉ LX := by
         intro hv
         exact hvL (Finset.mem_union_left LY hv)
       have hdegReal : q < degreeInto G v Y := by
         apply lt_of_not_ge
         intro hdeg
         apply hvLX
         exact mem_lowCrossSet.mpr ⟨hvX, hdeg⟩
       have hcrossReal : (d : ℝ) <
           ((crossNeighbors G X Y v).card : ℝ) := by
         have heq : degreeInto G v Y =
             ((crossNeighbors G X Y v).card : ℝ) := by
           simp only [degreeInto, crossNeighbors, hvX, if_true]
           congr 1
           apply congrArg Finset.card
           ext w
           simp only [SimpleGraph.mem_neighborFinset, Finset.mem_inter]
         rw [← heq]
         exact hd.trans_lt hdegReal
       exact_mod_cast hcrossReal
     · have hvY : v ∈ Y := (hgood.1.mem_right_iff v).mpr hvX
       have hvLY : v ∉ LY := by
         intro hv
         exact hvL (Finset.mem_union_right LX hv)
       have hdegReal : q < degreeInto G v X := by
         apply lt_of_not_ge
         intro hdeg
         apply hvLY
         exact mem_lowCrossSet.mpr ⟨hvY, hdeg⟩
       have hcrossReal : (d : ℝ) <
           ((crossNeighbors G X Y v).card : ℝ) := by
         have heq : degreeInto G v X =
             ((crossNeighbors G X Y v).card : ℝ) := by
           simp only [degreeInto, crossNeighbors, hvX, if_false]
           congr 1
           apply congrArg Finset.card
           ext w
           simp only [SimpleGraph.mem_neighborFinset, Finset.mem_inter]
         rw [← heq]
         exact hd.trans_lt hdegReal
       exact_mod_cast hcrossReal
   exact IsKGoodCut.isHamiltonian_of_lowSet hgood L anchor
     hsizeLeft' hsizeRight' hminCross hhigh hfirst hcommon hclose hV

 /-- High-level deterministic DKM lemma. Near-half part sizes and a dense
 crossing graph bound the vertices of crossing degree at most `3N/10` on
 both sides. Their union is the low set for the automatic absorber. -/
 theorem IsKGoodCut.isHamiltonian_of_dense_crossing {k ell t d : ℕ}
     (hgood : IsKGoodCut G X Y k) (anchor : V)
     {N delta eps : ℝ}
     (hN : 0 ≤ N) (hdelta : 0 ≤ delta)
     (hXlower : N / 2 - delta ≤ (X.card : ℝ))
     (hXupper : (X.card : ℝ) ≤ N / 2 + delta)
     (hYlower : N / 2 - delta ≤ (Y.card : ℝ))
     (hYupper : (Y.card : ℝ) ≤ N / 2 + delta)
     (hdense : N ^ 2 / 4 - eps * N ^ 2 ≤ edgeCount G X Y)
     (hgap : 0 < N / 5 - delta)
     (hlowNumeric : delta * N + delta ^ 2 + eps * N ^ 2 <
       ((ell + 1 : ℕ) : ℝ) * (N / 5 - delta))
     (hsizeLeft : 2 * (X.card - Y.card) + 2 * ell + 1 ≤ t)
     (hsizeRight : 2 * (Y.card - X.card) + 2 * ell + 1 ≤ t)
     (hd : (d : ℝ) ≤ 3 * N / 10)
     (hminCross : ∀ v, 3 * t ≤ (crossNeighbors G X Y v).card)
     (hfirst : 10 * t < d + 1)
     (hcommon : max X.card Y.card + 9 * t + 1 < 2 * (d + 1))
     (hclose : max X.card Y.card + 2 + 2 * (9 * t + 1) ≤
       2 * (d + 1))
     (hV : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
   let LX := lowCrossSet G X Y (3 * N / 10)
   let LY := lowCrossSet G Y X (3 * N / 10)
   let L := LX ∪ LY
   have hK : (0 : ℝ) ≤ ((ell + 1 : ℕ) : ℝ) := by positivity
   have hLXreal : ((LX.card : ℕ) : ℝ) < ((ell + 1 : ℕ) : ℝ) := by
     simpa only [LX] using card_lowCrossSet_three_tenths_lt
       G X Y hN hdelta hK hXupper hYlower hYupper hdense hgap hlowNumeric
   have hdense' : N ^ 2 / 4 - eps * N ^ 2 ≤ edgeCount G Y X := by
     rw [edgeCount_comm]
     exact hdense
   have hLYreal : ((LY.card : ℕ) : ℝ) < ((ell + 1 : ℕ) : ℝ) := by
     simpa only [LY] using card_lowCrossSet_three_tenths_lt
       G Y X hN hdelta hK hYupper hXlower hXupper hdense' hgap hlowNumeric
   have hLXcard : LX.card ≤ ell := by
     have hnat : LX.card < ell + 1 := by exact_mod_cast hLXreal
     omega
   have hLYcard : LY.card ≤ ell := by
     have hnat : LY.card < ell + 1 := by exact_mod_cast hLYreal
     omega
   have hLcard : L.card ≤ 2 * ell := by
     have hu := Finset.card_union_le LX LY
     dsimp only [L]
     omega
   have hsizeLeft' : 2 * (X.card - Y.card) + L.card + 1 ≤ t := by omega
   have hsizeRight' : 2 * (Y.card - X.card) + L.card + 1 ≤ t := by omega
   have hhigh : ∀ v, v ∉ L → d < (crossNeighbors G X Y v).card := by
     intro v hvL
     by_cases hvX : v ∈ X
     · have hvLX : v ∉ LX := by
         intro hv
         exact hvL (Finset.mem_union_left LY hv)
       have hdegReal : 3 * N / 10 < degreeInto G v Y := by
         apply lt_of_not_ge
         intro hdeg
         apply hvLX
         exact mem_lowCrossSet.mpr ⟨hvX, hdeg⟩
       have hcrossReal : (d : ℝ) <
           ((crossNeighbors G X Y v).card : ℝ) := by
         have heq : degreeInto G v Y =
             ((crossNeighbors G X Y v).card : ℝ) := by
           simp only [degreeInto, crossNeighbors, hvX, if_true]
           congr 1
           apply congrArg Finset.card
           ext w
           simp only [SimpleGraph.mem_neighborFinset, Finset.mem_inter]
         rw [← heq]
         exact hd.trans_lt hdegReal
       exact_mod_cast hcrossReal
     · have hvY : v ∈ Y := (hgood.1.mem_right_iff v).mpr hvX
       have hvLY : v ∉ LY := by
         intro hv
         exact hvL (Finset.mem_union_right LX hv)
       have hdegReal : 3 * N / 10 < degreeInto G v X := by
         apply lt_of_not_ge
         intro hdeg
         apply hvLY
         exact mem_lowCrossSet.mpr ⟨hvY, hdeg⟩
       have hcrossReal : (d : ℝ) <
           ((crossNeighbors G X Y v).card : ℝ) := by
         have heq : degreeInto G v X =
             ((crossNeighbors G X Y v).card : ℝ) := by
           simp only [degreeInto, crossNeighbors, hvX, if_false]
           congr 1
           apply congrArg Finset.card
           ext w
           simp only [SimpleGraph.mem_neighborFinset, Finset.mem_inter]
         rw [← heq]
         exact hd.trans_lt hdegReal
       exact_mod_cast hcrossReal
   exact IsKGoodCut.isHamiltonian_of_lowSet hgood L anchor
     hsizeLeft' hsizeRight' hminCross hhigh hfirst hcommon hclose hV

 /-- Symmetric good-cut wrapper.  A `k`-good cut is first weakened to a good
 cut and truncated to the exact imbalance forest; the matching orientation's
 certificate then invokes `isHamiltonian_of_oriented_goodCut`. -/
 theorem IsKGoodCut.isHamiltonian_of_certificates {k : ℕ}
     (hgood : IsKGoodCut G X Y k)
     (hleft : ∀ F : SimpleGraph V, F ≤ G → LinearForest F →
       F.support ⊆ (X : Set V) →
       F.edgeFinset.card = X.card - Y.card →
       OrientedGoodCutCertificate G F X Y)
     (hright : ∀ F : SimpleGraph V, F ≤ G → LinearForest F →
       F.support ⊆ (Y : Set V) →
       F.edgeFinset.card = Y.card - X.card →
       OrientedGoodCutCertificate G F Y X)
     (hV : 3 ≤ Fintype.card V) : G.IsHamiltonian := by
   rcases hgood.good.exists_exact with hF | hF
   · obtain ⟨F, hYX, hFG, hlinF, hsuppF, hcard0⟩ := hF
     have hcard : F.edgeFinset.card = X.card - Y.card := by
       simpa only [Nat.zero_add] using hcard0
     obtain ⟨T, d, hFT, hT, hattach, hhigh, hfirst, hcommon, hclose⟩ :=
       hleft F hFG hlinF hsuppF hcard
     exact isHamiltonian_of_oriented_goodCut (G := G) hgood.1 hYX hFG hlinF
       hsuppF hcard hFT hT hattach hhigh hfirst hcommon hclose hV
   · obtain ⟨F, hXY, hFG, hlinF, hsuppF, hcard0⟩ := hF
     have hcard : F.edgeFinset.card = Y.card - X.card := by
       simpa only [Nat.zero_add] using hcard0
     obtain ⟨T, d, hFT, hT, hattach, hhigh, hfirst, hcommon, hclose⟩ :=
       hright F hFG hlinF hsuppF hcard
     exact isHamiltonian_of_oriented_goodCut (G := G) hgood.1.symm hXY hFG
       hlinF hsuppF hcard hFT hT hattach hhigh hfirst hcommon hclose hV

 /-- Induced-sample form of the symmetric theorem, with the conclusion in
 the repository's exact `IsSpannedByCycle` predicate. -/
 theorem isSpannedByCycle_of_induce_goodCut_certificates
     {S : Finset V} (hS : 3 ≤ S.card)
     {X Y : Finset (S : Set V)} {k : ℕ}
     (hgood : IsKGoodCut (G.induce (S : Set V)) X Y k)
     (hleft : ∀ F : SimpleGraph (S : Set V),
       F ≤ G.induce (S : Set V) → LinearForest F →
       F.support ⊆ (X : Set (S : Set V)) →
       F.edgeFinset.card = X.card - Y.card →
       OrientedGoodCutCertificate (G.induce (S : Set V)) F X Y)
     (hright : ∀ F : SimpleGraph (S : Set V),
       F ≤ G.induce (S : Set V) → LinearForest F →
       F.support ⊆ (Y : Set (S : Set V)) →
       F.edgeFinset.card = Y.card - X.card →
       OrientedGoodCutCertificate (G.induce (S : Set V)) F Y X) :
   IsSpannedByCycle G S := by
   apply (isSpannedByCycle_iff_isHamiltonian hS).2
   exact IsKGoodCut.isHamiltonian_of_certificates hgood hleft hright (by
     simpa using hS)

 /-- Induced-sample version of the high-level dense-crossing theorem. -/
 theorem isSpannedByCycle_of_induce_goodCut_dense_crossing
     {S : Finset V} (hS : 3 ≤ S.card)
     {X Y : Finset (S : Set V)} {k ell t d : ℕ}
     (hgood : IsKGoodCut (G.induce (S : Set V)) X Y k)
     (anchor : (S : Set V)) {N delta eps : ℝ}
     (hN : 0 ≤ N) (hdelta : 0 ≤ delta)
     (hXlower : N / 2 - delta ≤ (X.card : ℝ))
     (hXupper : (X.card : ℝ) ≤ N / 2 + delta)
     (hYlower : N / 2 - delta ≤ (Y.card : ℝ))
     (hYupper : (Y.card : ℝ) ≤ N / 2 + delta)
     (hdense : N ^ 2 / 4 - eps * N ^ 2 ≤
       edgeCount (G.induce (S : Set V)) X Y)
     (hgap : 0 < N / 5 - delta)
     (hlowNumeric : delta * N + delta ^ 2 + eps * N ^ 2 <
       ((ell + 1 : ℕ) : ℝ) * (N / 5 - delta))
     (hsizeLeft : 2 * (X.card - Y.card) + 2 * ell + 1 ≤ t)
     (hsizeRight : 2 * (Y.card - X.card) + 2 * ell + 1 ≤ t)
     (hd : (d : ℝ) ≤ 3 * N / 10)
     (hminCross : ∀ v, 3 * t ≤
       (crossNeighbors (G.induce (S : Set V)) X Y v).card)
     (hfirst : 10 * t < d + 1)
     (hcommon : max X.card Y.card + 9 * t + 1 < 2 * (d + 1))
     (hclose : max X.card Y.card + 2 + 2 * (9 * t + 1) ≤
       2 * (d + 1)) : IsSpannedByCycle G S := by
   apply (isSpannedByCycle_iff_isHamiltonian hS).2
   exact IsKGoodCut.isHamiltonian_of_dense_crossing hgood anchor hN hdelta
     hXlower hXupper hYlower hYupper hdense hgap hlowNumeric hsizeLeft
     hsizeRight hd hminCross hfirst hcommon hclose (by simpa using hS)

 end Erdos622.GoodCutHamiltonicity
