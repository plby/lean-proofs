import Arxiv.Arxiv2411_18291.Relabeling
import Arxiv.Arxiv2411_18291.DecompositionGluing
import Mathlib.Data.Fintype.Sum

/-!
# Gluing the vertex sets along a clique

Use all vertices from the first graph and fresh copies of the second graph's
vertices outside the common clique. The two vertex maps are embeddings and
their ranges intersect precisely in the identified clique. Consequently the
two embedded hypergraphs intersect in precisely the common clique's edges.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} {q r : ℕ}

abbrev GluedVertex (V W : Type*) (Q : Finset W) := V ⊕ {w : W // w ∉ Q}

def glueLeft (Q : Finset W) : V ↪ GluedVertex V W Q :=
  ⟨Sum.inl, Sum.inl_injective⟩

variable [DecidableEq V] [DecidableEq W]

def glueRightFun (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    (w : W) : GluedVertex V W Q.val :=
  if hw : w ∈ Q.val then Sum.inl (σ ⟨w, hw⟩).val else Sum.inr ⟨w, hw⟩

omit [DecidableEq V] in
theorem glueRightFun_injective (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val) :
    Function.Injective (glueRightFun P Q σ) := by
  intro a b h
  by_cases ha : a ∈ Q.val <;> by_cases hb : b ∈ Q.val
  · simp only [glueRightFun, dif_pos ha, dif_pos hb, Sum.inl.injEq] at h
    exact congrArg Subtype.val (σ.injective (Subtype.ext h))
  · simp [glueRightFun, ha, hb] at h
  · simp [glueRightFun, ha, hb] at h
  · simp only [glueRightFun, dif_neg ha, dif_neg hb, Sum.inr.injEq] at h
    exact congrArg Subtype.val h

def glueRight (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val) :
    W ↪ GluedVertex V W Q.val := ⟨glueRightFun P Q σ, glueRightFun_injective P Q σ⟩

omit [DecidableEq V] in
theorem glueRight_of_mem (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    {w : W} (hw : w ∈ Q.val) : glueRight P Q σ w = Sum.inl (σ ⟨w, hw⟩).val := by
  change glueRightFun P Q σ w = _
  simp [glueRightFun, hw]

omit [DecidableEq V] in
theorem glue_common (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    {v : V} {w : W} (h : glueLeft Q.val v = glueRight P Q σ w) :
    v ∈ P.val ∧ w ∈ Q.val := by
  change Sum.inl v = glueRightFun P Q σ w at h
  by_cases hw : w ∈ Q.val
  · simp only [glueRightFun, dif_pos hw, Sum.inl.injEq] at h
    exact ⟨h.symm ▸ (σ ⟨w, hw⟩).property, hw⟩
  · simp [glueRightFun, hw] at h

omit [DecidableEq V] in
/-- The chosen bijection makes the two copies of the common clique equal. -/
theorem glue_clique (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val) :
    mapBlock (glueRight P Q σ) Q = mapBlock (glueLeft Q.val) P := by
  apply Subtype.ext
  ext z
  change z ∈ Q.val.map (glueRight P Q σ) ↔ z ∈ P.val.map (glueLeft Q.val)
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
    rw [glueRight_of_mem P Q σ hw]
    exact mem_map.mpr ⟨(σ ⟨w, hw⟩).val, (σ ⟨w, hw⟩).property, rfl⟩
  · intro hz
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hz
    let w := σ.symm ⟨v, hv⟩
    refine mem_map.mpr ⟨w.val, w.property, ?_⟩
    rw [glueRight_of_mem P Q σ w.property]
    change Sum.inl (σ (σ.symm ⟨v, hv⟩)).val = Sum.inl v
    rw [σ.apply_symm_apply]

variable [Fintype V] [Fintype W]

omit [DecidableEq V] [Fintype V] in
/-- A vertex of the old graph lies in the attached copy exactly when it is
in the common clique. -/
theorem glueLeft_mem_right_range (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    (v : V) : glueLeft Q.val v ∈ univ.map (glueRight P Q σ) ↔ v ∈ P.val := by
  constructor
  · intro h
    obtain ⟨w, _, hw⟩ := mem_map.mp h
    exact (glue_common P Q σ hw.symm).1
  · intro hv
    have hcl : glueLeft Q.val v ∈ (mapBlock (glueRight P Q σ) Q).val := by
      rw [glue_clique P Q σ]
      exact mem_map.mpr ⟨v, hv, rfl⟩
    exact (map_subset_map.mpr (subset_univ Q.val)) hcl

omit [Fintype V] in
/-- Intersection of the attached copy with any set of old vertices. -/
theorem glue_copy_inter_left (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    (T : Finset V) :
    univ.map (glueRight P Q σ) ∩ T.map (glueLeft Q.val) =
      (P.val ∩ T).map (glueLeft Q.val) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzR, hzT⟩ := mem_inter.mp hz
    obtain ⟨v, hvT, rfl⟩ := mem_map.mp hzT
    have hvP := (glueLeft_mem_right_range P Q σ v).mp hzR
    exact mem_map.mpr ⟨v, mem_inter.mpr ⟨hvP, hvT⟩, rfl⟩
  · intro hz
    obtain ⟨v, hv, rfl⟩ := mem_map.mp hz
    obtain ⟨hvP, hvT⟩ := mem_inter.mp hv
    exact mem_inter.mpr ⟨(glueLeft_mem_right_range P Q σ v).mpr hvP,
      mem_map.mpr ⟨v, hvT, rfl⟩⟩

omit [Fintype W] in
/-- An attached vertex set meets the old graph only in its part of the
gluing clique. -/
theorem glue_right_inter_old (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    (S : Finset W) :
    S.map (glueRight P Q σ) ∩ univ.map (glueLeft Q.val) =
      (S ∩ Q.val).map (glueRight P Q σ) := by
  ext z
  constructor
  · intro hz
    obtain ⟨hzS, hzV⟩ := mem_inter.mp hz
    obtain ⟨w, hwS, rfl⟩ := mem_map.mp hzS
    obtain ⟨v, _, hv⟩ := mem_map.mp hzV
    exact mem_map.mpr ⟨w, mem_inter.mpr ⟨hwS, (glue_common P Q σ hv).2⟩, rfl⟩
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
    obtain ⟨hwS, hwQ⟩ := mem_inter.mp hw
    refine mem_inter.mpr ⟨mem_map.mpr ⟨w, hwS, rfl⟩, ?_⟩
    rw [glueRight_of_mem P Q σ hwQ]
    exact mem_map.mpr ⟨(σ ⟨w, hwQ⟩).val, mem_univ _, rfl⟩

/-- The vertex gluing creates no extra common edges. -/
theorem glued_graph_intersection (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    (G : Hypergraph V r) (H : Hypergraph W r)
    (hPG : cliqueEdges r P ⊆ G) (hQH : cliqueEdges r Q ⊆ H) :
    mapGraph (glueLeft Q.val) G ∩ mapGraph (glueRight P Q σ) H =
      cliqueEdges r (mapBlock (glueLeft Q.val) P) := by
  have hleft : cliqueEdges r (mapBlock (glueLeft Q.val) P) ⊆ mapGraph (glueLeft Q.val) G := by
    rw [← map_cliqueEdges]
    exact mapGraph_mono _ hPG
  have hright : cliqueEdges r (mapBlock (glueLeft Q.val) P) ⊆ mapGraph (glueRight P Q σ) H := by
    rw [← glue_clique P Q σ, ← map_cliqueEdges]
    exact mapGraph_mono _ hQH
  apply subset_antisymm
  · intro e he
    obtain ⟨heG, heH⟩ := mem_inter.mp he
    obtain ⟨a, _, rfl⟩ := (mem_mapGraph _ G e).mp heG
    obtain ⟨b, _, hba⟩ := (mem_mapGraph _ H _).mp heH
    rw [mem_cliqueEdges, mapBlock_subset_mapBlock]
    intro v hv
    have hz : glueLeft Q.val v ∈ (mapBlock (glueRight P Q σ) b).val := by
      rw [hba]
      exact mem_map.mpr ⟨v, hv, rfl⟩
    obtain ⟨w, _, hw⟩ := mem_map.mp hz
    exact (glue_common P Q σ hw.symm).1
  · intro e he
    exact mem_inter.mpr ⟨hleft he, hright he⟩

/-- Gluing along any chosen bijection preserves both decompositions. -/
theorem vertex_glue_two_decompositions (hqr : r ≤ q)
    (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    {G : Hypergraph V r} {H : Hypergraph W r}
    {Dp Dn : Finset (Block V q)} {Ep En : Finset (Block W q)}
    (hDp : IsDecomposition G Dp) (hDn : IsDecomposition G Dn)
    (hEp : IsDecomposition H Ep) (hEn : IsDecomposition H En)
    (hP : P ∈ Dn) (hQ : Q ∈ Ep) :
    let l := glueLeft (V := V) Q.val
    let s := glueRight P Q σ
    let K := mapBlock l P
    IsDecomposition (mapGraph l G ∪ mapGraph s H)
      (mapGraph l Dp ∪ (mapGraph s Ep).erase K) ∧
    IsDecomposition (mapGraph l G ∪ mapGraph s H)
      (mapGraph s En ∪ (mapGraph l Dn).erase K) := by
  dsimp only
  apply glue_two_decompositions hqr (hDp.map _) (hDn.map _) (hEp.map _) (hEn.map _)
  · exact (mem_mapGraph _ Dn _).mpr ⟨P, hP, rfl⟩
  · exact (mem_mapGraph _ Ep _).mpr ⟨Q, hQ, glue_clique P Q σ⟩
  · exact glued_graph_intersection P Q σ G H (hDn.clique_subset hP) (hEp.clique_subset hQ)

/-- Exact edge accounting for a gluing: only the common clique is counted twice. -/
theorem glued_graph_card_add (P : Block V q) (Q : Block W q) (σ : Q.val ≃ P.val)
    (G : Hypergraph V r) (H : Hypergraph W r)
    (hPG : cliqueEdges r P ⊆ G) (hQH : cliqueEdges r Q ⊆ H) :
    (mapGraph (glueLeft Q.val) G ∪ mapGraph (glueRight P Q σ) H).card + q.choose r =
      G.card + H.card := by
  have h := card_union_add_card_inter
    (mapGraph (glueLeft Q.val) G) (mapGraph (glueRight P Q σ) H)
  rwa [glued_graph_intersection P Q σ G H hPG hQH, card_cliqueEdges,
    card_mapGraph, card_mapGraph] at h

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

omit [Fintype W] in
/-- After two gluings, the last attached copy meets the original vertex set
only in the image of the common edge. This is the separation calculation in
the proof of `lem:OO`; preservation through all later rounds is separate. -/
theorem two_glues_inter_old (P : Block V q) (Q R : Block W q)
    (σ : Q.val ≃ P.val) (e : Block W r) (hRQ : R.val ∩ Q.val = e.val)
    (S : Block Z q) (τ : S.val ≃ (mapBlock (glueRight P Q σ) R).val) :
    univ.map (glueRight (mapBlock (glueRight P Q σ) R) S τ) ∩
        (univ.map (glueLeft (V := V) Q.val)).map (glueLeft S.val) =
      (e.val.map (glueRight P Q σ)).map (glueLeft S.val) := by
  rw [glue_copy_inter_left]
  change ((R.val.map (glueRight P Q σ)) ∩ univ.map (glueLeft Q.val)).map (glueLeft S.val) = _
  rw [glue_right_inter_old, hRQ]

end Arxiv2411_18291
