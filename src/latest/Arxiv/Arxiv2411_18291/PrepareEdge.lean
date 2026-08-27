import Arxiv.Arxiv2411_18291.AttachmentGeometry
import Arxiv.Arxiv2411_18291.CrossSimpleGluing
import Arxiv.Arxiv2411_18291.PreparedProtection

/-! # Preparing one new edge by two actual seed attachments -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {q r : ℕ} {ι : Type*} [DecidableEq ι]

omit [DecidableEq V] in
theorem card_gluedVertex_le (Q : Finset W) :
    Fintype.card (GluedVertex V W Q) ≤ Fintype.card V + Fintype.card W := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add_left
    (Fintype.card_le_of_injective Subtype.val Subtype.val_injective) _

/-- The inductive construction step: prepare one new edge, preserve all old
prepared edges, and add at most two seed copies worth of edges and vertices. -/
theorem exists_prepare_edge_with_vertex_bound (S : ExchangeSystem V q r) (E : ExchangeSeed W q r)
    (hr : 0 < r) (hqr : r < q) {s : Finset ι} {edge : ι → Block V r}
    (P : PreparedFamily S.graph S.negative S.base s edge) (hinj : Function.Injective edge)
    (j : ι) (hj : j ∉ s) (hjB : (edge j).val ⊆ S.base.val) :
    ∃ T : FiniteExchangeSystem q r, ∃ f : V ↪ T.Vertex,
      T.system.base = mapBlock f S.base ∧
      (∃ P' : PreparedFamily T.system.graph T.system.negative T.system.base
        (insert j s) (fun i => mapBlock f (edge i)),
        P.Protects S.positive → P'.Protects T.system.positive) ∧
      T.system.graph.card ≤ S.graph.card + 2 * E.graph.card ∧
      (IsCrossSimple r S.positive S.negative → IsCrossSimple r E.positive E.negative →
        IsCrossSimple r T.system.positive T.system.negative) ∧
      Fintype.card T.Vertex ≤ Fintype.card V + 2 * Fintype.card W := by
  have heG : edge j ∈ S.graph := S.positive_decomposition.clique_subset S.base_mem
    ((mem_cliqueEdges (edge j) S.base).mpr hjB)
  obtain ⟨C, ⟨hC, hjC⟩, _⟩ := S.negative_decomposition.unique heG
  obtain ⟨σ₁, hσ₁⟩ := exists_glue_bijection C E.positiveClique (edge j) E.commonEdge
    hjC E.common_subset_positive
  let l₁ := glueLeft (V := V) E.positiveClique.val
  let a₁ := glueRight C E.positiveClique σ₁
  let S₁ := S.glue E hr hqr.le C hC σ₁
  let P₁ : PreparedFamily S₁.graph S₁.negative S₁.base s
      (fun i => mapBlock l₁ (edge i)) :=
    P.glue hqr C E.positiveClique σ₁ E.graph E.negative
      (P.avoids_interface hinj hj hjB hC hjC)
  let C₁ := mapBlock a₁ E.negativeClique
  have hC₁ : C₁ ∈ S₁.negative := S.glue_negative_mem E hr hqr.le C hC σ₁
  have hjC₁ : (mapBlock l₁ (edge j)).val ⊆ C₁.val :=
    seed_attachment_contains E C σ₁ (edge j) hσ₁
  have hjB₁ : (mapBlock l₁ (edge j)).val ⊆ S₁.base.val :=
    (mapBlock_subset_mapBlock l₁ _ _).mpr hjB
  obtain ⟨σ₂, hσ₂⟩ := exists_glue_bijection C₁ E.positiveClique
    (mapBlock l₁ (edge j)) E.commonEdge hjC₁ E.common_subset_positive
  let l₂ := glueLeft (V := GluedVertex V W E.positiveClique.val) E.positiveClique.val
  let a₂ := glueRight C₁ E.positiveClique σ₂
  let S₂ := S₁.glue E hr hqr.le C₁ hC₁ σ₂
  let P₂ : PreparedFamily S₂.graph S₂.negative S₂.base s
      (fun i => mapBlock l₂ (mapBlock l₁ (edge i))) :=
    P₁.glue hqr C₁ E.positiveClique σ₂ E.graph E.negative
      (P₁.avoids_interface ((mapBlock_injective l₁).comp hinj) hj hjB₁ hC₁ hjC₁)
  let N := mapBlock a₂ E.negativeClique
  let R : Finset (GluedVertex (GluedVertex V W E.positiveClique.val)
      W E.positiveClique.val) := univ.map a₂
  let U := (univ.map l₁).map l₂
  have hN : N ∈ S₂.negative := S₁.glue_negative_mem E hr hqr.le C₁ hC₁ σ₂
  have hjN : (mapBlock l₂ (mapBlock l₁ (edge j))).val ⊆ N.val :=
    seed_attachment_contains E C₁ σ₂ (mapBlock l₁ (edge j)) hσ₂
  have hNR : N.val ⊆ R := map_subset_map.mpr (subset_univ E.negativeClique.val)
  have hRU : R ∩ U = (mapBlock l₂ (mapBlock l₁ (edge j))).val := by
    calc
      R ∩ U = (E.commonEdge.val.map a₁).map l₂ :=
        two_glues_inter_old C E.positiveClique E.negativeClique σ₁ E.commonEdge
          (by rw [inter_comm, E.vertex_inter]) E.positiveClique σ₂
      _ = _ := by
        have h := congrArg Subtype.val hσ₁
        change E.commonEdge.val.map a₁ = (edge j).val.map l₁ at h
        rw [h]
        rfl
  have hjB₂ : (mapBlock l₂ (mapBlock l₁ (edge j))).val ⊆ S₂.base.val :=
    (mapBlock_subset_mapBlock l₂ _ _).mpr hjB₁
  have hBU : S₂.base.val ⊆ U :=
    map_subset_map.mpr (map_subset_map.mpr (subset_univ S.base.val))
  have hRB : R ∩ S₂.base.val = (mapBlock l₂ (mapBlock l₁ (edge j))).val :=
    inter_eq_of_between R U S₂.base.val _ hRU hBU hjB₂
  have hregions : ∀ i ∈ s, P₂.region i ⊆ U := by
    intro i _
    exact map_subset_map.mpr (map_subset_map.mpr (subset_univ (P.region i)))
  have hfresh : R ∩ U ⊆ S₂.base.val := by rw [hRU]; exact hjB₂
  have hNold : N.val ∩ univ.map l₂ = (mapBlock l₂ (mapBlock l₁ (edge j))).val :=
    seed_attachment_inter_old E C₁ σ₂ (mapBlock l₁ (edge j)) hσ₂
  have hOldAvoid : Disjoint (univ.map l₂) (N.val \ S₂.base.val) :=
    disjoint_private_of_inter_subset N.val _ S₂.base.val (by rw [hNold]; exact hjB₂)
  have hlocalE : ∀ e ∈ S₂.graph, ¬Disjoint e.val (N.val \ S₂.base.val) → e.val ⊆ R := by
    intro e he hcontact
    exact glued_family_local C₁ E.positiveClique σ₂ S₁.graph E.graph
      (N.val \ S₂.base.val) hOldAvoid e he hcontact
  have hlocalD : ∀ Q ∈ S₂.negative, ¬Disjoint Q.val (N.val \ S₂.base.val) → Q.val ⊆ R := by
    intro Q hQ hcontact
    have hmem : Q ∈ mapGraph l₂ S₁.negative ∪ mapGraph a₂ E.negative := by
      rcases mem_union.mp hQ with hQ | hQ
      · exact mem_union.mpr (Or.inr hQ)
      · exact mem_union.mpr (Or.inl (mem_erase.mp hQ).2)
    exact glued_family_local C₁ E.positiveClique σ₂ S₁.negative E.negative
      (N.val \ S₂.base.val) hOldAvoid Q hmem hcontact
  have hlocalP : ∀ Q ∈ S₂.positive, ¬Disjoint Q.val (N.val \ S₂.base.val) → Q.val ⊆ R := by
    intro Q hQ hcontact
    have hmem : Q ∈ mapGraph l₂ S₁.positive ∪ mapGraph a₂ E.positive := by
      rcases mem_union.mp hQ with hQ | hQ
      · exact mem_union_left _ hQ
      · exact mem_union_right _ (mem_erase.mp hQ).2
    exact glued_family_local C₁ E.positiveClique σ₂ S₁.positive E.positive
      (N.val \ S₂.base.val) hOldAvoid Q hmem hcontact
  let P₃ := P₂.insert_fresh j hj N R U hN hjN hNR hRB hregions hfresh hlocalE hlocalD
  have hprotect : P.Protects S.positive → P₃.Protects S₂.positive := by
    intro hP
    have hP₁ : P₁.Protects S₁.positive := hP.glue hqr C E.positiveClique σ₁
      E.graph E.negative E.positive (P.avoids_interface hinj hj hjB hC hjC)
    have hP₂ : P₂.Protects S₂.positive := hP₁.glue hqr C₁ E.positiveClique σ₂
      E.graph E.negative E.positive
      (P₁.avoids_interface ((mapBlock_injective l₁).comp hinj) hj hjB₁ hC₁ hjC₁)
    exact hP₂.insert_fresh j hj N R U hN hjN hNR hRB hregions hfresh hlocalE hlocalD hlocalP
  refine ⟨S₂.toFinite, l₁.trans l₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact mapBlock_map l₁ l₂ S.base
  · change ∃ P' : PreparedFamily S₂.graph S₂.negative S₂.base
      (insert j s) (fun i => mapBlock (l₁.trans l₂) (edge i)),
      P.Protects S.positive → P'.Protects S₂.positive
    have hw : ∃ P' : PreparedFamily S₂.graph S₂.negative S₂.base
        (insert j s) (fun i => mapBlock l₂ (mapBlock l₁ (edge i))),
        P.Protects S.positive → P'.Protects S₂.positive := ⟨P₃, hprotect⟩
    have heq : (fun i => mapBlock l₂ (mapBlock l₁ (edge i))) =
        (fun i => mapBlock (l₁.trans l₂) (edge i)) := funext fun i => mapBlock_map l₁ l₂ (edge i)
    exact (congrArg (fun edge' => ∃ P' : PreparedFamily S₂.graph S₂.negative S₂.base
      (insert j s) edge', P.Protects S.positive → P'.Protects S₂.positive) heq).mp hw
  · have h₁ := S.glue_card_le E hr hqr.le C hC σ₁
    have h₂ := S₁.glue_card_le E hr hqr.le C₁ hC₁ σ₂
    change S₁.graph.card ≤ S.graph.card + E.graph.card at h₁
    change S₂.graph.card ≤ S₁.graph.card + E.graph.card at h₂
    change S₂.graph.card ≤ S.graph.card + 2 * E.graph.card
    omega
  · intro hS hE
    exact S₁.glue_crossSimple E hr hqr.le C₁ hC₁ σ₂
      (S.glue_crossSimple E hr hqr.le C hC σ₁ hS hE) hE
  · have h₁ := card_gluedVertex_le (V := V) E.positiveClique.val
    have h₂ := card_gluedVertex_le (V := GluedVertex V W E.positiveClique.val)
      E.positiveClique.val
    change Fintype.card (GluedVertex (GluedVertex V W E.positiveClique.val)
      W E.positiveClique.val) ≤ Fintype.card V + 2 * Fintype.card W
    omega

/-- The original edge-count interface to the stronger construction. -/
theorem exists_prepare_edge (S : ExchangeSystem V q r) (E : ExchangeSeed W q r)
    (hr : 0 < r) (hqr : r < q) {s : Finset ι} {edge : ι → Block V r}
    (P : PreparedFamily S.graph S.negative S.base s edge) (hinj : Function.Injective edge)
    (j : ι) (hj : j ∉ s) (hjB : (edge j).val ⊆ S.base.val) :
    ∃ T : FiniteExchangeSystem q r, ∃ f : V ↪ T.Vertex,
      T.system.base = mapBlock f S.base ∧
      (∃ P' : PreparedFamily T.system.graph T.system.negative T.system.base
        (insert j s) (fun i => mapBlock f (edge i)),
        P.Protects S.positive → P'.Protects T.system.positive) ∧
      T.system.graph.card ≤ S.graph.card + 2 * E.graph.card ∧
      (IsCrossSimple r S.positive S.negative → IsCrossSimple r E.positive E.negative →
        IsCrossSimple r T.system.positive T.system.negative) := by
  obtain ⟨T, f, hb, hp, hc, hs, _⟩ :=
    exists_prepare_edge_with_vertex_bound S E hr hqr P hinj j hj hjB
  exact ⟨T, f, hb, hp, hc, hs⟩

end Arxiv2411_18291
