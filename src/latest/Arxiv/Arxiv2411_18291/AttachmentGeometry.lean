import Arxiv.Arxiv2411_18291.ExchangeSystem

/-! # The fresh region and clique produced by an attachment -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {q r k : ℕ}

theorem ExchangeSeed.common_subset_positive (E : ExchangeSeed W q r) :
    E.commonEdge.val ⊆ E.positiveClique.val := by
  rw [← E.vertex_inter]
  exact inter_subset_left

theorem ExchangeSeed.common_subset_negative (E : ExchangeSeed W q r) :
    E.commonEdge.val ⊆ E.negativeClique.val := by
  rw [← E.vertex_inter]
  exact inter_subset_right

omit [Fintype V] [DecidableEq V] in
theorem seed_attachment_contains (E : ExchangeSeed W q r) (C : Block V q)
    (σ : E.positiveClique.val ≃ C.val) (e : Block V r)
    (halign : mapBlock (glueRight C E.positiveClique σ) E.commonEdge =
      mapBlock (glueLeft E.positiveClique.val) e) :
    (mapBlock (glueLeft E.positiveClique.val) e).val ⊆
      (mapBlock (glueRight C E.positiveClique σ) E.negativeClique).val := by
  rw [← halign, mapBlock_subset_mapBlock]
  exact E.common_subset_negative

theorem seed_attachment_inter_old (E : ExchangeSeed W q r) (C : Block V q)
    (σ : E.positiveClique.val ≃ C.val) (e : Block V r)
    (halign : mapBlock (glueRight C E.positiveClique σ) E.commonEdge =
      mapBlock (glueLeft E.positiveClique.val) e) :
    (mapBlock (glueRight C E.positiveClique σ) E.negativeClique).val ∩
        univ.map (glueLeft E.positiveClique.val) =
      (mapBlock (glueLeft E.positiveClique.val) e).val := by
  change E.negativeClique.val.map (glueRight C E.positiveClique σ) ∩ _ = _
  rw [glue_right_inter_old, inter_comm E.negativeClique.val, E.vertex_inter]
  exact congrArg Subtype.val halign

omit [Fintype V] [Fintype W] [DecidableEq W] in
theorem disjoint_private_of_inter_subset (N U B : Finset V) (h : N ∩ U ⊆ B) :
    Disjoint U (N \ B) := by
  apply Finset.disjoint_left.mpr
  intro v hvU hvN
  exact (mem_sdiff.mp hvN).2 (h (mem_inter.mpr ⟨(mem_sdiff.mp hvN).1, hvU⟩))

omit [Fintype V] [Fintype W] [DecidableEq W] in
theorem inter_eq_of_between (R U B e : Finset V) (hRU : R ∩ U = e)
    (hBU : B ⊆ U) (heB : e ⊆ B) : R ∩ B = e := by
  apply subset_antisymm
  · intro v hv
    rw [← hRU]
    exact mem_inter.mpr ⟨(mem_inter.mp hv).1, hBU (mem_inter.mp hv).2⟩
  · intro v hv
    have hvR : v ∈ R := by rw [← hRU] at hv; exact (mem_inter.mp hv).1
    exact mem_inter.mpr ⟨hvR, heB hv⟩

/-- In a union of old and attached families, a member touching a set disjoint
from all old vertices must lie wholly in the attached copy. -/
theorem glued_family_local (C : Block V q) (Q : Block W q) (σ : Q.val ≃ C.val)
    (A : Finset (Block V k)) (D : Finset (Block W k))
    (T : Finset (GluedVertex V W Q.val)) (hold : Disjoint (univ.map (glueLeft Q.val)) T)
    (K : Block (GluedVertex V W Q.val) k)
    (hK : K ∈ mapGraph (glueLeft Q.val) A ∪ mapGraph (glueRight C Q σ) D)
    (hcontact : ¬Disjoint K.val T) : K.val ⊆ univ.map (glueRight C Q σ) := by
  rcases mem_union.mp hK with hK | hK
  · obtain ⟨J, _, rfl⟩ := (mem_mapGraph _ A K).mp hK
    exact (hcontact (disjoint_of_subset_left (map_subset_map.mpr (subset_univ J.val)) hold)).elim
  · obtain ⟨J, _, rfl⟩ := (mem_mapGraph _ D K).mp hK
    exact map_subset_map.mpr (subset_univ J.val)

end Arxiv2411_18291
