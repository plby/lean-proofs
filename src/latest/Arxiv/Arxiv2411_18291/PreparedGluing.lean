import Arxiv.Arxiv2411_18291.PreparedFamily

/-! # A gluing preserves previously prepared private vertices -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} [DecidableEq V] [DecidableEq W] {q r : ℕ}

omit [DecidableEq V] in
/-- A new copy cannot touch an old set avoided by its attachment interface. -/
theorem glue_right_disjoint_left (C : Block V q) (Q : Block W q) (σ : Q.val ≃ C.val)
    (S : Finset W) (T : Finset V) (hCT : Disjoint C.val T) :
    Disjoint (S.map (glueRight C Q σ)) (T.map (glueLeft Q.val)) := by
  apply Finset.disjoint_left.mpr
  intro z hzS hzT
  obtain ⟨w, _, rfl⟩ := mem_map.mp hzS
  obtain ⟨v, hvT, hvw⟩ := mem_map.mp hzT
  exact Finset.disjoint_left.mp hCT (glue_common C Q σ hvw).1 hvT

variable {ι : Type*}

namespace PreparedFamily

variable {G : Hypergraph V r} {D : Finset (Block V q)} {B : Block V q}
variable {s : Finset ι} {edge : ι → Block V r}

/-- Attach an arbitrary graph and negative family along an interface avoiding
the prepared private sets. The old prepared cliques and regions survive. -/
def glue (P : PreparedFamily G D B s edge) (hqr : r < q)
    (C : Block V q) (Q : Block W q) (σ : Q.val ≃ C.val)
    (H : Hypergraph W r) (N : Finset (Block W q))
    (havoid : ∀ i ∈ s, Disjoint C.val ((P.clique i).val \ B.val)) :
    PreparedFamily
      (mapGraph (glueLeft Q.val) G ∪ mapGraph (glueRight C Q σ) H)
      (mapGraph (glueRight C Q σ) N ∪ (mapGraph (glueLeft Q.val) D).erase
        (mapBlock (glueLeft Q.val) C))
      (mapBlock (glueLeft Q.val) B) s (fun i => mapBlock (glueLeft Q.val) (edge i)) where
  clique := fun i => mapBlock (glueLeft Q.val) (P.clique i)
  region := fun i => (P.region i).map (glueLeft Q.val)
  clique_mem := by
    intro i hi
    have hne : P.clique i ≠ C := by
      intro h
      obtain ⟨v, hv⟩ := P.private_nonempty hqr hi
      exact Finset.disjoint_left.mp (havoid i hi) (h ▸ (mem_sdiff.mp hv).1) hv
    apply mem_union.mpr
    apply Or.inr
    apply mem_erase.mpr
    exact ⟨(mapBlock_injective (glueLeft Q.val)).ne hne,
      (mem_mapGraph _ D _).mpr ⟨P.clique i, P.clique_mem i hi, rfl⟩⟩
  edge_subset := (P.map (glueLeft Q.val)).edge_subset
  clique_subset := (P.map (glueLeft Q.val)).clique_subset
  region_base := (P.map (glueLeft Q.val)).region_base
  separated := (P.map (glueLeft Q.val)).separated
  edge_local := by
    intro i hi e he hcontact
    rcases mem_union.mp he with he | he
    · exact (P.map (glueLeft Q.val)).edge_local i hi e he hcontact
    · obtain ⟨a, _, rfl⟩ := (mem_mapGraph _ H e).mp he
      apply (hcontact ?_).elim
      change Disjoint (a.val.map (glueRight C Q σ))
        ((P.clique i).val.map (glueLeft Q.val) \ B.val.map (glueLeft Q.val))
      rw [← map_sdiff]
      exact glue_right_disjoint_left C Q σ a.val _ (havoid i hi)
  clique_local := by
    intro i hi R hR hcontact
    rcases mem_union.mp hR with hR | hR
    · obtain ⟨A, _, rfl⟩ := (mem_mapGraph _ N R).mp hR
      apply (hcontact ?_).elim
      change Disjoint (A.val.map (glueRight C Q σ))
        ((P.clique i).val.map (glueLeft Q.val) \ B.val.map (glueLeft Q.val))
      rw [← map_sdiff]
      exact glue_right_disjoint_left C Q σ A.val _ (havoid i hi)
    · exact (P.map (glueLeft Q.val)).clique_local i hi R (mem_erase.mp hR).2 hcontact

end PreparedFamily

end Arxiv2411_18291
