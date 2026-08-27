import Arxiv.Arxiv2411_18291.ExchangeSystem
import Arxiv.Arxiv2411_18291.PolynomialExchangeSeed
import Arxiv.Arxiv2411_18291.CliqueIntersections

/-!
# Gluing preserves small opposite-clique intersections

Within either copy the intersection bound is inherited. Between copies,
all common vertices lie in the gluing clique. The surviving positive
cliques of the attached copy are edge-disjoint from that clique.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {q r : ℕ}

theorem ExchangeSystem.glue_crossSimple (S : ExchangeSystem V q r) (E : ExchangeSeed W q r)
    (hr : 0 < r) (hqr : r ≤ q) (C : Block V q) (hC : C ∈ S.negative)
    (σ : E.positiveClique.val ≃ C.val)
    (hS : IsCrossSimple r S.positive S.negative)
    (hE : IsCrossSimple r E.positive E.negative) :
    IsCrossSimple r (S.glue E hr hqr C hC σ).positive
      (S.glue E hr hqr C hC σ).negative := by
  intro P hP Q hQ
  rcases mem_union.mp hP with hPL | hPR <;> rcases mem_union.mp hQ with hQR | hQL
  · obtain ⟨P₀, hP₀, rfl⟩ := (mem_mapGraph _ _ _).mp hPL
    obtain ⟨Q₀, _, rfl⟩ := (mem_mapGraph _ _ _).mp hQR
    change (P₀.val.map (glueLeft E.positiveClique.val) ∩
      Q₀.val.map (glueRight C E.positiveClique σ)).card ≤ r
    calc
      _ ≤ (univ.map (glueRight C E.positiveClique σ) ∩
          P₀.val.map (glueLeft E.positiveClique.val)).card := by
        apply card_le_card
        intro v hv
        exact mem_inter.mpr
          ⟨(map_subset_map.mpr (subset_univ Q₀.val)) (mem_inter.mp hv).2, (mem_inter.mp hv).1⟩
      _ = (C.val ∩ P₀.val).card := by rw [glue_copy_inter_left, card_map]
      _ ≤ r := by rw [inter_comm]; exact hS P₀ hP₀ C hC
  · exact hS.map (glueLeft E.positiveClique.val) P hPL Q (mem_erase.mp hQL).2
  · exact hE.map (glueRight C E.positiveClique σ) P (mem_erase.mp hPR).2 Q hQR
  · obtain ⟨P₀, hP₀, rfl⟩ := (mem_mapGraph _ _ _).mp (mem_erase.mp hPR).2
    obtain ⟨Q₀, _, rfl⟩ := (mem_mapGraph _ _ _).mp (mem_erase.mp hQL).2
    have hPne : P₀ ≠ E.positiveClique := by
      intro h
      apply (mem_erase.mp hPR).1
      rw [h, glue_clique]
    change (P₀.val.map (glueRight C E.positiveClique σ) ∩
      Q₀.val.map (glueLeft E.positiveClique.val)).card ≤ r
    calc
      _ ≤ (P₀.val.map (glueRight C E.positiveClique σ) ∩
          univ.map (glueLeft E.positiveClique.val)).card :=
        card_le_card (inter_subset_inter Subset.rfl (map_subset_map.mpr (subset_univ Q₀.val)))
      _ = (P₀.val ∩ E.positiveClique.val).card := by rw [glue_right_inter_old, card_map]
      _ ≤ r := (E.positive_decomposition.clique_inter_card_lt hP₀ E.positive_mem hPne).le

end Arxiv2411_18291
