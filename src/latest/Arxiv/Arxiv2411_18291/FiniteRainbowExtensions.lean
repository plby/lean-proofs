import Arxiv.Arxiv2411_18291.FiniteColouredExtensions
import Arxiv.Arxiv2411_18291.TypicalRainbowExtensions
import Arxiv.Arxiv2411_18291.ExplicitBoostSize

/-! # Actual simultaneous rainbow extensions at the printed threshold -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem exists_many_rainbow_extensions_paper_threshold {W : Type*} [Fintype W]
    {q r n h : ℕ} (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (F : Finset W)
    (E : Hypergraph W (r + 1)) (hEh : E.card ≤ h) (hroot : ∀ e ∈ E, ¬e.val ⊆ F)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card) :
    ∃ σ : Option (Fin (paperColourTrialCount q (r + 1) F.card) × E) → Equiv.Perm (Fin n),
      ∀ φ : F ↪ Fin n,
        (3 / 8 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
          (rainbowExtensions φ E σ G).card := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hnsize := paper_small_carrier_completion_size hqr hn hw
  have hroot' : ∀ e ∈ (univ : Finset E), (e.val.val ∩ F).card < r + 1 :=
    fun e _ => block_root_inter_card_lt e.val (hroot e.val e.property)
  have hsize (φ : F ↪ Fin n) : (3 / 4 : ℝ) *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤ (univ : Finset (EmbeddingExtension φ)).card := by
    simpa only [card_univ, Fintype.card_fin] using card_embeddingExtension_three_quarters φ
      (by simpa only [Fintype.card_fin] using hnsize)
  obtain ⟨ω, hω⟩ := uniform_coloured_extensions_paper_threshold hqr hn hqh hH F hw
    univ (fun e : E => e.val) (by simpa only [card_univ, Fintype.card_coe] using hEh)
    hroot' K G hT hd hGK hloss (fun _ => univ) hsize
  refine ⟨groupedPermutation ω, fun φ => ?_⟩
  obtain ⟨j, hj⟩ := hω φ
  simp only [card_univ, Fintype.card_coe] at hj
  have hs := hsize φ
  rw [card_univ] at hs
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg (density_nonneg G) E.card)
  have hmean : (3 / 8 : ℝ) * density G ^ E.card *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤
        (Fintype.card (EmbeddingExtension φ) : ℝ) * density G ^ E.card / 2 := by
    nlinarith only [hm]
  exact (hmean.trans_lt hj).trans_le (extensionColourCount_le_rainbow_card φ E G ω j)

end Arxiv2411_18291
