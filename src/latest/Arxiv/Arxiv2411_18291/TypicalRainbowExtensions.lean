import Arxiv.Arxiv2411_18291.UniformColouredExtensions
import Arxiv.Arxiv2411_18291.TypicalGoodEdgeColours
import Arxiv.Arxiv2411_18291.RainbowExtensions

/-!
# Many rainbow extensions in permuted good subgraphs

All probability assumptions are discharged by typicality of the host and
a bound on the deleted edge fraction. The conclusion counts actual
root-preserving embeddings, with one colour family working for every root.
-/

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W]

theorem eventually_many_rainbow_extensions (F : Finset W) {r : ℕ}
    (E : Hypergraph W (r + 1)) (hroot : ∀ e ∈ E, ¬e.val ⊆ F) (h L : ℕ) (hh : 1 ≤ h)
    {b α δ τ γ χ κ : ℝ} (hb : 0 < b) (hκ : 0 < κ) (hκγ : κ < γ) (hγχ : γ < χ)
    (hχδ : χ < δ) (hχ1 : χ < 1) (hγτ : γ < τ)
    (hgap : 2 * α * E.card + κ < 1) (hhost : α + δ < 1) (hL : (F.card : ℝ) < κ * L) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h → b * (n : ℝ) ^ (-α) ≤ density K →
      ∀ G : Hypergraph (Fin n) (r + 1), G ⊆ K →
      ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-τ) * K.card →
      ∃ σ : Option (Fin L × E) → Equiv.Perm (Fin n), ∀ φ : F ↪ Fin n,
        (3 / 8 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
          (rainbowExtensions φ E σ G).card := by
  classical
  have hroot' : ∀ e ∈ (univ : Finset E), (e.val.val ∩ F).card < r + 1 :=
    fun e _ => block_root_inter_card_lt e.val (hroot e.val e.property)
  have hgap' : (0 : ℝ) + 2 * α * (univ : Finset E).card + κ < 1 := by
    simpa only [zero_add, card_univ, Fintype.card_coe] using hgap
  filter_upwards [eventually_uniform_coloured_extensions F univ (fun e : E => e.val)
    (r + 1) L hroot' (b := b / 2) (c := 3 / 4) (a := 0) (by positivity) (by norm_num)
      hκ hκγ hgap' hL,
    eventually_good_edge_colour_estimates r h hh hb (hκ.trans hκγ) hγχ hχδ hχ1 hγτ hhost,
    eventually_ge_atTop (4 * (Fintype.card W) ^ 2)] with n hcol hgood hn
  intro K hT hd G hGK hloss
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hG := hgood K hT hd G hGK hloss
  have hsize (φ : F ↪ Fin n) :
      (3 / 4 : ℝ) * (n : ℝ) ^ (Fintype.card W - F.card) ≤
        (Fintype.card (EmbeddingExtension φ) : ℝ) := by
    simpa only [Fintype.card_fin] using card_embeddingExtension_three_quarters φ
      (by simpa only [Fintype.card_fin] using hn)
  have hsize' (φ : F ↪ Fin n) :
      ((3 / 4 : ℝ) * (n : ℝ) ^ (-(0 : ℝ))) *
        (n : ℝ) ^ (Fintype.card W - F.card) ≤ (univ : Finset (EmbeddingExtension φ)).card := by
    simpa only [neg_zero, Real.rpow_zero, mul_one, card_univ] using hsize φ
  obtain ⟨ω, hω⟩ := hcol (fun _ => univ) G (density K) (density_nonneg K)
    hsize' hG.1 hG.2.1 hG.2.2
  refine ⟨groupedPermutation ω, fun φ => ?_⟩
  obtain ⟨j, hj⟩ := hω φ
  simp only [card_univ, Fintype.card_coe] at hj
  have hmul := mul_le_mul_of_nonneg_right (hsize φ) (pow_nonneg (density_nonneg G) E.card)
  have hmean : (3 / 8 : ℝ) * density G ^ E.card *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤
        (Fintype.card (EmbeddingExtension φ) : ℝ) * density G ^ E.card / 2 := by
    nlinarith only [hmul]
  exact (hmean.trans_lt hj).trans_le (extensionColourCount_le_rainbow_card φ E G ω j)

end Arxiv2411_18291
