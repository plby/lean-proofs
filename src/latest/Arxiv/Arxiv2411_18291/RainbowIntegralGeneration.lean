import Arxiv.Arxiv2411_18291.RainbowCliqueResidual
import Arxiv.Arxiv2411_18291.CliqueResidualGeneration

/-!
# Integral generation on the colour graph

Choose one punctured rainbow reference clique through every edge. The
exchange residual identity then generates every integral boundary supported
on the colour graph: references outside that graph cancel by linearity.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r t : ℕ} {S : ExchangeSystem W q (r + 1)} {N : Block W q}
variable {σ : I → Equiv.Perm V} {G : Hypergraph V (r + 1)}

theorem RainbowAvoidingExtensionProperties.exists_punctured_clique
    (hE : RainbowAvoidingExtensionProperties S N σ G t)
    (C : Finset I) (hC : C.card ≤ t) (e : Block V (r + 1)) :
    ∃ Q : Block V q, e.val ⊆ Q.val ∧
      IsRainbowAvoiding (fun i => mapGraph (σ i).toEmbedding G)
        ((cliqueEdges (r + 1) Q).erase e) C := by
  classical
  have hd : 0 ≤ density G := density_nonneg G
  have hmain : 0 ≤ ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
      (Fintype.card V : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial := by positivity
  have hpos := hmain.trans_lt (hE.punctured C hC e)
  obtain ⟨Q, hQ⟩ := card_pos.mp (Nat.cast_pos.mp hpos)
  exact ⟨Q, (mem_filter.mp hQ).2⟩

theorem RainbowAvoidingExtensionProperties.exists_punctured_references
    (hE : RainbowAvoidingExtensionProperties S N σ G t) :
    ∃ R : Block V (r + 1) → Block V q, (∀ e, e.val ⊆ (R e).val) ∧
      ∀ e, IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
        ((cliqueEdges (r + 1) (R e)).erase e) := by
  have h (e : Block V (r + 1)) := hE.exists_punctured_clique ∅ (Nat.zero_le t) e
  choose R hRroot hRcol using h
  exact ⟨R, hRroot, fun e => (hRcol e).isRainbow⟩

omit [Fintype V] [DecidableEq V] in
theorem eventually_integral_coloured_generated_rainbow [Fintype I]
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A) (hqr : r + 1 < q)
    (hN : N ∈ S.negative) (ht : 2 * q.choose (r + 1) ≤ t)
    {b α : ℝ} (hb : 0 < b) (hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      b * (n : ℝ) ^ (-α) ≤ density G → ∀ σ : I → Equiv.Perm (Fin n),
      RainbowAvoidingExtensionProperties S N σ G t →
      ∀ J : Block (Fin n) (r + 1) → ℤ, IntegrallyDecomposable q J →
        (∀ e, e ∉ permutedUnion σ G → J e = 0) →
        GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q) J := by
  classical
  filter_upwards [eventually_punctured_rainbow_pair_generated (I := I) hqr hN ht hb hgap]
    with n hpair
  intro G hd σ hE J hJ hs
  obtain ⟨R, hRroot, hRcol⟩ := hE.exists_punctured_references
  have ht' : q.choose (r + 1) ≤ t := by omega
  exact generatedBy_of_clique_residuals _ (permutedUnion σ G)
    (fun e => indicator (cliqueEdges (r + 1) (R e)))
    (rainbow_clique_residual_generated hA hE ht' R hRroot hRcol (hpair G hd σ hE)) J hJ hs

end Arxiv2411_18291
