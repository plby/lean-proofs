import Arxiv.Arxiv2411_18291.FiniteRainbowIntegralGeneration
import Arxiv.Arxiv2411_18291.RelaxedFocusingCounts

/-! # Rainbow bridges and integral generation with the relaxed good-edge loss -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I W : Type*} [Fintype W] [DecidableEq W] {q r n t H : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q}

theorem exists_avoiding_rainbow_bridge_relaxed_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card)
    (σ : I → Equiv.Perm (Fin n)) (hE : RainbowAvoidingExtensionProperties S N σ G t)
    (C : Finset I) (hC : C.card ≤ t) (P Q : Block (Fin n) q)
    (e : Block (Fin n) (r + 1)) (heP : e.val ⊆ P.val) (heQ : e.val ⊆ Q.val) :
    ∃ R : Block (Fin n) q, e.val ⊆ R.val ∧ R.val ∩ P.val = e.val ∧
      R.val ∩ Q.val = e.val ∧
      IsRainbowAvoiding (fun i => mapGraph (σ i).toEmbedding G)
        ((cliqueEdges (r + 1) R).erase e) C := by
  classical
  let D := rainbowAvoidingPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q C
  have hD : ∀ R ∈ D, e.val ⊆ R.val := fun _ hR => (mem_filter.mp hR).2.1
  have hsize : (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) *
      (n : ℝ) ^ (q - (r + 1)) ≤ (D.card : ℝ) :=
    (focusing_clique_mainTerm_lower_relaxed_paper_threshold
      hqr hn hqh hH K G hd hGK hloss).trans
      (by simpa only [D, Fintype.card_fin] using (hE.punctured C hC e).le)
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  obtain ⟨R, hR, hRP, hRQ⟩ := exists_rooted_clique_bridge D e hqr hD P Q heP heQ
    (by positivity) hsize
    (by simpa only [Fintype.card_fin] using rainbow_bridge_collision_bound_paper_threshold hqr hn)
  exact ⟨R, hD R hR, hRP, hRQ, (mem_filter.mp hR).2.2⟩

theorem punctured_rainbow_pair_generated_relaxed_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) (hN : N ∈ S.negative)
    (ht : 2 * q.choose (r + 1) ≤ t) (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card)
    (σ : I → Equiv.Perm (Fin n)) (hE : RainbowAvoidingExtensionProperties S N σ G t)
    (P Q : Block (Fin n) q) (e : Block (Fin n) (r + 1))
    (heP : e.val ⊆ P.val) (heQ : e.val ⊆ Q.val)
    (hP : IsRainbow (fun i => mapGraph (σ i).toEmbedding G) ((cliqueEdges (r + 1) P).erase e))
    (hQ : IsRainbow (fun i => mapGraph (σ i).toEmbedding G) ((cliqueEdges (r + 1) Q).erase e)) :
    GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q)
      (indicator (cliqueEdges (r + 1) P) - indicator (cliqueEdges (r + 1) Q)) :=
  hE.punctured_pair_generated_of_bridges hN ht
    (exists_avoiding_rainbow_bridge_relaxed_paper_threshold
      hqr hn hqh hH K G hd hGK hloss σ hE)
    P Q e heP heQ hP hQ

theorem integral_coloured_generated_rainbow_relaxed_paper_threshold [Fintype I]
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ H)
    (hH : H ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) (hN : N ∈ S.negative)
    (ht : 2 * q.choose (r + 1) ≤ t) (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card)
    (σ : I → Equiv.Perm (Fin n)) (hE : RainbowAvoidingExtensionProperties S N σ G t)
    (J : Block (Fin n) (r + 1) → ℤ) (hJ : IntegrallyDecomposable q J)
    (hs : ∀ e, e ∉ permutedUnion σ G → J e = 0) :
    GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q) J := by
  classical
  obtain ⟨R, hRroot, hRcol⟩ := hE.exists_punctured_references
  have ht' : q.choose (r + 1) ≤ t := by omega
  exact generatedBy_of_clique_residuals _ (permutedUnion σ G)
    (fun e => indicator (cliqueEdges (r + 1) (R e)))
    (rainbow_clique_residual_generated hA hE ht' R hRroot hRcol
      (punctured_rainbow_pair_generated_relaxed_paper_threshold
        hqr hn hqh hH hN ht K G hd hGK hloss σ hE))
    J hJ hs

end Arxiv2411_18291
