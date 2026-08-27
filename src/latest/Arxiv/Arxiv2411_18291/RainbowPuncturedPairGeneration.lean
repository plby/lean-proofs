import Arxiv.Arxiv2411_18291.RainbowPairGeneration
import Arxiv.Arxiv2411_18291.RainbowBridgeExistence

/-!
# Generating differences of arbitrary punctured rainbow cliques

Two cliques through one edge may intersect in other vertices and may
reuse colour labels. A bridge avoiding both palettes resolves both issues.
The two elimination identities cancel the bridge boundary exactly.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {I W : Type*} [Fintype W] [DecidableEq W] {q r t : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q}

theorem RainbowAvoidingExtensionProperties.punctured_pair_generated_of_bridges
    {n : ℕ} {G : Hypergraph (Fin n) (r + 1)} {σ : I → Equiv.Perm (Fin n)}
    (hE : RainbowAvoidingExtensionProperties S N σ G t)
    (hN : N ∈ S.negative) (ht : 2 * q.choose (r + 1) ≤ t)
    (hbridge : ∀ C : Finset I, C.card ≤ t → ∀ P Q : Block (Fin n) q,
      ∀ e : Block (Fin n) (r + 1), e.val ⊆ P.val → e.val ⊆ Q.val →
      ∃ R : Block (Fin n) q, e.val ⊆ R.val ∧ R.val ∩ P.val = e.val ∧
        R.val ∩ Q.val = e.val ∧
        IsRainbowAvoiding (fun i => mapGraph (σ i).toEmbedding G)
          ((cliqueEdges (r + 1) R).erase e) C)
    (P Q : Block (Fin n) q) (e : Block (Fin n) (r + 1))
    (heP : e.val ⊆ P.val) (heQ : e.val ⊆ Q.val)
    (hP : IsRainbow (fun i => mapGraph (σ i).toEmbedding G) ((cliqueEdges (r + 1) P).erase e))
    (hQ : IsRainbow (fun i => mapGraph (σ i).toEmbedding G) ((cliqueEdges (r + 1) Q).erase e)) :
    GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q)
      (indicator (cliqueEdges (r + 1) P) - indicator (cliqueEdges (r + 1) Q)) := by
  classical
  obtain ⟨cP, hcP⟩ := hP
  obtain ⟨cQ, hcQ⟩ := hQ
  let C := univ.image cP ∪ univ.image cQ
  have hPcard : (univ.image cP).card ≤ q.choose (r + 1) := by
    calc
      _ ≤ (univ : Finset ↥((cliqueEdges (r + 1) P).erase e)).card := card_image_le
      _ = ((cliqueEdges (r + 1) P).erase e).card := by rw [card_univ, Fintype.card_coe]
      _ ≤ (cliqueEdges (r + 1) P).card := card_le_card (erase_subset _ _)
      _ = _ := card_cliqueEdges _
  have hQcard : (univ.image cQ).card ≤ q.choose (r + 1) := by
    calc
      _ ≤ (univ : Finset ↥((cliqueEdges (r + 1) Q).erase e)).card := card_image_le
      _ = ((cliqueEdges (r + 1) Q).erase e).card := by rw [card_univ, Fintype.card_coe]
      _ ≤ (cliqueEdges (r + 1) Q).card := card_le_card (erase_subset _ _)
      _ = _ := card_cliqueEdges _
  have hC : C.card ≤ t := by
    have hu : C.card ≤ (univ.image cP).card + (univ.image cQ).card := card_union_le _ _
    omega
  obtain ⟨R, _, hRP, hRQ, hR⟩ := hbridge C hC P Q e heP heQ
  have hPRcol : IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
      ((cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) R).erase e) := by
    rw [erase_union_distrib]
    exact hR.union_left cP hcP (fun x => mem_union_left _
      (mem_image.mpr ⟨x, mem_univ _, rfl⟩))
  have hQRcol : IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
      ((cliqueEdges (r + 1) Q ∪ cliqueEdges (r + 1) R).erase e) := by
    rw [erase_union_distrib]
    exact hR.union_left cQ hcQ (fun x => mem_union_right _
      (mem_image.mpr ⟨x, mem_univ _, rfl⟩))
  have hPR := hE.pair_generated hN ht P R e ((inter_comm _ _).trans hRP) hPRcol
  have hQR := hE.pair_generated hN ht Q R e ((inter_comm _ _).trans hRQ) hQRcol
  convert hPR.sub hQR using 1
  abel

theorem eventually_punctured_rainbow_pair_generated (hqr : r + 1 < q)
    (hN : N ∈ S.negative) (ht : 2 * q.choose (r + 1) ≤ t)
    {b α : ℝ} (hb : 0 < b) (hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      b * (n : ℝ) ^ (-α) ≤ density G → ∀ σ : I → Equiv.Perm (Fin n),
      RainbowAvoidingExtensionProperties S N σ G t →
      ∀ P Q : Block (Fin n) q, ∀ e : Block (Fin n) (r + 1),
      e.val ⊆ P.val → e.val ⊆ Q.val →
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) ((cliqueEdges (r + 1) P).erase e) →
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) ((cliqueEdges (r + 1) Q).erase e) →
      GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q)
        (indicator (cliqueEdges (r + 1) P) - indicator (cliqueEdges (r + 1) Q)) := by
  filter_upwards [eventually_exists_avoiding_rainbow_bridge (I := I) (S := S) (N := N)
    (t := t) hqr hb hgap] with n hbridge
  intro G hd σ hE
  exact hE.punctured_pair_generated_of_bridges hN ht (hbridge G hd σ hE)

end Arxiv2411_18291
