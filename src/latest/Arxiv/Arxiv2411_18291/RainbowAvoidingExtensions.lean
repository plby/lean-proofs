import Arxiv.Arxiv2411_18291.RainbowGeneratingSystem
import Arxiv.Arxiv2411_18291.RainbowColourAvoidance

/-!
# Simultaneous extensions avoiding a bounded set of colours

Distinct labelled copies of the same palette preserve all three extension
properties after forbidding any bounded set of labels. The punctured-clique
count still counts distinct cliques, with its factorial divisor.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {I J W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ}

open Classical in
def rainbowAvoidingPuncturedCliques (colour : J → Hypergraph V (r + 1))
    (e : Block V (r + 1)) (q : ℕ) (B : Finset J) : Finset (Block V q) :=
  univ.filter fun Q => e.val ⊆ Q.val ∧ IsRainbowAvoiding colour ((cliqueEdges (r + 1) Q).erase e) B

omit [Fintype W] [DecidableEq W] in
theorem rainbowPuncturedCliques_subset_avoiding_copies [Fintype I]
    (colour : J → Hypergraph V (r + 1)) (e : Block V (r + 1)) (B : Finset (I × J))
    (hB : B.card < Fintype.card I) :
    rainbowPuncturedCliques colour e q ⊆
      rainbowAvoidingPuncturedCliques (fun p : I × J => colour p.2) e q B := by
  classical
  intro Q hQ
  obtain ⟨_, heQ, hcol⟩ := mem_filter.mp hQ
  exact mem_filter.mpr ⟨mem_univ _, heQ, hcol.avoiding_copies B hB⟩

structure RainbowAvoidingExtensionProperties (S : ExchangeSystem W q (r + 1))
    (N : Block W q) (σ : J → Equiv.Perm V) (G : Hypergraph V (r + 1)) (t : ℕ) : Prop where
  punctured : ∀ B : Finset J, B.card ≤ t → ∀ e : Block V (r + 1),
    ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
      (Fintype.card V : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial <
        (rainbowAvoidingPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q B).card
  clique : ∀ B : Finset J, B.card ≤ t → ∀ P : Block V q,
    ∃ f : W ↪ V, mapBlock f S.base = P ∧
      IsRainbowAvoiding (fun i => mapGraph (σ i).toEmbedding G)
        (mapGraph f S.graph \ cliqueEdges (r + 1) P) B
  pair : ∀ B : Finset J, B.card ≤ t → ∀ P Q : Block V q,
    ∀ d : Block V (r + 1), P.val ∩ Q.val = d.val →
      ∃ f : W ↪ V, mapBlock f S.base = P ∧ mapBlock f N = Q ∧
        IsRainbowAvoiding (fun i => mapGraph (σ i).toEmbedding G)
          (mapGraph f S.graph \ (cliqueEdges (r + 1) P ∪ cliqueEdges (r + 1) Q)) B

omit [Fintype W] [DecidableEq W] in
theorem rainbowAvoidingPuncturedCliques_subset (colour : J → Hypergraph V (r + 1))
    (e : Block V (r + 1)) (B : Finset J) :
    rainbowAvoidingPuncturedCliques colour e q B ⊆ rainbowPuncturedCliques colour e q := by
  classical
  intro Q hQ
  obtain ⟨_, heQ, hcol⟩ := mem_filter.mp hQ
  exact mem_filter.mpr ⟨mem_univ _, heQ, hcol.isRainbow⟩

theorem RainbowAvoidingExtensionProperties.toRainbowExtensionProperties
    {S : ExchangeSystem W q (r + 1)} {N : Block W q} {σ : J → Equiv.Perm V}
    {G : Hypergraph V (r + 1)} {t : ℕ} (hE : RainbowAvoidingExtensionProperties S N σ G t) :
    RainbowExtensionProperties S N σ G := by
  have hempty : (∅ : Finset J).card ≤ t := Nat.zero_le t
  constructor
  · intro e
    exact (hE.punctured ∅ hempty e).trans_le (Nat.cast_le.mpr
      (card_le_card (rainbowAvoidingPuncturedCliques_subset _ e ∅)))
  · intro P
    obtain ⟨f, hf, hcol⟩ := hE.clique ∅ hempty P
    exact ⟨f, hf, hcol.isRainbow⟩
  · intro P Q d hPQ
    obtain ⟨f, hfP, hfQ, hcol⟩ := hE.pair ∅ hempty P Q d hPQ
    exact ⟨f, hfP, hfQ, hcol.isRainbow⟩

theorem RainbowExtensionProperties.avoiding_copies {S : ExchangeSystem W q (r + 1)}
    {N : Block W q} {σ : J → Equiv.Perm V} {G : Hypergraph V (r + 1)}
    (hE : RainbowExtensionProperties S N σ G) (t : ℕ) :
    RainbowAvoidingExtensionProperties S N (fun p : Fin (t + 1) × J => σ p.2) G t := by
  have hsize (B : Finset (Fin (t + 1) × J)) (hB : B.card ≤ t) :
      B.card < Fintype.card (Fin (t + 1)) := by
    simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hB
  constructor
  · intro B hB e
    have hsub := rainbowPuncturedCliques_subset_avoiding_copies
      (q := q) (fun i => mapGraph (σ i).toEmbedding G) e B (hsize B hB)
    exact (hE.punctured e).trans_le (Nat.cast_le.mpr (card_le_card hsub))
  · intro B hB P
    obtain ⟨f, hf, hcol⟩ := hE.clique P
    exact ⟨f, hf, hcol.avoiding_copies B (hsize B hB)⟩
  · intro B hB P Q d hPQ
    obtain ⟨f, hfP, hfQ, hcol⟩ := hE.pair P Q d hPQ
    exact ⟨f, hfP, hfQ, hcol.avoiding_copies B (hsize B hB)⟩

end Arxiv2411_18291
