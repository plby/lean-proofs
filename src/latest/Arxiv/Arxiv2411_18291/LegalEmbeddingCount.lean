import Arxiv.Arxiv2411_18291.ForbiddenEmbeddingCount

/-!
# Legal choices for a greedy embedding step

Only edges not contained in the root set must avoid the forbidden graph.
A union bound over these edges, combined with the initial extension count,
leaves at least half of all unrestricted assignments when the forbidden
degree parameter is small enough.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

/-- The edges whose images are chosen by the extension rather than by its roots. -/
def newEdges (F : Finset W) (H : Hypergraph W (r + 1)) : Hypergraph W (r + 1) :=
  H.filter fun e => ¬ e.val ⊆ F

def forbiddenExtensions (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) : Finset (EmbeddingExtension φ) :=
  (newEdges F H).biUnion fun e => forbiddenEdgeExtensions φ e B

def legalExtensions (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) : Finset (EmbeddingExtension φ) :=
  univ \ forbiddenExtensions φ H B

omit [Fintype W] in
@[simp] theorem mem_newEdges (H : Hypergraph W (r + 1)) (e : Block W (r + 1)) :
    e ∈ newEdges F H ↔ e ∈ H ∧ ¬ e.val ⊆ F := by
  simp [newEdges]

@[simp] theorem mem_legalExtensions (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (f : EmbeddingExtension φ) :
    f ∈ legalExtensions φ H B ↔
      ∀ e ∈ H, ¬ e.val ⊆ F → mapBlock f.val e ∉ B := by
  simp [legalExtensions, forbiddenExtensions, forbiddenEdgeExtensions, newEdges]

theorem forbiddenExtensions_card_le (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ) :
    ((forbiddenExtensions φ H B).card : ℝ) ≤
      H.card * θ * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) := by
  have hc : (newEdges F H).card ≤ H.card := card_filter_le _ _
  have hp : 0 ≤ θ * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) := by positivity
  calc
    _ ≤ ∑ e ∈ newEdges F H, ((forbiddenEdgeExtensions φ e B).card : ℝ) := by
      exact_mod_cast (card_biUnion_le (s := newEdges F H)
        (t := fun e => forbiddenEdgeExtensions φ e B))
    _ ≤ ∑ _e ∈ newEdges F H,
        θ * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) := by
      apply sum_le_sum
      intro e he
      exact forbiddenEdgeExtensions_card_le φ e B hB hθ ((mem_newEdges H e).mp he).2
    _ = (newEdges F H).card *
        (θ * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card)) := by
      simp only [sum_const, nsmul_eq_mul]
    _ ≤ H.card * (θ * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hp
    _ = _ := by ring

/-- A numerical, nonasymptotic lower bound on the available choices. -/
theorem legalExtensions_card_half (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hsmall : H.card * θ ≤ 1 / 4) :
    (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤
      (legalExtensions φ H B).card := by
  have htotal := card_embeddingExtension_three_quarters φ hn
  have hbad := (forbiddenExtensions_card_le φ H B hB hθ).trans
    (mul_le_mul_of_nonneg_right hsmall (pow_nonneg (Nat.cast_nonneg _) _))
  have hsplit : (legalExtensions φ H B).card + (forbiddenExtensions φ H B).card =
      Fintype.card (EmbeddingExtension φ) := by
    simpa only [legalExtensions, card_univ] using
      card_sdiff_add_card_eq_card (subset_univ (forbiddenExtensions φ H B))
  have hsplitR : ((legalExtensions φ H B).card : ℝ) +
      (forbiddenExtensions φ H B).card = Fintype.card (EmbeddingExtension φ) := by
    exact_mod_cast hsplit
  linarith

theorem legalExtensions_nonempty (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V) (hsmall : H.card * θ ≤ 1 / 4)
    (hnpos : 0 < Fintype.card V) : (legalExtensions φ H B).Nonempty := by
  apply card_pos.mp
  have hpow : (0 : ℝ) < (1 / 2 : ℝ) *
      (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) := by
    have hV : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
    positivity
  exact_mod_cast hpow.trans_le (legalExtensions_card_half φ H B hB hθ hn hsmall)

end Arxiv2411_18291
