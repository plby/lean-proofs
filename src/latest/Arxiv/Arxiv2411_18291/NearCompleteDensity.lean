import Arxiv.Arxiv2411_18291.AsymptoticNearCompleteCliques

/-! # A bounded complement leaves more than half the edges -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem rootedCliques_empty_self {V : Type*} [Fintype V]
    {r : ℕ} (G : Hypergraph V (r + 1)) :
    rootedCliques G (⟨∅, rfl⟩ : Block V 0) (r + 1) = G := by
  classical
  ext e
  rw [mem_rootedCliques]
  constructor
  · intro h
    rcases h.2 e Subset.rfl with he | he
    · exact he
    · have hz := card_le_card he
      simp only [e.property, card_empty] at hz
      omega
  · intro he
    refine ⟨empty_subset _, fun f hf => Or.inl ?_⟩
    have hfe : f = e := Subtype.ext (eq_of_subset_of_card_le hf
      (by rw [e.property, f.property]))
    simpa only [hfe] using he

theorem eventually_dense_of_bounded_complement (r : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) ((n : ℝ) ^ (-δ)) →
      (1 / 2 : ℝ) * (n.choose (r + 1) : ℝ) < G.card := by
  have hκ : 0 < δ / 2 := by positivity
  have hlim := (tendsto_rpow_neg_atTop hκ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_rootedClique_count_of_bounded_complement (r + 1) r 0
      (Nat.zero_le _) (δ := δ) hκ (by linarith) (by linarith),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (1 : ℕ)] with n hcount hsmall hn
  intro G hG
  dsimp only [Function.comp_def] at hsmall
  have h := hcount G hG (⟨∅, rfl⟩ : Block (Fin n) 0)
  rw [rootedCliques_empty_self, Nat.sub_zero] at h
  have hu := shifted_choose_upper n 0 (r + 1)
  simp only [Nat.sub_zero] at hu
  have hpos : (0 : ℝ) < (n : ℝ) ^ (r + 1) / (r + 1).factorial := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have herror := mul_lt_mul_of_pos_right hsmall hpos
  have hlo := (abs_le.mp h).1
  linarith only [hu, herror, hlo]

end Arxiv2411_18291
