import Arxiv.Arxiv2411_18291.SampledAbsorberProcess
import Arxiv.Arxiv2411_18291.SmallCarrierExchange

/-!
# Constructing every pattern of the sampled absorber

Only the sparse input graph and a multiplicity-16 family of integral
generators are supplied. All exchange patterns, initial roots, conditional
placement laws, and their joint success estimate are constructed at n0.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sampled_absorber_for_generated_leaves {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1)) (D₁ : Finset (Block (Fin n) q))
    (hB : IsGraphBounded B (2 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hDB : cliqueSupport (r + 1) D₁ ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1), (D₁.filter fun Q => e.val ⊆ Q.val).card ≤ 16) :
    ∃ F₀ : Block (Fin (q + (r + 1))) (r + 1),
    ∃ S T : FiniteExchangeSystem q (r + 1), ∃ N : Block T.Vertex q,
    ∃ d₀ : Block (Fin n) (r + 1), ∃ Q₀ : Block (Fin n) q,
      SampledAbsorberProcessSuccess F₀ (Fintype.card_fin _) S.system T.system N B D₁ d₀ Q₀ := by
  classical
  obtain ⟨f, _, hf⟩ := exists_subset_card_eq
    (s := (univ : Finset (Fin (q + (r + 1)))))
    (by simp only [card_univ, Fintype.card_fin]; omega : r + 1 ≤
      (univ : Finset (Fin (q + (r + 1)))).card)
  let F₀ : Block (Fin (q + (r + 1))) (r + 1) := ⟨f, hf⟩
  have hnq : q ≤ n := by
    have hh := (boost_threshold_root_size_bounds (by omega : 2 ≤ q)
      ((boost_threshold_le_paper_threshold hqr).trans hn)).2.2
    omega
  obtain ⟨s, _, hsq⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n)))
    (by simpa only [card_univ, Fintype.card_fin] using hnq)
  let Q₀ : Block (Fin n) q := ⟨s, hsq⟩
  obtain ⟨d, _, hd⟩ := exists_subset_card_eq (s := Q₀.val)
    (by rw [Q₀.property]; exact hqr.le : r + 1 ≤ Q₀.val.card)
  let d₀ : Block (Fin n) (r + 1) := ⟨d, hd⟩
  obtain ⟨S, A₀, hS, hA₀, hcross, hlocal, hwS⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨T, N, e₀, hpair, hT, hwT⟩ := exists_small_carrier_elimination_pattern q r hqr
  exact ⟨F₀, S, T, N, d₀, Q₀,
    exists_sampled_absorber_process_paper_threshold F₀ (Fintype.card_fin _) S.system
      hA₀ hlocal hcross T.system N e₀ hpair hqr hn hwS hwT hS hT B D₁ hB hDB hmult d₀ Q₀⟩

end Arxiv2411_18291
