import Arxiv.Arxiv2411_18291.SharedDecodersAtThreshold
import Arxiv.Arxiv2411_18291.AllEdgeFocusing

/-! # The exact standalone decoder and focusing lemma at n0

Sharing a decoder region across each input clique gives enough room for
the printed boundary coefficient. The focusing conclusion holds for every
reserve edge, with no disjointness assumption on the coloured host.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_decoder_focusing_exact_coefficient {q r n u : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hu : 1 ≤ u)
    (D₀ : Finset (Block (Fin n) q))
    (hD₀ : IsCliqueFamilyBounded r D₀
      (u * 2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))))
    (B E : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) *
        (n : ℝ) ^ (q - (r + 1)) ≤ (puncturedCliques E e q).card) :
    ∃ D : Finset (Block (Fin n) q), D₀ ⊆ D ∧
      IsCliqueFamilyBounded r D (2 ^ (q + 2) * (4 * q : ℝ) ^ (r + 1) * u *
        (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      (∀ e ∈ cliqueSupport (r + 1) D₀, ∃ Z : Block (Fin n) (q + (r + 1)),
        e.val ⊆ Z.val ∧ ∀ Q : Block (Fin n) q, Q.val ⊆ Z.val → Q ∈ D) ∧
      ∀ e ∈ B, ∃ Q ∈ D, e.val ⊆ Q.val ∧ (cliqueEdges (r + 1) Q).erase e ⊆ E := by
  have hC : (1 : ℝ) ≤ u * 2 ^ q :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hu)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  obtain ⟨D₁, hsub, hD₁, hdecode⟩ :=
    exists_shared_clique_decoders_paper_threshold hqr hn hC D₀ hD₀
  obtain ⟨F, hF, hfocus⟩ := exists_all_edge_focusing_paper_threshold hqr hn B E hB hcount
  have hA : (1 : ℝ) ≤ (4 * q : ℝ) ^ (r + 1) := by
    apply one_le_pow₀
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    linarith only [hq]
  have hAC : (1 : ℝ) ≤ (4 * q : ℝ) ^ (r + 1) * (u * 2 ^ q) :=
    one_le_mul_of_one_le_of_one_le hA hC
  have hcoef : 2 * (4 * q : ℝ) ^ (r + 1) * (u * 2 ^ q) + 1 ≤
      2 ^ (q + 2) * (4 * q : ℝ) ^ (r + 1) * u := by
    rw [pow_add (2 : ℝ) q 2]
    norm_num only [pow_two]
    nlinarith only [hAC]
  have hbound := (hD₁.union hF).mono
    (show 2 * (4 * q : ℝ) ^ (r + 1) * (u * 2 ^ q) *
        (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) +
          (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) ≤
        2 ^ (q + 2) * (4 * q : ℝ) ^ (r + 1) * u *
          (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) by
      simpa only [add_mul, one_mul] using mul_le_mul_of_nonneg_right hcoef
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-(7 * paperAlpha q (r + 1) / 10))))
  refine ⟨D₁ ∪ F, hsub.trans subset_union_left, hbound, ?_, ?_⟩
  · intro e he
    obtain ⟨Z, heZ, hZ⟩ := hdecode e he
    exact ⟨Z, heZ, fun Q hQ => mem_union_left _ (hZ Q hQ)⟩
  · intro e he
    obtain ⟨Q, hQ, heQ⟩ := hfocus e he
    exact ⟨Q, mem_union_right _ hQ, heQ⟩

theorem exists_coloured_decoder_focusing_exact_coefficient
    {I : Type*} [Fintype I] {q r n u : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hu : 1 ≤ u)
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (σ : I → Equiv.Perm (Fin n))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
          (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (D₀ : Finset (Block (Fin n) q))
    (hD₀ : IsCliqueFamilyBounded r D₀
      (u * 2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) :
    ∃ D : Finset (Block (Fin n) q), D₀ ⊆ D ∧
      IsCliqueFamilyBounded r D (2 ^ (q + 2) * (4 * q : ℝ) ^ (r + 1) * u *
        (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      (∀ e ∈ cliqueSupport (r + 1) D₀, ∃ Z : Block (Fin n) (q + (r + 1)),
        e.val ⊆ Z.val ∧ ∀ Q : Block (Fin n) q, Q.val ⊆ Z.val → Q ∈ D) ∧
      ∀ e ∈ B, ∃ Q ∈ D, e.val ⊆ Q.val ∧
        (cliqueEdges (r + 1) Q).erase e ⊆ permutedUnion σ G := by
  exact exists_decoder_focusing_exact_coefficient hqr hn hu D₀ hD₀ B
    (permutedUnion σ G) hB
    (coloured_punctured_clique_count_paper_threshold hqr hn K G hd hGK hloss σ hcount)

end Arxiv2411_18291
