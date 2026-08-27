import Arxiv.Arxiv2411_18291.DenseNibble
import Arxiv.Arxiv2411_18291.RankOneRestriction
import Arxiv.Arxiv2411_18291.RankOneRestrictionScales
import Arxiv.Arxiv2411_18291.CliqueFamilyRelabeling
import Arxiv.Arxiv2411_18291.RainbowExchangePlacements

/-! # The general rank-one nibble for cliques of size at least three -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_sparse_rankOne_nibble (q : ℕ) (hq : 3 ≤ q)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Hypergraph (Fin n) 1) (H : Finset (Block (Fin n) q))
      (τ : ℝ), (n : ℝ) ^ (2 / 3 : ℝ) ≤ G.card →
      (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      (∀ Q ∈ H, cliqueEdges 1 Q ⊆ G) →
      (∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - 1) : ℝ)| ≤
          (n : ℝ) ^ (-ε) * (τ * (n.choose (q - 1) : ℝ))) →
      ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧ IsDecomposition (cliqueSupport 1 C) C ∧
        IsGraphBounded (G \ cliqueSupport 1 C) (3 * (n : ℝ) ^ (-(ε / (3 * (q : ℝ))))) := by
  have hdense := eventually_exists_dense_nibble q 0 (by omega)
    (by simpa only [Nat.zero_add, Nat.choose_one_right] using hq)
    hε hεhalf (θ := 1) (by norm_num)
  simp only [Nat.zero_add, Nat.choose_one_right, one_mul] at hdense
  obtain ⟨M, hM⟩ := hdense.exists_forall_of_atTop
  have hgrowth := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop ((max M (q + 1) : ℕ) : ℝ))
  filter_upwards [hgrowth, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro G H τ hG hτ hHG hd
  have hm : max M (q + 1) ≤ G.card := by exact_mod_cast hn.trans hG
  have hm0 : 0 < G.card := by omega
  have hmn : G.card ≤ n := by simpa only [Fintype.card_fin] using card_rankOne_le G
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hD : 0 ≤ τ * (n.choose (q - 1) : ℝ) :=
    mul_nonneg ((Real.rpow_nonneg hn0.le _).trans hτ) (Nat.cast_nonneg _)
  obtain ⟨τ', hτ', hmean⟩ := rankOne_restricted_degree_scale hm0 hmn
    (by omega : 0 < q - 1) (by omega : q - 1 ≤ G.card) hτ
  obtain ⟨f, H', hmapG, hmapH⟩ := exists_rankOne_restriction G H hHG
  have hdegrees : ∀ e ∈ complete (Fin G.card) 1,
      |((H'.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ' * (G.card.choose (q - 1) : ℝ)| ≤
        (G.card : ℝ) ^ (-ε) * (τ' * (G.card.choose (q - 1) : ℝ)) := by
    intro e he
    have heG : mapBlock f e ∈ G := by
      apply hmapG.le
      exact (mem_mapGraph f (complete (Fin G.card) 1) (mapBlock f e)).mpr ⟨e, he, rfl⟩
    have hh := hd (mapBlock f e) heG
    rw [← hmapH, card_mapGraph_containing] at hh
    rw [hmean]
    exact rankOne_restricted_degree_error hm0 hmn hε.le hD hh
  have hcomplete : (G.card : ℝ) ≤ ((complete (Fin G.card) 1).card : ℝ) := by
    simp only [complete, card_univ, Block, Fintype.card_finset_len, Fintype.card_fin,
      Nat.choose_one_right, le_refl]
  obtain ⟨D, hDH, hDdec, hleave⟩ := hM G.card (by omega) (complete (Fin G.card) 1) H' τ'
    hcomplete hτ' (fun _ _ => subset_univ _) hdegrees
  let C := mapGraph f D
  have hCH : C ⊆ H := hmapH ▸ mapGraph_mono f hDH
  have hCdec : IsDecomposition (cliqueSupport 1 C) C := by
    simpa only [mapGraph_cliqueSupport] using hDdec.map f
  have hmapL : mapGraph f (complete (Fin G.card) 1 \ cliqueSupport 1 D) =
      G \ cliqueSupport 1 C := by
    rw [mapGraph_sdiff, hmapG, mapGraph_cliqueSupport]
  have hcard : (G \ cliqueSupport 1 C).card =
      (complete (Fin G.card) 1 \ cliqueSupport 1 D).card := by
    rw [← hmapL, card_mapGraph]
  refine ⟨C, hCH, hCdec, (isGraphBounded_one_iff _ _).mpr ?_⟩
  have hb := (isGraphBounded_one_iff _ _).mp hleave
  simp only [Fintype.card_fin] at hb ⊢
  rw [hcard]
  apply hb.trans_le
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hβ : ε / (3 * (q : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hεhalf, hqR]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (rankOne_leave_scale_mono hm0 hmn hβ) (by norm_num : (0 : ℝ) ≤ 3)

end Arxiv2411_18291
