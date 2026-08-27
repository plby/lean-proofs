import Arxiv.Arxiv2411_18291.NearRegularPairPacking
import Arxiv.Arxiv2411_18291.PairNibbleNumerics
import Arxiv.Arxiv2411_18291.RankOneVertices

/-! # The general rank-one nibble for pairs -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem exists_general_pair_nibble_of_numerics {n : ℕ} {ε : ℝ} (hn : 1 ≤ n)
    (hnum : let c := (n : ℝ) ^ (-(ε / 2))
      0 < c ∧ c ≤ 1 / 4 ∧ (n : ℝ) ^ (-ε) ≤ c ∧
        9 * c * n + 2 < 3 * (n : ℝ) ^ (-(ε / 6)) * n ∧
        ∀ D : ℝ, (n : ℝ) ^ (2 / 3 : ℝ) ≤ D →
          (n + 1 : ℝ) * (2 * Real.exp (-((D / 2) * c ^ 2 / (4 * (1 + 2 * c))))) < 1) :
    ∀ (G : Hypergraph (Fin n) 1) (H : Finset (Block (Fin n) 2))
      (τ : ℝ), (n : ℝ) ^ (2 / 3 : ℝ) ≤ G.card →
      (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      (∀ Q ∈ H, cliqueEdges 1 Q ⊆ G) →
      (∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * n| ≤
          (n : ℝ) ^ (-ε) * (τ * n)) →
      ∃ C : Finset (Block (Fin n) 2), C ⊆ H ∧ IsDecomposition (cliqueSupport 1 C) C ∧
        IsGraphBounded (G \ cliqueSupport 1 C) (3 * (n : ℝ) ^ (-(ε / 6))) := by
  intro G H τ hG hτ hHG hd
  let S := vertexSupport G
  let c := (n : ℝ) ^ (-(ε / 2))
  let D := τ * n
  obtain ⟨hc, hcsmall, herror, hleave, hfail⟩ := hnum
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpower : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (-(1 / 3 : ℝ)) * n := by
    rw [show (2 / 3 : ℝ) = -(1 / 3 : ℝ) + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  have hDlower : (n : ℝ) ^ (2 / 3 : ℝ) ≤ D := by
    rw [hpower]
    exact mul_le_mul_of_nonneg_right hτ hn0.le
  have hD : 0 < D := (Real.rpow_pos_of_pos hn0 _).trans_le hDlower
  have hScard : S.card = G.card := card_vertexSupport_rankOne G
  have hSpos : 0 < S.card := by
    rw [hScard]
    exact_mod_cast (Real.rpow_pos_of_pos hn0 (2 / 3 : ℝ)).trans_le hG
  have hSn : (S.card : ℝ) ≤ n := by
    rw [hScard]
    exact_mod_cast (by simpa only [Fintype.card_fin] using card_rankOne_le G)
  have hHS : ∀ Q ∈ H, Q.val ⊆ S :=
    fun Q hQ => clique_vertices_subset_rankOne_support (hHG Q hQ)
  have hNS (v : Fin n) : pairNeighbors H v ⊆ S := by
    intro w hw
    obtain ⟨Q, hQ, hQval⟩ := (mem_pairNeighbors H v w).mp hw
    exact hHS Q hQ (by simp [hQval])
  have hdegrees : ∀ v ∈ S, |((pairNeighbors H v).card : ℝ) - D| ≤ c * D := by
    intro v hv
    obtain ⟨e, he, hve⟩ := mem_biUnion.mp hv
    have hs := one_block_eq_singleton hve
    have hh := hd e he
    simp only [hs, singleton_subset_iff, ← card_pairNeighbors] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right herror hD.le)
  have hS : D / 2 ≤ (S.card : ℝ) := by
    obtain ⟨v, hv⟩ := card_pos.mp hSpos
    have hlo := (abs_le.mp (hdegrees v hv)).1
    have hcD := mul_le_mul_of_nonneg_right hcsmall hD.le
    have hcard : ((pairNeighbors H v).card : ℝ) ≤ S.card := by
      exact_mod_cast card_le_card (hNS v)
    linarith only [hlo, hcD, hcard, hD]
  have hsampling : (S.card + 1 : ℝ) *
      (2 * Real.exp (-((D / 2) * c ^ 2 / (4 * (1 + 2 * c))))) < 1 := by
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (show (S.card : ℝ) + 1 ≤ n + 1 by linarith)
        (by positivity))
      (hfail D hDlower)
  obtain ⟨C, hCH, hC, hbound⟩ := exists_nearRegular_pair_packing S H hHS hD hc.le hcsmall
    hS hdegrees hsampling
  have hcard : (G \ cliqueSupport 1 C).card = (S \ vertexSupport C).card := by
    rw [← card_vertexSupport_rankOne (G \ cliqueSupport 1 C),
      vertexSupport_sdiff_rankOne, vertexSupport_cliqueSupport_one]
  refine ⟨C, hCH, hC.isDecomposition_rankOne, (isGraphBounded_one_iff _ _).mpr ?_⟩
  simp only [Fintype.card_fin]
  rw [hcard]
  apply (hbound.trans _).trans_lt hleave
  have hcoef : 0 ≤ 9 * c := by positivity
  linarith only [mul_le_mul_of_nonneg_left hSn hcoef]

theorem eventually_exists_general_pair_nibble {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Hypergraph (Fin n) 1) (H : Finset (Block (Fin n) 2))
      (τ : ℝ), (n : ℝ) ^ (2 / 3 : ℝ) ≤ G.card →
      (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ →
      (∀ Q ∈ H, cliqueEdges 1 Q ⊆ G) →
      (∀ e ∈ G,
        |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * n| ≤
          (n : ℝ) ^ (-ε) * (τ * n)) →
      ∃ C : Finset (Block (Fin n) 2), C ⊆ H ∧ IsDecomposition (cliqueSupport 1 C) C ∧
        IsGraphBounded (G \ cliqueSupport 1 C) (3 * (n : ℝ) ^ (-(ε / 6))) := by
  filter_upwards [eventually_pair_nibble_numerics hε hεhalf,
    eventually_ge_atTop (1 : ℕ)] with n hnum hn
  exact exists_general_pair_nibble_of_numerics hn hnum

end Arxiv2411_18291
