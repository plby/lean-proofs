import Arxiv.Arxiv2411_18291.FiniteSparseNibbleExponents
import Arxiv.Arxiv2411_18291.ExplicitNibbleTail
import Arxiv.Arxiv2411_18291.NibbleUniformExponent
import Arxiv.Arxiv2411_18291.NibbleBinomialScales
import Arxiv.Arxiv2411_18291.RankOneVertices
import Arxiv.Arxiv2411_18291.FiniteSparsePairNibble

/-!
# Section 9's sparse nibble at n0 in a variable-error range

The graph and clique densities may be as small as the polynomial lower
bounds in Lemma 9.1. The finite comparison estimates cover
`3*choose(q,r)*rho ≤ ε ≤ 2/5` in every positive edge rank, and the pair
case covers every `ε ≤ 2/5`. The other results accept explicit floor
conditions, separated from the density estimates. Rank-one graphs with
too few vertices already satisfy the leave bound; larger graphs use the
same finite concentration estimates. `FiniteGeneralNibble` extends this
to large cliques and proves a uniform version with a larger leave constant.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

open CliqueRemovalProcess

theorem exists_nibble_of_one_lt_leave {q r n : ℕ} {θ : ℝ}
    (hn : 1 ≤ n) (hθ : 1 < θ)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q)) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C) θ := by
  refine ⟨∅, empty_subset _, ?_, ?_⟩
  · simp [IsDecomposition, cliqueSupport]
  · simp only [cliqueSupport, biUnion_empty, sdiff_empty]
    intro f
    simp only [Fintype.card_fin]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hf : ((G.filter fun e => f.val ⊆ e.val).card : ℝ) ≤ n := by
      exact_mod_cast (by simpa only [Fintype.card_fin] using face_degree_le_card G f)
    exact hf.trans_lt (by simpa only [one_mul] using mul_lt_mul_of_pos_right hθ hn0)

theorem exists_nibble_of_nonpositive_error {q r n : ℕ} {ε : ℝ}
    (hn : 1 ≤ n) (hε : ε ≤ 0)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q)) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  apply exists_nibble_of_one_lt_leave hn _ G H
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) :=
    Real.one_le_rpow hn1 (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hε (by positivity)))
  linarith only [hp]

theorem exists_pair_nibble_paper_threshold {n : ℕ}
    (hn : paperSizeThreshold 2 1 ≤ n) {ε : ℝ} (hεhi : ε ≤ 2 / 5)
    (G : Hypergraph (Fin n) 1) (H : Finset (Block (Fin n) 2)) (τ : ℝ)
    (hG : (n : ℝ) ^ (2 / 3 : ℝ) ≤ G.card)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges 1 Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * n| ≤
        (n : ℝ) ^ (-ε) * (τ * n)) :
    ∃ C : Finset (Block (Fin n) 2), C ⊆ H ∧
      IsDecomposition (cliqueSupport 1 C) C ∧
        IsGraphBounded (G \ cliqueSupport 1 C) (3 * (n : ℝ) ^ (-(ε / 6))) := by
  have hnNat : 1 ≤ n := (paperSizeThreshold_one_lt (by norm_num : 1 < 2)).le.trans hn
  by_cases hε : 0 < ε
  · by_cases hp : (n : ℝ) ^ (-(ε / 6)) ≤ 1 / 3
    · exact exists_general_pair_nibble_of_numerics hnNat
        (pair_nibble_numerics_of_small_leave_paper_threshold hn hε hεhi hp)
        G H τ hG hτ hHG hd
    · exact exists_nibble_of_one_lt_leave (r := 0) hnNat
        (by linarith only [lt_of_not_ge hp]) G H
  · simpa only [Nat.zero_add, Nat.choose_one_right, Nat.cast_ofNat,
      show (3 : ℝ) * 2 = 6 by norm_num] using
        exists_nibble_of_nonpositive_error (q := 2) (r := 0) hnNat (le_of_not_gt hε) G H

theorem exists_nibble_of_graph_size_at_floor_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 3 ≤ q.choose (r + 1))
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ε p₀ : ℝ} (hεhi : ε ≤ 2 / 5)
    (hp : (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) ≤ p₀) (hp₁ : p₀ ≤ 1)
    (hF : NibbleFloorConditions (q.choose (r + 1)) ((n : ℝ) ^ (-(ε / 3)))
      p₀)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (τ : ℝ) (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * (r + 1).factorial) ≤ G.card)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * p₀) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hk0 : (q.choose (r + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (show q.choose (r + 1) ≠ 0 by omega)
  have hpow : (n : ℝ) ^ (-(ε / 3)) ≤ p₀ ^ (q.choose (r + 1)) := by
    have heq : ((n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) ^
        (q.choose (r + 1)) = (n : ℝ) ^ (-(ε / 3)) := by
      rw [← Real.rpow_mul_natCast hn0.le]
      congr 1
      field_simp
    rw [← heq]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hn0.le _) hp _
  have hD₂ := binomial_density_lower_paper_threshold (Nat.succ_le_iff.mpr (Nat.succ_pos r))
    hqr hn (Nat.sub_le q (r + 1)) hτ
  have hD : (n : ℝ) ^ (((q - (r + 1) : ℕ) : ℝ) - 1 / 3) /
      (4 * (q - (r + 1)).factorial) ≤ τ * (n.choose (q - (r + 1)) : ℝ) := by
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le _)
      (by positivity : (0 : ℝ) < 2 * (q - (r + 1)).factorial)
      (by nlinarith only [(Nat.cast_nonneg (q - (r + 1)).factorial :
        (0 : ℝ) ≤ (q - (r + 1)).factorial)])).trans hD₂
  let k := q.choose (r + 1)
  let a := (n : ℝ) ^ (-(ε / 3))
  let D := τ * (n.choose (q - (r + 1)) : ℝ)
  let N := nibbleHorizon k (G.card : ℝ) p₀
  have hdiff : q - (r + 1) + 1 = q - r := by omega
  have P : NibbleComparisonParameters k a G.card D p₀
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) := by
    simpa only [Fintype.card_fin, k, a, D] using
      sparse_nibble_comparison_at_floor_paper_threshold
        (Nat.succ_le_iff.mpr (Nat.succ_pos r)) hqr hk hεhi
          ((Real.rpow_pos_of_pos hn0 _).trans_le hp) hp₁ hpow hF hn hg hD
  have Q : NibbleCountConditions k a G.card D p₀
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) := by
    simpa only [Fintype.card_fin, k, a, D] using
      sparse_nibble_count_at_floor_paper_threshold
        (Nat.succ_le_iff.mpr (Nat.succ_pos r)) hqr hεhi hF hn hg hD
  have R : NibbleEndConditions k a G.card (Fintype.card (Fin n)) p₀ (q - r) := by
    simpa only [Fintype.card_fin, k, a, hdiff] using
      sparse_nibble_end_at_floor_paper_threshold
        (Nat.succ_le_iff.mpr (Nat.succ_pos r)) hqr hεhi hF hn hg
  have S : NibbleExponentConditions k (q - r) a G.card D (Fintype.card (Fin n))
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) ((n : ℝ) ^ (1 / 10 : ℝ))
      ((n : ℝ) ^ (-(1 / 20 : ℝ)) / (4 * (r + 1).factorial)) := by
    simpa only [Fintype.card_fin, k, a, D, hdiff] using
      sparse_nibble_exponents_paper_threshold
        (Nat.succ_le_iff.mpr (Nat.succ_pos r)) hqr hεhi hn hg hD
  have hkpos : 0 < k := by dsimp only [k]; omega
  have hN : (N : ℝ) ≤ G.card :=
    nibbleHorizon_le_graph hkpos P.graph_pos.le P.floor_pos.le P.floor_le_one
  have hfailure := nibbleFailureBound_le_of_margins hqr G P R S N hN
  have hsmall : nibbleFailureBound q G a D N < 1 := by
    apply hfailure.trans_lt
    simpa only [Fintype.card_fin] using paper_nibble_tail_tenth_lt_one
      (Nat.succ_le_iff.mpr (Nat.succ_pos r)) hqr hn
  have ha3 : a ^ 3 = (n : ℝ) ^ (-ε) := by
    dsimp only [a]
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    ring
  rw [← ha3] at hd
  obtain ⟨C, hsub, _, hdec, hbounded⟩ :=
    exists_packing_at_nibble_horizon hqr G H hHG P Q R hd hsmall
  exact ⟨C, hsub, hdec, hbounded⟩

theorem exists_nibble_of_graph_size_of_floor_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 3 ≤ q.choose (r + 1))
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ε : ℝ} (hε0 : 0 < ε) (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions (q.choose (r + 1)) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose (r + 1))))))
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (τ : ℝ) (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * (r + 1).factorial) ≤ G.card)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  exact exists_nibble_of_graph_size_at_floor_paper_threshold hqr hk hn hεhi le_rfl
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (by positivity)))
    hF G H τ hg hτ hHG hd

theorem exists_nibble_of_graph_size_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hk : 3 ≤ q.choose (r + 1))
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ε : ℝ} (hεlo : 3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε)
    (hεhi : ε ≤ 2 / 5)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (τ : ℝ) (hg : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * (r + 1).factorial) ≤ G.card)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  exact exists_nibble_of_graph_size_of_floor_paper_threshold hqr hk hn
    (paper_sparse_nibble_floor_gaps hqr hk hεlo).1 hεhi
    (sparse_nibble_floor_paper_threshold (by omega) hqr hk hεlo hn) G H τ hg hτ hHG hd

theorem exists_sparse_nibble_at_floor_paper_threshold {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ε p₀ : ℝ} (hεhi : ε ≤ 2 / 5)
    (hp : (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ)))) ≤ p₀) (hp₁ : p₀ ≤ 1)
    (hF : NibbleFloorConditions (q.choose (r + 1)) ((n : ℝ) ^ (-(ε / 3)))
      p₀)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (φ τ : ℝ) (hG : (G.card : ℝ) = φ * (n.choose (r + 1) : ℝ))
    (hφ : (n : ℝ) ^ (-((r + 1 : ℕ) : ℝ) / 3) ≤ φ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * p₀) := by
  have hrank : 2 ≤ r + 1 := by omega
  have hk := three_le_clique_size hrank hqr
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hg₂ := binomial_density_lower_paper_threshold (Nat.succ_le_iff.mpr (Nat.succ_pos r))
    hqr hn hqr.le (β := ((r + 1 : ℕ) : ℝ) / 3) (by simpa only [neg_div] using hφ)
  have hg : (n : ℝ) ^ (2 * ((r + 1 : ℕ) : ℝ) / 3) / (4 * (r + 1).factorial) ≤ G.card := by
    rw [hG, show 2 * ((r + 1 : ℕ) : ℝ) / 3 =
      ((r + 1 : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 3 by ring]
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le _)
      (by positivity : (0 : ℝ) < 2 * (r + 1).factorial)
      (by nlinarith only [(Nat.cast_nonneg (r + 1).factorial :
        (0 : ℝ) ≤ (r + 1).factorial)])).trans hg₂
  have hsize : (n : ℝ) ^ (19 / 20 : ℝ) / (4 * (r + 1).factorial) ≤ G.card := by
    have hrR : (2 : ℝ) ≤ (r + 1 : ℕ) := by exact_mod_cast hrank
    have hp := Real.rpow_le_rpow_of_exponent_le hn1
      (show (19 / 20 : ℝ) ≤ 2 * ((r + 1 : ℕ) : ℝ) / 3 by linarith only [hrR])
    exact (div_le_div_of_nonneg_right hp (by positivity)).trans hg
  exact exists_nibble_of_graph_size_at_floor_paper_threshold hqr hk hn hεhi hp hp₁ hF
    G H τ hsize hτ hHG hd

theorem exists_sparse_nibble_of_floor_paper_threshold {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ε : ℝ} (hε0 : 0 < ε) (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions (q.choose (r + 1)) ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * q.choose (r + 1))))))
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (φ τ : ℝ) (hG : (G.card : ℝ) = φ * (n.choose (r + 1) : ℝ))
    (hφ : (n : ℝ) ^ (-((r + 1 : ℕ) : ℝ) / 3) ≤ φ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  exact exists_sparse_nibble_at_floor_paper_threshold hr hqr hn hεhi le_rfl
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (by positivity)))
    hF G H φ τ hG hφ hτ hHG hd

theorem exists_sparse_nibble_paper_threshold {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ε : ℝ} (hεlo : 3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε)
    (hεhi : ε ≤ 2 / 5)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (φ τ : ℝ) (hG : (G.card : ℝ) = φ * (n.choose (r + 1) : ℝ))
    (hφ : (n : ℝ) ^ (-((r + 1 : ℕ) : ℝ) / 3) ≤ φ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  have hk := three_le_clique_size (by omega : 2 ≤ r + 1) hqr
  exact exists_sparse_nibble_of_floor_paper_threshold hr hqr hn
    (paper_sparse_nibble_floor_gaps hqr hk hεlo).1 hεhi
    (sparse_nibble_floor_paper_threshold (by omega) hqr hk hεlo hn)
    G H φ τ hG hφ hτ hHG hd

theorem exists_sparse_rankOne_nibble_at_floor_paper_threshold {q n : ℕ} (hq : 3 ≤ q)
    (hn : paperSizeThreshold q 1 ≤ n) {ε p₀ : ℝ}
    (hεhi : ε ≤ 2 / 5)
    (hp : (n : ℝ) ^ (-(ε / (3 * (q : ℝ)))) ≤ p₀) (hp₁ : p₀ ≤ 1)
    (hF : NibbleFloorConditions q ((n : ℝ) ^ (-(ε / 3)))
      p₀)
    (G : Hypergraph (Fin n) 1) (H : Finset (Block (Fin n) q)) (τ : ℝ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges 1 Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - 1) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - 1) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport 1 C) C ∧
        IsGraphBounded (G \ cliqueSupport 1 C)
          (3 * p₀) := by
  have hqr : 1 < q := by omega
  by_cases hg : (n : ℝ) ^ (19 / 20 : ℝ) / 4 ≤ G.card
  · simpa only [Nat.zero_add, Nat.choose_one_right] using
      exists_nibble_of_graph_size_at_floor_paper_threshold (r := 0) hqr
        (by simpa only [Nat.zero_add, Nat.choose_one_right] using hq) hn hεhi
        (by simpa only [Nat.zero_add, Nat.choose_one_right] using hp) hp₁
        (by simpa only [Nat.zero_add, Nat.choose_one_right] using hF) G H τ
        (by simpa only [Nat.zero_add, Nat.factorial_one, Nat.cast_one, mul_one] using hg)
        hτ hHG hd
  · refine ⟨∅, empty_subset _, ?_, ?_⟩
    · simp [IsDecomposition, cliqueSupport]
    · simp only [cliqueSupport, biUnion_empty, sdiff_empty]
      apply (isGraphBounded_one_iff _ _).mpr
      simp only [Fintype.card_fin]
      have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
      have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
      have hβ : ε / (3 * (q : ℝ)) ≤ 1 / 20 := by
        apply (div_le_iff₀ (by positivity)).mpr
        linarith only [hεhi, hqR]
      have hscale : (n : ℝ) ^ (19 / 20 : ℝ) ≤
          (n : ℝ) ^ (-(ε / (3 * (q : ℝ)))) * n := by
        rw [← Real.rpow_add_one hn0.ne']
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hβ])
      have hp0 := Real.rpow_nonneg hn0.le (19 / 20 : ℝ)
      have hscaled := mul_le_mul_of_nonneg_right hp hn0.le
      exact (lt_of_not_ge hg).trans_le (by nlinarith only [hscale, hp0, hscaled])

theorem exists_sparse_rankOne_nibble_of_floor_paper_threshold {q n : ℕ} (hq : 3 ≤ q)
    (hn : paperSizeThreshold q 1 ≤ n) {ε : ℝ}
    (hε0 : 0 < ε) (hεhi : ε ≤ 2 / 5)
    (hF : NibbleFloorConditions q ((n : ℝ) ^ (-(ε / 3)))
      ((n : ℝ) ^ (-(ε / (3 * (q : ℝ))))))
    (G : Hypergraph (Fin n) 1) (H : Finset (Block (Fin n) q)) (τ : ℝ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges 1 Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - 1) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - 1) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport 1 C) C ∧
        IsGraphBounded (G \ cliqueSupport 1 C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q : ℝ))))) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt (by omega : 1 < q)).le.trans hn
  exact exists_sparse_rankOne_nibble_at_floor_paper_threshold hq hn hεhi le_rfl
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (by positivity)))
    hF G H τ hτ hHG hd

theorem exists_sparse_rankOne_nibble_paper_threshold {q n : ℕ} (hq : 3 ≤ q)
    (hn : paperSizeThreshold q 1 ≤ n) {ε : ℝ}
    (hεlo : 3 * (q : ℝ) * paperRho q 1 ≤ ε) (hεhi : ε ≤ 2 / 5)
    (G : Hypergraph (Fin n) 1) (H : Finset (Block (Fin n) q)) (τ : ℝ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges 1 Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - 1) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - 1) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport 1 C) C ∧
        IsGraphBounded (G \ cliqueSupport 1 C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q : ℝ))))) := by
  have hqr : 1 < q := by omega
  have hk : 3 ≤ q.choose 1 := by simpa only [Nat.choose_one_right] using hq
  have hlo : 3 * (q.choose 1 : ℝ) * paperRho q 1 ≤ ε := by
    simpa only [Nat.choose_one_right] using hεlo
  apply exists_sparse_rankOne_nibble_of_floor_paper_threshold hq hn
    (paper_sparse_nibble_floor_gaps hqr hk hlo).1 hεhi _ G H τ hτ hHG hd
  simpa only [Nat.choose_one_right] using
    sparse_nibble_floor_paper_threshold (by norm_num : 1 ≤ 1) hqr hk hlo hn

theorem exists_sparse_nibble_all_ranks_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ε : ℝ} (hεlo : 3 * (q.choose (r + 1) : ℝ) * paperRho q (r + 1) ≤ ε)
    (hεhi : ε ≤ 2 / 5)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (φ τ : ℝ) (hG : (G.card : ℝ) = φ * (n.choose (r + 1) : ℝ))
    (hφ : (n : ℝ) ^ (-((r + 1 : ℕ) : ℝ) / 3) ≤ φ)
    (hτ : (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ τ)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * (n.choose (q - (r + 1)) : ℝ)| ≤
        (n : ℝ) ^ (-ε) * (τ * (n.choose (q - (r + 1)) : ℝ))) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          (3 * (n : ℝ) ^ (-(ε / (3 * (q.choose (r + 1) : ℝ))))) := by
  by_cases hr : 1 ≤ r
  · exact exists_sparse_nibble_paper_threshold hr hqr hn hεlo hεhi G H φ τ hG hφ hτ hHG hd
  · have hr0 : r = 0 := by omega
    subst r
    by_cases hq : 3 ≤ q
    · simpa only [Nat.zero_add, Nat.choose_one_right] using
        exists_sparse_rankOne_nibble_paper_threshold hq hn
          (by simpa only [Nat.zero_add, Nat.choose_one_right] using hεlo) hεhi G H τ hτ hHG hd
    · have hq2 : q = 2 := by omega
      subst q
      have hnNat : 1 ≤ n :=
        (paperSizeThreshold_one_lt (by norm_num : 1 < 2)).le.trans hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
      have hsize : (n : ℝ) ^ (2 / 3 : ℝ) ≤ G.card := by
        have hprod : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ (-(1 / 3 : ℝ)) * n := by
          rw [← Real.rpow_add_one hn0.ne']
          norm_num
        rw [hprod, hG]
        simpa only [Nat.zero_add, Nat.choose_one_right, Nat.cast_one, neg_div] using
          mul_le_mul_of_nonneg_right hφ hn0.le
      have hdegrees : ∀ e ∈ G,
          |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - τ * n| ≤
            (n : ℝ) ^ (-ε) * (τ * n) := by
        simpa only [Nat.zero_add, Nat.reduceSub, Nat.choose_one_right] using hd
      simpa only [Nat.zero_add, Nat.choose_one_right, Nat.cast_ofNat,
        show (3 : ℝ) * 2 = 6 by norm_num] using
          exists_pair_nibble_paper_threshold hn hεhi G H τ hsize hτ hHG hdegrees

end Arxiv2411_18291
