import Arxiv.Arxiv2411_18291.ExplicitNibbleParameters
import Arxiv.Arxiv2411_18291.ExplicitNibbleTail
import Arxiv.Arxiv2411_18291.NibbleUniformExponent

/-! # The paper's finite nibble construction when cliques have at least three edges -/

open Finset

noncomputable section

namespace Arxiv2411_18291

open CliqueRemovalProcess

theorem exists_nibble_paper_threshold_of_three_le (q r n : ℕ) (hqr : r + 1 < q)
    (hk : 3 ≤ q.choose (r + 1)) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (G : Hypergraph (Fin n) (r + 1)) (H : Finset (Block (Fin n) q))
    (hG : (1 / 2 : ℝ) * (n.choose (r + 1) : ℝ) < G.card)
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G)
    (hd : ∀ e ∈ G,
      |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - (n.choose (q - (r + 1)) : ℝ) / 2| ≤
        (n : ℝ) ^ (-(1 / 3 : ℝ)) * ((n.choose (q - (r + 1)) : ℝ) / 2)) :
    ∃ C : Finset (Block (Fin n) q), C ⊆ H ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C)
          ((n : ℝ) ^ (-(3 * q.choose (r + 1) * paperRho q (r + 1)))) := by
  let k := q.choose (r + 1)
  let a := (n : ℝ) ^ (-(1 / 9 : ℝ))
  let D := (n.choose (q - (r + 1)) : ℝ) / 2
  let p₀ := (n : ℝ) ^ (-(1 / (9 * k) : ℝ))
  let N := nibbleHorizon k (G.card : ℝ) p₀
  have hdiff : q - (r + 1) + 1 = q - r := by omega
  obtain ⟨hP, hQ, hR, hS⟩ := nibble_parameters_paper_threshold (by omega) hqr hk hn hG.le
  have P : NibbleComparisonParameters k a G.card D p₀
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) := by
    simpa only [Fintype.card_fin, k, a, D, p₀] using hP
  have Q : NibbleCountConditions k a G.card D p₀
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) := by
    simpa only [Fintype.card_fin, k, a, D, p₀] using hQ
  have R : NibbleEndConditions k a G.card (Fintype.card (Fin n)) p₀ (q - r) := by
    simpa only [Fintype.card_fin, k, a, p₀, hdiff] using hR
  have S : NibbleExponentConditions k (q - r) a G.card D (Fintype.card (Fin n))
      ((Fintype.card (Fin n) : ℝ) ^ (q - (r + 1) - 1)) ((n : ℝ) ^ (1 / 6 : ℝ))
      (1 / (4 * (r + 1).factorial)) := by
    simpa only [Fintype.card_fin, k, a, D, hdiff] using hS
  have hkpos : 0 < k := by dsimp only [k]; omega
  have hN : (N : ℝ) ≤ G.card :=
    nibbleHorizon_le_graph hkpos P.graph_pos.le P.floor_pos.le P.floor_le_one
  have hfailure := nibbleFailureBound_le_of_margins hqr G P R S N hN
  have hsmall : nibbleFailureBound q G a D N < 1 := by
    apply hfailure.trans_lt
    simpa only [Fintype.card_fin] using paper_nibble_tail_lt_one (by omega) hqr hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have ha3 : a ^ 3 = (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
    dsimp only [a]
    rw [← Real.rpow_mul_natCast hnpos.le]
    norm_num
  rw [← ha3] at hd
  obtain ⟨C, hsub, _, hdec, hbounded⟩ :=
    exists_packing_at_nibble_horizon hqr G H hHG P Q R hd hsmall
  exact ⟨C, hsub, hdec, hbounded.mono (paper_nibble_leave_scale (by omega) hqr hn)⟩

end Arxiv2411_18291
