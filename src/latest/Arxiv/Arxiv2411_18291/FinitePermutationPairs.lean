import Arxiv.Arxiv2411_18291.FinitePermutationPairNumerics
import Arxiv.Arxiv2411_18291.TypicalPermutationPairs

/-! # Joint probabilities of permuted clique families at n0 -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem permuted_clique_pair_probability_paper_threshold {q r n h k s : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hk : k ≤ q)
    (hqh : q.choose (r + 1) ≤ h) (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    [MeasurableSpace (Equiv.Perm (Fin n))] [MeasurableSingletonClass (Equiv.Perm (Fin n))]
    (P : IntersectingBlockPair (Fin n) k k s) (hsr : s < r + 1)
    (D E : Finset (Block (Fin n) k)) (hD : D ⊆ cliqueFamily K k) (hE : E ⊆ cliqueFamily K k) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).toMeasure.real
      {σ | P.val.1 ∈ mapGraph σ.toEmbedding D ∧ P.val.2 ∈ mapGraph σ.toEmbedding E} ≤
      (1 + 16 * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 6))) *
        density K ^ (2 * k.choose (r + 1)) := by
  have hnNat : 0 < n :=
    Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hc0 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 / 10 : ℝ))
  have hε := Real.rpow_nonneg (Nat.cast_nonneg n) (-(paperAlpha q (r + 1) / 6))
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hkchoose : k.choose (r + 1) ≤ q.choose (r + 1) := Nat.choose_le_choose _ hk
  have hpow : density K ^ q.choose (r + 1) ≤ density K ^ k.choose (r + 1) :=
    pow_le_pow_of_le_one (density_nonneg K) (density_le_one K) hkchoose
  have hsize : (k : ℝ) ≤ (2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ))) * (Fintype.card (Fin n) * density K ^ k.choose (r + 1)) := by
    rw [Fintype.card_fin, show 2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ)) = (n : ℝ) ^ (-(1 / 10 : ℝ)) by ring]
    calc
      _ ≤ (q : ℝ) := by exact_mod_cast hk
      _ ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n * density K ^ q.choose (r + 1)) :=
        modular_host_clique_size_paper_threshold hqr hn K hd
      _ ≤ _ := by gcongr
  have herror : (2 * (n : ℝ) ^ (-(1 / 10 : ℝ))) * k * 2 ^ k ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 6)) := by
    have he := typical_count_error_at_exponent_paper_threshold hqr hn
      (by linarith only [hα] : paperAlpha q (r + 1) + paperAlpha q (r + 1) / 6 ≤ 1 / 10)
    have hm : (2 * (n : ℝ) ^ (-(1 / 10 : ℝ))) * k * 2 ^ k ≤
        (2 * (n : ℝ) ^ (-(1 / 10 : ℝ))) * q * 2 ^ q := by gcongr; norm_num
    linarith only [hm, he, hε]
  have hchoose : ∀ a ≤ k, ∀ b ≤ k,
      (1 - (n : ℝ) ^ (-(paperAlpha q (r + 1) / 6))) *
        (Fintype.card (Fin n) : ℝ) ^ b / b.factorial ≤
          ((Fintype.card (Fin n) - a).choose b : ℝ) := by
    intro a ha b hb
    simpa only [Fintype.card_fin] using uniform_shifted_choose_paper_threshold hqr hn
      (by linarith only [hα] : paperAlpha q (r + 1) + paperAlpha q (r + 1) / 6 ≤ 1)
      a (ha.trans hk) b (hb.trans hk)
  exact hT.permuted_clique_pair_probability_le (hkchoose.trans hqh)
    (by linarith only [hc0]) (by positivity) (paper_host_error_small hqr hn) hsize
    (by simpa only [Fintype.card_fin] using hnNat) hε (paper_sixth_alpha_error_small hqr hn)
    herror hchoose P hsr D E hD hE

end Arxiv2411_18291
