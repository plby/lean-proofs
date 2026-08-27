import Arxiv.Arxiv2411_18291.EdgeCapNumerics
import Arxiv.Arxiv2411_18291.TypicalEdgeCappedGenerators
import Arxiv.Arxiv2411_18291.FiniteModularHostNumerics
import Arxiv.Arxiv2411_18291.FiniteModularErrorBudget
import Arxiv.Arxiv2411_18291.FiniteTypicalHost

/-! # Modular generation with small edge multiplicity at the paper's threshold

Relaxing the relative error to `n^(-alpha/60)` allows an edge cap at most
`n^(alpha/20)`. The original face-density estimate is retained. These are
actual generators and a good host, not an additional construction hypothesis.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_edge_capped_modular_generators_paper_threshold {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hqh : q.choose (r + 1) ≤ h) (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
      IsCliqueFamilyBounded r C.generators
        (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      (∀ e : Block (Fin n) (r + 1),
        ((C.generators.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
          (n : ℝ) ^ (paperAlpha q (r + 1) / 20)) ∧
      C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) ≤
        ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) ^ 2 * (cliqueFamily K q).card ∧
      ((K \ C.good).card : ℝ) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card ∧
      ∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1) := by
  have hnNat : 0 < n :=
    Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  let δ := (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))
  let faceCap := ⌊(n : ℝ) ^ (1 - 7 * paperAlpha q (r + 1) / 10)⌋₊
  let edgeCap := modularEdgeCap q (r + 1) N δ
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδ1 : δ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1
    (by linarith only [paperAlpha_pos hqr])
  have hδOld : (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ δ :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [paperAlpha_pos hqr])
  have hsq : 2 * ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) / 4) ^ 2 ≤ δ ^ 2 := by
    have hh := sq_le_sq₀ (Real.rpow_nonneg hn0.le _) hδ.le |>.mpr hδOld
    nlinarith only [hh, sq_nonneg ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)))]
  obtain ⟨hdlo, hdhi⟩ := paper_host_density_bounds hqr hn K hd
  obtain ⟨hcap, hθ, hsmall⟩ := generator_cap_quarter_error_paper_threshold hqr hn hNb
  have hp : 0 < density K := (by positivity :
    (0 : ℝ) < (1 / 2 : ℝ) * (n : ℝ) ^ (-paperAlpha q (r + 1))).trans_le hdlo
  have hc0 := Real.rpow_nonneg hn0.le (-(1 / 10 : ℝ))
  have hsize : (q : ℝ) ≤ (2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ))) * (Fintype.card (Fin n) * density K ^ q.choose (r + 1)) := by
    rw [Fintype.card_fin, show 2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ)) = (n : ℝ) ^ (-(1 / 10 : ℝ)) by ring]
    exact modular_host_clique_size_paper_threshold hqr hn K hd
  have hfaceBudget : (8 * q.choose (r + 1) * q.choose r * N : ℝ) *
      Fintype.card (Fin n) * density K ≤ faceCap * δ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg faceCap : (0 : ℝ) ≤ faceCap)
    have hb := mul_le_mul_of_nonneg_left (hsmall (density K) hdhi) (by norm_num : (0 : ℝ) ≤ 2)
    rw [Fintype.card_fin]
    dsimp only [faceCap] at hh ⊢
    nlinarith only [hh, hb]
  have herror : (2 * (n : ℝ) ^ (-(1 / 10 : ℝ))) * q * 2 ^ q ≤ δ / 2 :=
    (generator_count_error_paper_threshold hqr hn).trans
      (div_le_div_of_nonneg_right hδOld (by norm_num))
  obtain ⟨C, hF, hE, hcard, hsat, hbad, hcount⟩ :=
    exists_good_edge_capped_generating_data N hN hT hqh hqr.le
      (by simpa only [Fintype.card_fin] using hnNat) hp (by linarith only [hc0])
      (by positivity) (paper_host_error_small hqr hn) hsize faceCap edgeCap hcap
      (modularEdgeCap_pos hqr.le hN hδ) hδ hδ1 herror
      (by simpa only [Fintype.card_fin] using hθ) hfaceBudget
      (modularEdgeCap_budget q (r + 1) N hδ)
  refine ⟨C, hF, ?_, hcard, hsat, hbad, ?_⟩
  · intro e
    exact (by exact_mod_cast hE e :
      ((C.generators.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ edgeCap).trans
        (modularEdgeCap_le_paper_threshold hqr hn hN hNb)
  · simpa only [Fintype.card_fin] using hcount

theorem exists_sparse_edge_capped_modular_generators_paper_threshold {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        (∀ e : Block (Fin n) (r + 1),
          ((C.generators.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
            (n : ℝ) ^ (paperAlpha q (r + 1) / 20)) ∧
        C.generators.card ≤ N * K.card ∧
        (C.saturated.card : ℝ) ≤
          ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) ^ 2 * (cliqueFamily K q).card ∧
        ((K \ C.good).card : ℝ) ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card ∧
        ∀ e ∈ C.good,
          |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
            cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
            (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) *
              cliqueMainTerm n (density K) q (r + 1) (r + 1) := by
  obtain ⟨K, hT, hd⟩ := exists_typicalGraph_paper_alpha_threshold hqr hn
    ((Nat.choose_pos hqr.le).trans_le hqh) hH
  exact ⟨K, hT, hd,
    exists_edge_capped_modular_generators_paper_threshold hqr hn hN hNb hqh K hT hd⟩

end Arxiv2411_18291
