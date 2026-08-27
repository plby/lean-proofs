import Arxiv.Arxiv2411_18291.PrescribedCliqueFamily
import Arxiv.Arxiv2411_18291.FiniteFocusingFamily
import Arxiv.Arxiv2411_18291.FiniteNearFrameNumerics
import Arxiv.Arxiv2411_18291.SharedDecoderNumerics

/-! # Geometric focusing for every reserve edge at n0

The reserve need not be disjoint from the coloured host. Independent
choices provide the geometric conclusion even for edges already in it.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_all_edge_focusing_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B E : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) *
        (n : ℝ) ^ (q - (r + 1)) ≤ (puncturedCliques E e q).card) :
    ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      ∀ e ∈ B, ∃ Q ∈ F, e.val ⊆ Q.val ∧ (cliqueEdges (r + 1) Q).erase e ⊆ E := by
  have hnNat := (shared_decoder_sampling_size hqr hn).2.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hqn : q ≤ n := by have h := (shared_decoder_sampling_size hqr hn).1; omega
  have hk : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr.le
  have hfailure : (n.choose r : ℝ) * Real.exp
      (-(2 * (r + 1).factorial * (n : ℝ) ^ (-paperRho q (r + 1)) * n /
        (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) / 3)) < 1 := by
    apply lt_of_le_of_lt _ (paper_focusing_failure_lt_one hqr hn)
    have hnonneg : (0 : ℝ) ≤ n.choose r * Real.exp
        (-(2 * (r + 1).factorial * (n : ℝ) ^ (-paperRho q (r + 1)) * n /
          (n : ℝ) ^ (-paperFocusingExponent q (r + 1)) / 3)) := by positivity
    simpa only [mul_assoc] using le_mul_of_one_le_left hnonneg hk
  obtain ⟨Q, hQ, hF⟩ := exists_prescribed_clique_family hqr.le
    (by simpa only [Fintype.card_fin] using hqn)
    (by simpa only [Fintype.card_fin] using hnNat) B (fun e => puncturedCliques E e q)
    (Real.rpow_nonneg hn0.le _) (Real.rpow_pos_of_pos hn0 _) hB
    (fun e Q h => ((mem_puncturedCliques E e Q).mp h).1)
    (by simpa only [Fintype.card_fin] using hcount)
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfailure)
  have hcoef : ((q - r : ℕ) : ℝ) *
      (4 * (r + 1).factorial * (n : ℝ) ^ (-paperRho q (r + 1)) /
        (n : ℝ) ^ (-paperFocusingExponent q (r + 1))) ≤
      (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) := by
    have hkr : ((q - r : ℕ) : ℝ) ≤ q.choose (r + 1) := by
      exact_mod_cast (Nat.sub_le q r).trans (q_le_choose_succ hqr)
    calc
      _ = ((q - r : ℕ) : ℝ) * (4 * (r + 1).factorial *
          (n : ℝ) ^ (-(paperRho q (r + 1) - paperFocusingExponent q (r + 1)))) := by
        rw [mul_div_assoc, rpow_density_ratio hn0]
      _ ≤ (n : ℝ) ^ (-paperRho q (r + 1)) + q.choose (r + 1) *
          (4 * (r + 1).factorial *
            (n : ℝ) ^ (-(paperRho q (r + 1) - paperFocusingExponent q (r + 1)))) := by
        exact (mul_le_mul_of_nonneg_right hkr (by positivity)).trans
          (le_add_of_nonneg_left (by positivity))
      _ ≤ _ := focusing_degree_bound_paper_threshold hqr hn
  refine ⟨univ.image Q, hF.mono hcoef, ?_⟩
  intro e he
  refine ⟨Q ⟨e, he⟩, mem_image.mpr ⟨⟨e, he⟩, mem_univ _, rfl⟩, ?_⟩
  exact (isPuncturedClique_iff E e (Q ⟨e, he⟩)).mp
    ((mem_puncturedCliques E e (Q ⟨e, he⟩)).mp (hQ ⟨e, he⟩))

end Arxiv2411_18291
