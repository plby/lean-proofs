import Arxiv.Arxiv2411_18291.AsymptoticBalancedRepresentatives
import Arxiv.Arxiv2411_18291.ExplicitAbsorberGreedyTail

/-! # Balanced clique representatives at the printed finite threshold -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem representative_failure_lt_one_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ρ θ C : ℝ} (hρ : ρ ≤ 2 / 5) (hθ : (n : ℝ) ^ (-ρ) ≤ θ)
    (hC : 0 < C) (hsize : C ≤ ((n.sqrt + 1 : ℕ) : ℝ)) :
    (n.choose r : ℝ) * Real.exp (-(θ * n / (3 * C))) < 1 := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn1
  have hnat : (n.sqrt : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hsize' : C ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    push_cast at hsize
    linarith only [hsize, hsqrt, hnat]
  have hscale : (n : ℝ) ^ (1 / 2 - ρ) * (n : ℝ) ^ (1 / 2 : ℝ) =
      (n : ℝ) ^ (-ρ) * n := by
    rw [← Real.rpow_add hnpos, show (1 / 2 - ρ) + 1 / 2 = -ρ + 1 by ring,
      Real.rpow_add hnpos, Real.rpow_one]
  have hprod : (n : ℝ) ^ (1 / 2 - ρ) * C ≤ 2 * ((n : ℝ) ^ (-ρ) * n) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 2 - ρ) * (2 * (n : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsize' (Real.rpow_nonneg hnpos.le _)
      _ = _ := by rw [← hscale]; ring
  have hB := mul_le_mul_of_nonneg_right hθ hnpos.le
  have hp : 0 ≤ (n : ℝ) ^ (-ρ) * n := by positivity
  have hlow : (n : ℝ) ^ (1 / 2 - ρ) / 12 ≤ θ * n / (3 * C) := by
    apply (le_div_iff₀ (by positivity : 0 < 3 * C)).mpr
    nlinarith only [hprod, hB, hp]
  have hpower := Real.rpow_le_rpow_of_exponent_le hn1
    (by linarith only [hρ] : (1 / 10 : ℝ) ≤ 1 / 2 - ρ)
  have hprob : Real.exp (-(θ * n / (3 * C))) ≤
      Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ) / 12)) := by
    apply Real.exp_le_exp.mpr
    linarith only [hlow, hpower]
  have hcount : (n.choose r : ℝ) ≤ 6 * (n : ℝ) ^ (r + 1) := by
    calc
      _ ≤ (n : ℝ) ^ r := by exact_mod_cast Nat.choose_le_pow n r
      _ ≤ (n : ℝ) ^ (r + 1) := pow_le_pow_right₀ hn1 (Nat.le_succ r)
      _ ≤ _ := le_mul_of_one_le_left (pow_nonneg hnpos.le _) (by norm_num)
  exact (mul_le_mul hcount hprob (Real.exp_pos _).le (by positivity)).trans_lt
    (boost_sampling_tail_lt_one (by omega) hqr.le
      ((boost_threshold_le_paper_threshold hqr).trans hn))

theorem exists_balanced_clique_representatives_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ρ θ : ℝ} (hρ : ρ ≤ 2 / 5) (hθ : (n : ℝ) ^ (-ρ) ≤ θ)
    (D : Finset (Block (Fin n) q)) (hD : IsCliqueFamilyBounded r D θ)
    (G : Finset (Finset (Block (Fin n) q))) (hne : ∀ c ∈ G, c.Nonempty)
    (hsub : ∀ c ∈ G, c ⊆ D) (hdis : Pairwise fun c d : G => Disjoint c.val d.val)
    (hsize : ∀ c ∈ G, c.card ≤ n.sqrt + 1) :
    ∃ Q : G → Block (Fin n) q, (∀ c, Q c ∈ c.val) ∧ ∀ T : Block (Fin n) r,
      (representativeDegree G Q T.val : ℝ) ≤ 2 * θ * n := by
  have hC : (0 : ℝ) < (n.sqrt + 1 : ℕ) := by positivity
  have hfail := representative_failure_lt_one_paper_threshold hqr hn hρ hθ hC le_rfl
  have hcard (c) (hc : c ∈ G) : (c.card : ℝ) ≤ (n.sqrt + 1 : ℕ) := by
    exact_mod_cast hsize c hc
  obtain ⟨Q, hQ, hbound⟩ := exists_balanced_clique_representatives hqr.le D G hne hsub hdis
    hD hC hcard (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfail)
  exact ⟨Q, hQ, by simpa only [Fintype.card_fin] using hbound⟩

end Arxiv2411_18291
