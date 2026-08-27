import Arxiv.Arxiv2411_18291.CliqueCountEstimates
import Arxiv.Arxiv2411_18291.SaturationCounts

/-!
# Comparing face, edge, and total clique counts

The face main term is the edge main term times `n*d/(q-r+1)` in the
paper's edge-rank notation. Double counting over the host then compares
the edge mean with the total number of cliques. These comparisons turn
the saturation bounds into small relative losses.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem cliqueMainTerm_face_identity (n p : ℝ) {q r : ℕ} (hqr : r + 1 ≤ q) :
    ((q - r : ℕ) : ℝ) * cliqueMainTerm n p q (r + 1) r =
      n * p * cliqueMainTerm n p q (r + 1) (r + 1) := by
  have hstep : q - r = (q - (r + 1)) + 1 := by omega
  have hk : 1 ≤ q.choose (r + 1) := Nat.choose_pos hqr
  have hpow : p ^ q.choose (r + 1) = p ^ (q.choose (r + 1) - 1) * p := by
    conv_lhs => rw [show q.choose (r + 1) = (q.choose (r + 1) - 1) + 1 by omega]
    rw [pow_succ]
  unfold cliqueMainTerm
  rw [Nat.choose_self, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self r), Nat.sub_zero,
    hstep, Nat.factorial_succ, Nat.cast_mul, pow_succ, hpow]
  field_simp

theorem cliqueMainTerm_face_le {n p : ℝ} (hn : 0 ≤ n) (hp : 0 ≤ p)
    {q r : ℕ} (hqr : r + 1 ≤ q) :
    cliqueMainTerm n p q (r + 1) r ≤ n * p * cliqueMainTerm n p q (r + 1) (r + 1) := by
  rw [← cliqueMainTerm_face_identity n p hqr]
  have h : (1 : ℝ) ≤ (q - r : ℕ) := by exact_mod_cast (show 1 ≤ q - r by omega)
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (cliqueMainTerm_nonneg hn hp _ _ _)

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem sum_clique_load_on_host (K : Hypergraph V r) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges r Q ⊆ K) :
    (∑ e ∈ K, (D.filter fun Q => e.val ⊆ Q.val).card) = q.choose r * D.card := by
  have hs : (∑ e ∈ K, (D.filter fun Q => e.val ⊆ Q.val).card) =
      ∑ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card := by
    apply sum_subset (subset_univ K)
    intro e _ heK
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro Q hQ
    exact heK (hD Q (mem_filter.mp hQ).1 ((mem_cliqueEdges _ _).mpr (mem_filter.mp hQ).2))
  exact hs.trans (sum_clique_face_load D r)

theorem host_clique_mean_le (K : Hypergraph V r) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges r Q ⊆ K) {μ ε : ℝ} (hμ : 0 ≤ μ) (hε : ε ≤ 1 / 2)
    (hcount : ∀ e ∈ K, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ε * μ) :
    (K.card : ℝ) * μ ≤ 2 * (q.choose r : ℝ) * D.card := by
  have he (e : Block V r) (heK : e ∈ K) : μ / 2 ≤ ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) := by
    have hl := (abs_le.mp (hcount e heK)).1
    nlinarith [mul_le_mul_of_nonneg_right hε hμ]
  have hs : (K.card : ℝ) * (μ / 2) ≤ (q.choose r : ℝ) * D.card := by
    calc
      _ = ∑ _ ∈ K, μ / 2 := by simp
      _ ≤ ∑ e ∈ K, ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) := sum_le_sum he
      _ = _ := by rw [← Nat.cast_sum, sum_clique_load_on_host K D hD, Nat.cast_mul]
  nlinarith

end Arxiv2411_18291
