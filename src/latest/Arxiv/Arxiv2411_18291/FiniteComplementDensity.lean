import Arxiv.Arxiv2411_18291.GraphBoundedness
import Arxiv.Arxiv2411_18291.SaturationCounts

/-! # Finite density estimates from bounded face degrees -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

theorem IsGraphBounded.total_degree_le {G : Hypergraph V (r + 1)} {θ : ℝ}
    (hG : IsGraphBounded G θ) :
    (r + 1 : ℝ) * G.card ≤ (Fintype.card V).choose r * θ * Fintype.card V := by
  have heq : (r + 1 : ℝ) * G.card =
      ∑ S : Block V r, ((G.filter fun e => S.val ⊆ e.val).card : ℝ) := by
    have hh := sum_clique_face_load G r
    rw [Nat.choose_succ_self_right] at hh
    exact_mod_cast hh.symm
  calc
    _ = _ := heq
    _ ≤ ∑ _S : Block V r, θ * Fintype.card V :=
      sum_le_sum fun S _ => (hG S).le
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Block, Fintype.card_finset_len]
      ring

theorem IsGraphBounded.card_le_twice_density {G : Hypergraph V (r + 1)} {θ : ℝ}
    (hG : IsGraphBounded G θ) (hθ : 0 ≤ θ) (hn : 2 * (r + 1) ≤ Fintype.card V) :
    (G.card : ℝ) ≤ 2 * θ * (Fintype.card V).choose (r + 1) := by
  let n := Fintype.card V
  have hnr : (n : ℝ) ≤ 2 * ((n - r : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (n - r) by dsimp only [n]; omega)
  have hchoose : (n.choose (r + 1) : ℝ) * (r + 1) =
      (n.choose r : ℝ) * (n - r : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq n r
  have hscale := mul_le_mul_of_nonneg_left hnr
    (mul_nonneg hθ (Nat.cast_nonneg (n.choose r)))
  apply le_of_mul_le_mul_left _ (by positivity : (0 : ℝ) < r + 1)
  calc
    (r + 1 : ℝ) * G.card ≤ (n.choose r : ℝ) * θ * n := hG.total_degree_le
    _ ≤ 2 * θ * ((n.choose r : ℝ) * (n - r : ℕ)) := by nlinarith only [hscale]
    _ = (r + 1 : ℝ) * (2 * θ * n.choose (r + 1)) := by rw [← hchoose]; ring

theorem dense_of_bounded_complement_finite {G : Hypergraph V (r + 1)} {θ : ℝ}
    (hG : IsGraphBounded (complete V (r + 1) \ G) θ)
    (hθ : 0 ≤ θ) (hθsmall : θ < 1 / 4) (hn : 2 * (r + 1) ≤ Fintype.card V) :
    (1 / 2 : ℝ) * (Fintype.card V).choose (r + 1) < G.card := by
  have hc := hG.card_le_twice_density hθ hn
  have hcount : ((complete V (r + 1) \ G).card : ℝ) + G.card =
      (Fintype.card V).choose (r + 1) := by
    have hh := card_sdiff_add_card_eq_card (subset_univ G)
    simpa only [complete, card_univ, Block, Fintype.card_finset_len, Nat.cast_add] using
      (congrArg (fun x : ℕ => (x : ℝ)) hh)
  have hp : (0 : ℝ) < (Fintype.card V).choose (r + 1) := by
    exact_mod_cast Nat.choose_pos (show r + 1 ≤ Fintype.card V by omega)
  have hsmall := mul_lt_mul_of_pos_right (show 2 * θ < 1 / 2 by linarith only [hθsmall]) hp
  linarith only [hc, hcount, hsmall]

end Arxiv2411_18291
