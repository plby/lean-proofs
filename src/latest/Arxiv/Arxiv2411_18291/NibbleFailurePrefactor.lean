import Arxiv.Arxiv2411_18291.NibbleTrackExponents
import Mathlib.Data.Nat.Choose.Bounds

/-! # Polynomial numbers of tracks and steps in the simultaneous failure bound -/

open Finset
open scoped BigOperators

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] {q r : ℕ}

theorem graph_card_le_vertex_pow (G : Hypergraph V r) : G.card ≤ Fintype.card V ^ r := by
  calc
    _ ≤ Fintype.card (Block V r) := card_le_univ G
    _ = (Fintype.card V).choose r := Fintype.card_finset_len r
    _ ≤ _ := Nat.choose_le_pow _ _

theorem nibbleTrack_card_le (hn : 1 ≤ Fintype.card V) :
    Fintype.card (NibbleTrack V r) ≤ 5 * Fintype.card V ^ (r + 1) := by
  have hupper := Nat.choose_le_pow (Fintype.card V) (r + 1)
  have hlower := Nat.choose_le_pow (Fintype.card V) r
  have hpow : Fintype.card V ^ r ≤ Fintype.card V ^ (r + 1) := by
    calc
      _ = Fintype.card V ^ r * 1 := by rw [mul_one]
      _ ≤ Fintype.card V ^ r * Fintype.card V := Nat.mul_le_mul_left _ hn
      _ = _ := by rw [pow_succ]
  have hone : 1 ≤ Fintype.card V ^ (r + 1) := one_le_pow₀ hn
  simp only [NibbleTrack, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_finset_len]
  omega

theorem nibbleFailureBound_le_of_exponents (G : Hypergraph V (r + 1)) (a D : ℝ)
    (N : ℕ) {ξ : ℝ} (hξ : ∀ t, ξ ≤ nibbleTrackExponent q G a D N t) :
    nibbleFailureBound q G a D N ≤
      (Fintype.card (NibbleTrack V r) : ℝ) * N * Real.exp (-ξ) := by
  rw [nibbleFailureBound_eq_sum]
  calc
    _ ≤ ∑ _t : NibbleTrack V r, (N : ℝ) * Real.exp (-ξ) := by
      apply sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (hξ t)))
        (Nat.cast_nonneg _)
    _ = _ := by simp [mul_assoc]

theorem nibbleFailureBound_le_polynomial (G : Hypergraph V (r + 1)) (a D : ℝ)
    (N : ℕ) (hn : 1 ≤ Fintype.card V) (hN : (N : ℝ) ≤ G.card)
    {ξ : ℝ} (hξ : ∀ t, ξ ≤ nibbleTrackExponent q G a D N t) :
    nibbleFailureBound q G a D N ≤
      5 * (Fintype.card V : ℝ) ^ (2 * (r + 1)) * Real.exp (-ξ) := by
  have hcard : (Fintype.card (NibbleTrack V r) : ℝ) ≤
      5 * (Fintype.card V : ℝ) ^ (r + 1) := by exact_mod_cast nibbleTrack_card_le (r := r) hn
  have hg : (G.card : ℝ) ≤ (Fintype.card V : ℝ) ^ (r + 1) := by
    exact_mod_cast graph_card_le_vertex_pow G
  have hprod := mul_le_mul hcard (hN.trans hg) (Nat.cast_nonneg N) (by positivity)
  calc
    _ ≤ (Fintype.card (NibbleTrack V r) : ℝ) * N * Real.exp (-ξ) :=
      nibbleFailureBound_le_of_exponents G a D N hξ
    _ ≤ (5 * (Fintype.card V : ℝ) ^ (r + 1) * (Fintype.card V : ℝ) ^ (r + 1)) *
        Real.exp (-ξ) := mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    _ = _ := by rw [show 2 * (r + 1) = (r + 1) + (r + 1) by omega, pow_add]; ring

end Arxiv2411_18291.CliqueRemovalProcess
