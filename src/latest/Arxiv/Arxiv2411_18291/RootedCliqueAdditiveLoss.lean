import Arxiv.Arxiv2411_18291.RootedCliqueBounds
import Mathlib.Tactic

/-! # Iterating clique counts with a sum of extension losses -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem additive_loss_step {N A b : ℝ} (hN : 0 < N) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (t : ℕ) :
    (1 - (A + b) / N) * N ^ (t + 1) ≤ (1 - A / N) * N ^ t * (N - b) := by
  have heq : (1 - A / N) * N ^ t * (N - b) - (1 - (A + b) / N) * N ^ (t + 1) =
      A * b / N * N ^ t := by
    rw [pow_succ]
    field_simp
    ring
  have hpos : 0 ≤ A * b / N * N ^ t := by positivity
  linarith only [heq, hpos]

theorem rootedCliques_factorial_lower_additive {V : Type*} [Fintype V] [DecidableEq V]
    {r a : ℕ} (G : Hypergraph V (r + 1)) (I : Block V a) (q : ℕ)
    {N : ℝ} (hN : 0 < N) (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (htotal : ∑ i ∈ range (q - a), b i ≤ N)
    (hstep : ∀ t, a + t < q → ∀ U ∈ rootedCliques G I (a + t),
      N - b t ≤ ((cliqueNextVertices G U).card : ℝ))
    (t : ℕ) (ht : a + t ≤ q) :
    (1 - (∑ i ∈ range t, b i) / N) * N ^ t ≤
      (t.factorial : ℝ) * (rootedCliques G I (a + t)).card := by
  induction t with
  | zero => simp [rootedCliques_base]
  | succ t ih =>
    have hk : a + t < q := by omega
    have hi := ih (by omega)
    have hpartial : ∑ i ∈ range (t + 1), b i ≤ N :=
      (sum_le_sum_of_subset_of_nonneg (range_mono (by omega : t + 1 ≤ q - a))
        (fun i _ _ => hb i)).trans htotal
    have hA : 0 ≤ ∑ i ∈ range t, b i := sum_nonneg (fun i _ => hb i)
    have hL : 0 ≤ N - b t := by
      rw [sum_range_succ] at hpartial
      linarith only [hpartial, hA]
    have hnext := rootedClique_step_lower G I (k := a + t) (by omega) (hstep t hk)
    have hnext' : (rootedCliques G I (a + t)).card * (N - b t) ≤
        (t + 1 : ℕ) * ((rootedCliques G I (a + (t + 1))).card : ℝ) := by
      rw [show a + t + 1 - a = t + 1 by omega,
        show a + t + 1 = a + (t + 1) by omega] at hnext
      exact hnext
    calc
      _ = (1 - ((∑ i ∈ range t, b i) + b t) / N) * N ^ (t + 1) := by
        rw [sum_range_succ]
      _ ≤ (1 - (∑ i ∈ range t, b i) / N) * N ^ t * (N - b t) :=
        additive_loss_step hN hA (hb t) t
      _ ≤ ((t.factorial : ℝ) * (rootedCliques G I (a + t)).card) * (N - b t) :=
        mul_le_mul_of_nonneg_right hi hL
      _ = (t.factorial : ℝ) * ((rootedCliques G I (a + t)).card * (N - b t)) := by ring
      _ ≤ (t.factorial : ℝ) * ((t + 1 : ℕ) *
          ((rootedCliques G I (a + (t + 1))).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hnext' (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul]; ring

theorem sum_choose_extension (a r t : ℕ) :
    (∑ i ∈ range t, (a + i).choose r) =
      (a + t).choose (r + 1) - a.choose (r + 1) := by
  induction t with
  | zero => simp
  | succ t ih => rw [sum_range_succ, ih, choose_extension_exponent_succ]

end Arxiv2411_18291
