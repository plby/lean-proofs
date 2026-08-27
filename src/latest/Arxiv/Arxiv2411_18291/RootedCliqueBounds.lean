import Arxiv.Arxiv2411_18291.RootedCliqueCount

/-!
# Iterating upper and lower rooted clique counts

The one-vertex recurrences give an exact factorial normalization and the
density exponent counting all edges outside the root. No fixed fraction
of the main term is discarded in these estimates.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem choose_extension_exponent_succ (a r t : ℕ) :
    (a + (t + 1)).choose (r + 1) - a.choose (r + 1) =
      ((a + t).choose (r + 1) - a.choose (r + 1)) + (a + t).choose r := by
  have hchoose := Nat.choose_le_choose (r + 1) (Nat.le_add_right a t)
  rw [show a + (t + 1) = (a + t) + 1 by omega, Nat.choose_succ_succ]
  simp only [Nat.succ_eq_add_one]
  omega

variable {V : Type*} [Fintype V] [DecidableEq V] {r a : ℕ}

theorem rootedCliques_factorial_lower (G : Hypergraph V (r + 1)) (I : Block V a)
    (q : ℕ) {L d : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hstep : ∀ k, a ≤ k → k < q → ∀ U ∈ rootedCliques G I k,
      L * d ^ k.choose r ≤ ((cliqueNextVertices G U).card : ℝ))
    (t : ℕ) (ht : a + t ≤ q) :
    L ^ t * d ^ ((a + t).choose (r + 1) - a.choose (r + 1)) ≤
      (t.factorial : ℝ) * (rootedCliques G I (a + t)).card := by
  induction t with
  | zero => simp [rootedCliques_base]
  | succ t ih =>
    have hk : a + t < q := by omega
    have hi := ih (by omega)
    have hnext := rootedClique_step_lower G I (k := a + t) (by omega)
      (hstep (a + t) (by omega) hk)
    have hnext' : (rootedCliques G I (a + t)).card * (L * d ^ (a + t).choose r) ≤
        (t + 1 : ℕ) * ((rootedCliques G I (a + (t + 1))).card : ℝ) := by
      rw [show a + t + 1 - a = t + 1 by omega,
        show a + t + 1 = a + (t + 1) by omega] at hnext
      exact hnext
    have hfactor : 0 ≤ L * d ^ (a + t).choose r := mul_nonneg hL (pow_nonneg hd _)
    calc
      _ = (L ^ t * d ^ ((a + t).choose (r + 1) - a.choose (r + 1))) *
          (L * d ^ (a + t).choose r) := by
        rw [choose_extension_exponent_succ, pow_add, pow_succ]
        ring
      _ ≤ ((t.factorial : ℝ) * (rootedCliques G I (a + t)).card) *
          (L * d ^ (a + t).choose r) := mul_le_mul_of_nonneg_right hi hfactor
      _ = (t.factorial : ℝ) * ((rootedCliques G I (a + t)).card *
          (L * d ^ (a + t).choose r)) := by ring
      _ ≤ (t.factorial : ℝ) * ((t + 1 : ℕ) *
          ((rootedCliques G I (a + (t + 1))).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hnext' (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.factorial_succ, Nat.cast_mul]; ring

theorem rootedCliques_factorial_upper (G : Hypergraph V (r + 1)) (I : Block V a)
    (q : ℕ) {L d : ℝ} (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hstep : ∀ k, a ≤ k → k < q → ∀ U ∈ rootedCliques G I k,
      ((cliqueNextVertices G U).card : ℝ) ≤ L * d ^ k.choose r)
    (t : ℕ) (ht : a + t ≤ q) :
    (t.factorial : ℝ) * (rootedCliques G I (a + t)).card ≤
      L ^ t * d ^ ((a + t).choose (r + 1) - a.choose (r + 1)) := by
  induction t with
  | zero => simp [rootedCliques_base]
  | succ t ih =>
    have hk : a + t < q := by omega
    have hi := ih (by omega)
    have hnext := rootedClique_step_upper G I (k := a + t) (by omega)
      (hstep (a + t) (by omega) hk)
    have hnext' : (t + 1 : ℕ) * ((rootedCliques G I (a + (t + 1))).card : ℝ) ≤
        (rootedCliques G I (a + t)).card * (L * d ^ (a + t).choose r) := by
      rw [show a + t + 1 - a = t + 1 by omega,
        show a + t + 1 = a + (t + 1) by omega] at hnext
      exact hnext
    have hfactor : 0 ≤ L * d ^ (a + t).choose r := mul_nonneg hL (pow_nonneg hd _)
    calc
      _ = (t.factorial : ℝ) * ((t + 1 : ℕ) *
          ((rootedCliques G I (a + (t + 1))).card : ℝ)) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        ring
      _ ≤ (t.factorial : ℝ) * ((rootedCliques G I (a + t)).card *
          (L * d ^ (a + t).choose r)) :=
        mul_le_mul_of_nonneg_left hnext' (Nat.cast_nonneg _)
      _ = ((t.factorial : ℝ) * (rootedCliques G I (a + t)).card) *
          (L * d ^ (a + t).choose r) := by ring
      _ ≤ (L ^ t * d ^ ((a + t).choose (r + 1) - a.choose (r + 1))) *
          (L * d ^ (a + t).choose r) := mul_le_mul_of_nonneg_right hi hfactor
      _ = _ := by
        rw [choose_extension_exponent_succ, pow_add, pow_succ]
        ring

end Arxiv2411_18291
