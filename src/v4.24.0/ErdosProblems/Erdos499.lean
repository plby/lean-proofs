/-

This is a Lean formalization of a solution to Erdős Problem 499.
https://www.erdosproblems.com/499

The original human proof was found by: Marcus, M.; Minc, H.

Marcus, Marvin and Minc, Henryk, Some results on doubly stochastic matrices. Proc. Amer. Math. Soc. (1962), 571-579.
Marcus, Marvin and Minc, Henryk, Inequalities for the permanent function. Ann. Math. 75 (1962), 47-62.


The formal proof was written by Aristotle from Harmonic.

The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind.

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos499


/--
Let $M$ be a real $n \times n$ doubly stochastic matrix. Does there exist some $σ \in S_n$ such that
$$
\prod_{1 \leq i \leq n} M_{i, σ(i)} \geq n^{-n}?
$$
This is true, and was proved by Marcus and Minc [MaMi62]

[MaMi62] Marcus, Marvin and Minc, Henryk, Some results on doubly stochastic matrices. Proc. Amer. Math. Soc. (1962), 571-579.
-/

/-
The entropy-like function $F(M) = \sum M_{ij} \log M_{ij}$ is minimized at the matrix $J_n$ (all entries $1/n$) over the set of doubly stochastic matrices.
-/
lemma entropy_inequality (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    ∑ i, ∑ j, M i j * Real.log (M i j) ≥ n * Real.log (1 / n) := by
      by_cases hn : n = 0 <;> aesop;
      -- Apply Jensen's inequality to each row of the matrix $M$.
      have h_jensen : ∀ i, ∑ j, M i j * Real.log (M i j) ≥ n * (1 / n) * Real.log (1 / n) := by
        bound;
        -- Apply Jensen's inequality to the convex function $f(x) = x \log x$ with the weights $M_{ij}$.
        have h_jensen : (∑ j, (1 / n : ℝ) * (M i j * Real.log (M i j))) ≥ ((∑ j, (1 / n : ℝ) * M i j) * Real.log (∑ j, (1 / n : ℝ) * M i j)) := by
          have h_jensen : ConvexOn ℝ (Set.Ici 0) (fun x => x * Real.log x) := by
            exact ( Real.convexOn_mul_log );
          apply ConvexOn.map_sum_le h_jensen;
          · bound;
          · norm_num [ hn ];
          · exact fun j _ => hM.1 i j;
        -- Since $M$ is doubly stochastic, we have $\sum_{j} M_{ij} = 1$.
        have h_sum : ∑ j, M i j = 1 := by
          cases hM ; aesop;
          simpa [ Matrix.mulVec, dotProduct ] using congr_fun left_1 i;
        simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
        nlinarith [ inv_mul_cancel_left₀ ( by positivity : ( n : ℝ ) ≠ 0 ) ( Real.log n ), inv_mul_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ) ];
      simpa [ hn, mul_assoc, mul_left_comm ] using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_jensen i

set_option maxHeartbeats 0 in
theorem erdos_499 :
    (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      n ^ (- n : ℤ) ≤ ∏ i, M i (σ i)) := by
  -- By the Birkhoff-von Neumann theorem, any doubly stochastic matrix $M$ can be written as a convex combination of permutation matrices.
  have h_birkhoff : ∀ n : ℕ, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ (w : Equiv.Perm (Fin n) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hw_sum : ∑ σ, w σ = 1), M = ∑ σ, w σ • (fun i j => if σ i = j then 1 else 0 : Matrix (Fin n) (Fin n) ℝ) := by
    intro n M hM;
    have := @doublyStochastic_eq_convexHull_permMatrix;
    replace := this.subset hM;
    rw [ mem_convexHull_iff ] at this;
    specialize this ( { x : Matrix ( Fin n ) ( Fin n ) ℝ | ∃ w : Equiv.Perm ( Fin n ) → ℝ, ( ∀ σ, 0 ≤ w σ ) ∧ ( ∑ σ, w σ = 1 ) ∧ x = ∑ σ, w σ • ( fun i j => if σ i = j then 1 else 0 : Matrix ( Fin n ) ( Fin n ) ℝ ) } ) ?_ ?_;
    · norm_num +zetaDelta at *;
      intro σ; use fun τ => if τ = σ then 1 else 0; aesop;
    · intro x hx y hy a b ha hb hab;
      obtain ⟨ w₁, hw₁₁, hw₁₂, rfl ⟩ := hx; obtain ⟨ w₂, hw₂₁, hw₂₂, rfl ⟩ := hy; use fun σ => a * w₁ σ + b * w₂ σ; simp +decide [ *, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, smul_add, add_smul, mul_add, add_mul, mul_assoc, mul_left_comm, Finset.sum_smul, Finset.smul_sum ] ;
      exact ⟨ fun σ => add_nonneg ( mul_nonneg ha ( hw₁₁ σ ) ) ( mul_nonneg hb ( hw₂₁ σ ) ), by rw [ ← Finset.mul_sum _ _ _, ← Finset.mul_sum _ _ _, hw₁₂, hw₂₂, mul_one, mul_one, hab ], by simp +decide [ mul_assoc, MulAction.mul_smul ] ⟩;
    · exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1, this.choose_spec.2.2 ⟩;
  -- By the entropy inequality, we have $L(M) \ge n \log(1/n)$.
  have h_entropy : ∀ n : ℕ, ∀ M ∈ doublyStochastic ℝ (Fin n), ∑ i, ∑ j, M i j * Real.log (M i j) ≥ n * Real.log (1 / n) := by
    exact?;
  intro n M hM
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ := h_birkhoff n M hM
  have h_log_bound : ∑ σ, w σ * ∑ i, Real.log (M i (σ i)) ≥ n * Real.log (1 / n) := by
    have h_log_bound : ∑ i, ∑ j, M i j * Real.log (M i j) = ∑ σ, w σ * ∑ i, Real.log (M i (σ i)) := by
      have h_log_bound : ∀ i j, M i j * Real.log (M i j) = ∑ σ, w σ * (if σ i = j then Real.log (M i j) else 0) := by
        intro i j
        rw [hw_eq]
        simp [Matrix.sum_apply];
        simp +decide [ Finset.sum_ite, Finset.filter_congr, Finset.sum_mul _ _ _ ];
      simp +decide only [h_log_bound, Finset.mul_sum _ _ _];
      rw [ Finset.sum_comm ];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; rw [ Finset.sum_comm ] ;
      intro i hi; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
    exact h_log_bound ▸ h_entropy n M hM;
  -- Since $w$ is a probability distribution, there exists some $\sigma$ such that $w_\sigma > 0$ and $\sum_{i} \log M_{i, \sigma(i)} \ge n \log(1/n)$.
  obtain ⟨σ, hσ_pos, hσ_log⟩ : ∃ σ : Equiv.Perm (Fin n), w σ > 0 ∧ ∑ i, Real.log (M i (σ i)) ≥ n * Real.log (1 / n) := by
    contrapose! h_log_bound;
    have h_log_bound : ∑ σ, w σ * ∑ i, Real.log (M i (σ i)) < ∑ σ, w σ * (n * Real.log (1 / n)) := by
      apply Finset.sum_lt_sum;
      · exact fun σ _ => if hσ : w σ = 0 then by simp +decide [ hσ ] else mul_le_mul_of_nonneg_left ( le_of_lt ( h_log_bound σ ( lt_of_le_of_ne ( hw_nonneg σ ) ( Ne.symm hσ ) ) ) ) ( hw_nonneg σ );
      · norm_num +zetaDelta at *;
        exact Exists.elim ( show ∃ σ, w σ > 0 from not_forall_not.mp fun h => by norm_num [ show w = fun _ => 0 from funext fun σ => le_antisymm ( le_of_not_gt fun hσ => h σ hσ ) ( hw_nonneg σ ) ] at hw_sum ) fun σ hσ => ⟨ σ, by nlinarith [ h_log_bound σ hσ ] ⟩;
    simpa [ ← Finset.sum_mul _ _ _, hw_sum ] using h_log_bound;
  use σ;
  rw [ ← Real.log_le_log_iff ] <;> norm_cast <;> norm_num;
  · rw [ Real.log_prod _ _ fun i _ => _ ];
    · simpa using hσ_log;
    · intro i _; contrapose! hσ_pos; simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] ;
      rw [ Finset.sum_eq_zero_iff_of_nonneg ] at hσ_pos <;> aesop;
  · cases n <;> norm_num at * ; positivity;
  · refine' Finset.prod_pos fun i _ => _;
    rw [ hw_eq ];
    simp +decide [ Finset.sum_apply, Matrix.sum_apply ];
    exact lt_of_lt_of_le ( by simpa [ hσ_pos ] ) ( Finset.single_le_sum ( fun x _ => by split_ifs <;> linarith [ hw_nonneg x ] ) ( Finset.mem_univ σ ) )
