/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 499.
https://www.erdosproblems.com/forum/thread/499

Informal authors:
- Marvin Marcus
- Henryk Minc

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos499.md
-/
import Mathlib

namespace Erdos499

/--
Let $M$ be a real $n \times n$ doubly stochastic matrix. Does there exist some $σ \in S_n$ such that
$$
\prod_{1 \leq i \leq n} M_{i, σ(i)} \geq n^{-n}?
$$
This is true, and was proved by Marcus and Minc [MaMi62]

[MaMi62] Marcus, Marvin and Minc, Henryk, Some results on doubly stochastic
matrices. Proc. Amer. Math. Soc. (1962), 571-579.
-/
/-
The entropy-like function $F(M) = \sum M_{ij} \log M_{ij}$ is minimized at the
matrix $J_n$ (all entries $1/n$) over the set of doubly stochastic matrices.
-/
lemma entropy_inequality
    (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M ∈ doublyStochastic ℝ (Fin n)) :
    ∑ i, ∑ j, M i j * Real.log (M i j) ≥ n * Real.log (1 / n) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hrow :
      ∀ i : Fin n, (n : ℝ) * ((1 / n : ℝ) * Real.log (1 / n)) ≤
        ∑ j : Fin n, M i j * Real.log (M i j) := by
    intro i
    have hsum : ∑ j : Fin n, M i j = 1 :=
      sum_row_of_mem_doublyStochastic hM i
    have havg : (∑ j : Fin n, (1 / n : ℝ) • M i j) = (1 / n : ℝ) := by
      simp [smul_eq_mul, ← Finset.mul_sum, hsum]
    have hjensen :
        (fun x : ℝ => x * Real.log x) (∑ j : Fin n, (1 / n : ℝ) • M i j) ≤
          ∑ j : Fin n, (1 / n : ℝ) • ((fun x : ℝ => x * Real.log x) (M i j)) := by
      refine Real.convexOn_mul_log.map_sum_le ?_ ?_ ?_
      · intro j hj
        positivity
      · simp [hnpos.ne']
      · intro j hj
        exact hM.1 i j
    have hmul := mul_le_mul_of_nonneg_left (by simpa [havg] using hjensen) hnpos.le
    have havg' : (∑ x : Fin n, (n : ℝ)⁻¹ * M i x) = (n : ℝ)⁻¹ := by
      simpa [one_div, smul_eq_mul] using havg
    calc
      (n : ℝ) * ((1 / n : ℝ) * Real.log (1 / n))
          ≤ (n : ℝ) * ∑ j : Fin n, (1 / n : ℝ) * (M i j * Real.log (M i j)) := by
            simpa [havg', one_div, Real.log_inv] using hmul
      _ = ∑ j : Fin n, M i j * Real.log (M i j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        field_simp [hnpos.ne']
  have hsum_rows :
      ∑ i : Fin n, (n : ℝ) * ((1 / n : ℝ) * Real.log (1 / n)) ≤
        ∑ i : Fin n, ∑ j : Fin n, M i j * Real.log (M i j) :=
    Finset.sum_le_sum fun i hi => hrow i
  have hconst :
      (∑ i : Fin n, (n : ℝ) * ((1 / n : ℝ) * Real.log (1 / n))) =
        (n : ℝ) * Real.log (1 / n) := by
    rw [Finset.sum_const, Finset.card_fin]
    field_simp [hnpos.ne']
    ring
  exact hconst ▸ hsum_rows

set_option maxHeartbeats 8000000 in
-- The main entropy argument needs a larger concrete heartbeat budget.
theorem erdos_499 :
    (∀ n, ∀ M ∈ doublyStochastic ℝ (Fin n), ∃ σ : Equiv.Perm (Fin n),
      n ^ (- n : ℤ) ≤ ∏ i, M i (σ i)) := by
  classical
  intro n M hM
  by_cases hn : n = 0
  · subst n
    use 1
    simp
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq_sum⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic (R := ℝ) (n := Fin n) hM
  have hw_eq : M = ∑ σ : Equiv.Perm (Fin n), w σ • σ.permMatrix ℝ := hw_eq_sum.symm
  have hlog_identity :
      (∑ i : Fin n, ∑ j : Fin n, M i j * Real.log (M i j)) =
        ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i : Fin n, Real.log (M i (σ i)) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, M i j * Real.log (M i j))
          = ∑ i : Fin n, ∑ j : Fin n, ∑ σ : Equiv.Perm (Fin n),
              w σ * (σ.permMatrix ℝ i j * Real.log (M i j)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hw_eq]
            simp [Matrix.sum_apply, Finset.sum_mul]
      _ = ∑ σ : Equiv.Perm (Fin n), w σ *
              ∑ i : Fin n, ∑ j : Fin n, σ.permMatrix ℝ i j * Real.log (M i j) := by
            calc
              (∑ i : Fin n, ∑ j : Fin n, ∑ σ : Equiv.Perm (Fin n),
                  w σ * (σ.permMatrix ℝ i j * Real.log (M i j)))
                  = ∑ i : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ j : Fin n,
                      w σ * (σ.permMatrix ℝ i j * Real.log (M i j)) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    rw [Finset.sum_comm]
              _ = ∑ σ : Equiv.Perm (Fin n), ∑ i : Fin n, ∑ j : Fin n,
                    w σ * (σ.permMatrix ℝ i j * Real.log (M i j)) := by
                    rw [Finset.sum_comm]
              _ = ∑ σ : Equiv.Perm (Fin n), w σ *
                    ∑ i : Fin n, ∑ j : Fin n, σ.permMatrix ℝ i j * Real.log (M i j) := by
                    refine Finset.sum_congr rfl ?_
                    intro σ hσ
                    symm
                    simp [Finset.mul_sum, mul_comm]
      _ = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i : Fin n, Real.log (M i (σ i)) := by
            refine Finset.sum_congr rfl ?_
            intro σ hσ
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [Equiv.Perm.permMatrix]
  have hlog_bound :
      ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i : Fin n, Real.log (M i (σ i)) ≥
        (n : ℝ) * Real.log (1 / n) := by
    simpa [hlog_identity] using entropy_inequality n M hM
  have hw_pos_exists : ∃ σ : Equiv.Perm (Fin n), 0 < w σ := by
    by_contra h
    push Not at h
    have hw_zero : ∀ σ : Equiv.Perm (Fin n), w σ = 0 := fun σ =>
      le_antisymm (h σ) (hw_nonneg σ)
    have : (∑ σ : Equiv.Perm (Fin n), w σ) = 0 := by simp [hw_zero]
    linarith
  obtain ⟨σ, hσ_pos, hσ_log⟩ :
      ∃ σ : Equiv.Perm (Fin n), 0 < w σ ∧
        (n : ℝ) * Real.log (1 / n) ≤ ∑ i : Fin n, Real.log (M i (σ i)) := by
    by_contra h
    push Not at h
    have hle : ∀ σ : Equiv.Perm (Fin n),
        w σ * ∑ i : Fin n, Real.log (M i (σ i)) ≤
          w σ * ((n : ℝ) * Real.log (1 / n)) := by
      intro σ
      by_cases hzero : w σ = 0
      · simp [hzero]
      · have hpos : 0 < w σ := lt_of_le_of_ne (hw_nonneg σ) (Ne.symm hzero)
        exact mul_le_mul_of_nonneg_left (le_of_lt (h σ hpos)) (hw_nonneg σ)
    have hlt_exists : ∃ σ : Equiv.Perm (Fin n),
        w σ * ∑ i : Fin n, Real.log (M i (σ i)) <
          w σ * ((n : ℝ) * Real.log (1 / n)) := by
      obtain ⟨σ, hσ⟩ := hw_pos_exists
      exact ⟨σ, mul_lt_mul_of_pos_left (h σ hσ) hσ⟩
    have hlt :
        ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i : Fin n, Real.log (M i (σ i)) <
          ∑ σ : Equiv.Perm (Fin n), w σ * ((n : ℝ) * Real.log (1 / n)) :=
      Finset.sum_lt_sum (fun σ hσ => hle σ) (by
        obtain ⟨σ, hlt⟩ := hlt_exists
        exact ⟨σ, Finset.mem_univ σ, hlt⟩)
    have hright :
        (∑ σ : Equiv.Perm (Fin n), w σ * ((n : ℝ) * Real.log (1 / n))) =
          (n : ℝ) * Real.log (1 / n) := by
      rw [← Finset.sum_mul, hw_sum, one_mul]
    linarith
  use σ
  have hentry_pos : ∀ i : Fin n, 0 < M i (σ i) := by
    intro i
    have hsingle :
        w σ * σ.permMatrix ℝ i (σ i) ≤
          ∑ τ : Equiv.Perm (Fin n), w τ * τ.permMatrix ℝ i (σ i) :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun τ : Equiv.Perm (Fin n) => w τ * τ.permMatrix ℝ i (σ i))
        (fun τ hτ => mul_nonneg (hw_nonneg τ) (by
          rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
          split_ifs <;> norm_num))
        (Finset.mem_univ σ)
    have hterm : w σ * σ.permMatrix ℝ i (σ i) = w σ := by
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Option.mem_def]
    have hMentry :
        M i (σ i) = ∑ τ : Equiv.Perm (Fin n), w τ * τ.permMatrix ℝ i (σ i) := by
      rw [hw_eq]
      simp [Matrix.sum_apply]
    rw [hMentry]
    exact lt_of_lt_of_le (by simpa [hterm] using hσ_pos) hsingle
  have hprod_pos : 0 < ∏ i : Fin n, M i (σ i) :=
    Finset.prod_pos fun i hi => hentry_pos i
  have hleft_pos : 0 < (n : ℝ) ^ (-n : ℤ) := zpow_pos hnpos _
  rw [← Real.log_le_log_iff hleft_pos hprod_pos]
  have hlog_left :
      Real.log ((n : ℝ) ^ (-n : ℤ)) = (n : ℝ) * Real.log (1 / n) := by
    rw [Real.log_zpow, Real.log_div one_ne_zero hnpos.ne', Real.log_one]
    norm_num
  have hlog_prod :
      Real.log (∏ i : Fin n, M i (σ i)) =
        ∑ i : Fin n, Real.log (M i (σ i)) := by
    exact Real.log_prod fun i hi => (hentry_pos i).ne'
  rw [hlog_left, hlog_prod]
  exact hσ_log

#print axioms erdos_499
-- 'Erdos499.erdos_499' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos499
