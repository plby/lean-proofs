import ErdosProblems.Erdos327.Analytic.PowerConvolution
import ErdosProblems.Erdos327.Analytic.SieveScheduleLog

/-!
# Arithmetic of terminal dyadic residuals

Let `X = 2^j`, `Y = Q / X²`, and `n = log₂ Q`.  When `Y ≥ 2`,
the residual logarithmic index `n - 2j` is positive and
`2^(n-2j) ≤ Y`.  In the terminal range `Y < X`, one also has
`n < 3j`.  These exact natural-number statements bridge the scheduled
blocks to the finite power-convolution estimate.
-/

namespace Erdos327.Analytic

open Finset Real

noncomputable section

/-- Binary logarithmic index left after dividing by a dyadic square. -/
def dyadicResidualIndex (Q j : ℕ) : ℕ :=
  Nat.log 2 Q - 2 * j

theorem dyadicScale_sq_eq_pow (j : ℕ) :
    dyadicScale j ^ 2 = 2 ^ (2 * j) := by
  unfold dyadicScale
  rw [← pow_mul]
  congr 1
  omega

/-- A residual quotient of size at least two forces the square scale
strictly below the leading dyadic power. -/
theorem two_mul_index_lt_log_of_two_le_residual
    {Q j : ℕ}
    (hY : 2 ≤ Q / dyadicScale j ^ 2) :
    2 * j < Nat.log 2 Q := by
  have hXpos : 0 < dyadicScale j ^ 2 := by
    exact pow_pos (Nat.pow_pos (by norm_num)) _
  have hpowQ :
      2 * dyadicScale j ^ 2 ≤ Q :=
    (Nat.le_div_iff_mul_le hXpos).mp hY
  have hpow :
      2 ^ (2 * j + 1) ≤ Q := by
    calc
      2 ^ (2 * j + 1) = 2 * 2 ^ (2 * j) := by
        rw [pow_add]
        norm_num
        ring
      _ = 2 * dyadicScale j ^ 2 := by
        rw [dyadicScale_sq_eq_pow]
      _ ≤ Q := hpowQ
  exact lt_of_lt_of_le
    (show 2 * j < 2 * j + 1 by omega)
    (Nat.le_log_of_pow_le (by norm_num) hpow)

theorem dyadicResidualIndex_pos
    {Q j : ℕ}
    (hY : 2 ≤ Q / dyadicScale j ^ 2) :
    0 < dyadicResidualIndex Q j := by
  have ht :=
    two_mul_index_lt_log_of_two_le_residual hY
  unfold dyadicResidualIndex
  omega

/-- The largest dyadic power below `Q`, divided by the dyadic square,
remains below the exact residual quotient. -/
theorem pow_dyadicResidualIndex_le_residual
    {Q j : ℕ}
    (hY : 2 ≤ Q / dyadicScale j ^ 2) :
    2 ^ dyadicResidualIndex Q j ≤
      Q / dyadicScale j ^ 2 := by
  let n := Nat.log 2 Q
  have hjn : 2 * j ≤ n := by
    dsimp [n]
    exact (two_mul_index_lt_log_of_two_le_residual hY).le
  have hQ0 : Q ≠ 0 := by
    have hXpos : 0 < dyadicScale j ^ 2 := by
      exact pow_pos (Nat.pow_pos (by norm_num)) _
    have := (Nat.le_div_iff_mul_le hXpos).mp hY
    omega
  have hpowQ : 2 ^ n ≤ Q := by
    dsimp [n]
    exact Nat.pow_log_le_self 2 hQ0
  have hdenPos : 0 < dyadicScale j ^ 2 := by
    exact pow_pos (Nat.pow_pos (by norm_num)) _
  apply (Nat.le_div_iff_mul_le hdenPos).2
  rw [dyadicResidualIndex, dyadicScale_sq_eq_pow,
    Nat.pow_sub_mul_pow 2 hjn]
  exact hpowQ

/-- Logarithmic form of the dyadic residual lower bound. -/
theorem residualIndex_mul_log_two_le_log_residual
    {Q j : ℕ}
    (hY : 2 ≤ Q / dyadicScale j ^ 2) :
    (dyadicResidualIndex Q j : ℝ) * log 2 ≤
      log (Q / dyadicScale j ^ 2 : ℕ) := by
  have hkpos := dyadicResidualIndex_pos hY
  have hpow :=
    pow_dyadicResidualIndex_le_residual hY
  have hleftPos : (0 : ℝ) < (2 ^ dyadicResidualIndex Q j : ℕ) := by
    positivity
  have hresPos :
      0 < Q / dyadicScale j ^ 2 := by omega
  have hlog :=
    Real.strictMonoOn_log.monotoneOn
      (by
        simpa only [Set.mem_Ioi] using hleftPos)
      (by
        simpa only [Set.mem_Ioi] using
          (show (0 : ℝ) <
              (Q / dyadicScale j ^ 2 : ℕ) by
                exact_mod_cast hresPos))
      (by exact_mod_cast hpow)
  simpa [Real.log_pow] using hlog

/-- In the terminal range `Y < X`, the total binary logarithmic index is
strictly smaller than `3j`. -/
theorem log_lt_three_mul_index_of_residual_lt_scale
    {Q j : ℕ}
    (hYpos : 1 ≤ Q / dyadicScale j ^ 2)
    (hterminal : Q / dyadicScale j ^ 2 < dyadicScale j) :
    Nat.log 2 Q < 3 * j := by
  let X := dyadicScale j
  let Y := Q / X ^ 2
  have hXpos : 0 < X ^ 2 := by
    dsimp [X]
    exact pow_pos (Nat.pow_pos (by norm_num)) _
  have hdiv :
      Q < X ^ 2 * (Y + 1) := by
    dsimp [Y]
    exact Nat.lt_mul_div_succ Q hXpos
  have hsucc : Y + 1 ≤ X := by
    dsimp [Y, X] at hterminal ⊢
    omega
  have hcube : Q < X ^ 3 := by
    calc
      Q < X ^ 2 * (Y + 1) := hdiv
      _ ≤ X ^ 2 * X :=
        Nat.mul_le_mul_left _ hsucc
      _ = X ^ 3 := by ring
  have hpow : Q < 2 ^ (3 * j) := by
    have hpow' : Q < 2 ^ (j * 3) := by
      simpa [X, dyadicScale, ← pow_mul] using hcube
    simpa [mul_comm] using hpow'
  have hQ0 : Q ≠ 0 := by
    intro hQ
    subst Q
    simp at hYpos
  exact Nat.log_lt_of_lt_pow hQ0 hpow

/-- The residual-index map is injective on every set on which `2j` does
not exceed the ambient binary index. -/
theorem dyadicResidualIndex_injOn
    {Q : ℕ} {s : Finset ℕ}
    (hs : ∀ j ∈ s, 2 * j ≤ Nat.log 2 Q) :
    Set.InjOn (dyadicResidualIndex Q) s := by
  intro i hi j hj hij
  unfold dyadicResidualIndex at hij
  have hi' := hs i hi
  have hj' := hs j hj
  omega

/-- Every positive residual index belongs to the natural range ending at
`log₂ Q`. -/
theorem dyadicResidualIndex_mem_range
    {Q j : ℕ} (hj : 2 * j ≤ Nat.log 2 Q) :
    dyadicResidualIndex Q j ∈ range (Nat.log 2 Q + 1) := by
  rw [mem_range]
  unfold dyadicResidualIndex
  omega

/-- An injective family of residual indices is dominated by the complete
power sum up to `log₂ Q`. -/
theorem sum_dyadicResidualIndex_rpow_le
    {Q : ℕ} {s : Finset ℕ} {q : ℝ}
    (hs : ∀ j ∈ s, 2 * j ≤ Nat.log 2 Q)
    (hqLower : -1 < q) (hqUpper : q ≤ 0) :
    (∑ j ∈ s,
      (((dyadicResidualIndex Q j + 1 : ℕ) : ℝ) ^ q)) ≤
      partialRpowConstant q *
        (((Nat.log 2 Q + 1 : ℕ) : ℝ) ^ (q + 1)) := by
  let g : ℕ → ℕ := dyadicResidualIndex Q
  let f : ℕ → ℝ := fun k ↦ (((k + 1 : ℕ) : ℝ) ^ q)
  have hinj : Set.InjOn g s :=
    dyadicResidualIndex_injOn hs
  have hsubset : image g s ⊆ range (Nat.log 2 Q + 1) := by
    intro k hk
    rw [mem_image] at hk
    rcases hk with ⟨j, hj, rfl⟩
    exact dyadicResidualIndex_mem_range (hs j hj)
  have himage :
      (∑ k ∈ image g s, f k) =
        ∑ j ∈ s, f (g j) :=
    sum_image hinj
  calc
    (∑ j ∈ s,
        (((dyadicResidualIndex Q j + 1 : ℕ) : ℝ) ^ q)) =
        ∑ k ∈ image g s, f k := by
      rw [himage]
    _ ≤ ∑ k ∈ range (Nat.log 2 Q + 1), f k := by
      refine sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro k hk hnot
      dsimp [f]
      exact Real.rpow_nonneg (by positivity) _
    _ ≤ partialRpowConstant q *
          (((Nat.log 2 Q + 1 : ℕ) : ℝ) ^ (q + 1)) := by
      simpa [f] using
        (sum_range_add_one_rpow_le
          hqLower hqUpper (Nat.log 2 Q))

end

end Erdos327.Analytic
