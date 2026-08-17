import ErdosProblems.Erdos896.Basic
import ErdosProblems.Erdos896.Scale

/-!
# Elementary upper-bound and asymptotic bridges for Erdős Problem 896

This file contains no analytic number-theory input.  Its Ford estimates are
always explicit hypotheses.  The results below convert the finite inequality
`maxF N ≤ multiplicationTable N` into real-valued `O` estimates and assemble
the upper estimate with a separately proved lower estimate into `Θ`.
-/

namespace Erdos896

open Filter Asymptotics

/-! ## Normalizing Ford's `x`-scale at `x = N²` -/

/-- Ford's multiplication-table scale when its theorem is stated with a
single ambient parameter `x`.  Substitution `x = N²` gives the scale used in
Problem 896, up to the harmless change from `D(N²)` to `D(N)`. -/
noncomputable def fordScale896 (x : ℕ) : ℝ :=
  (x : ℝ) / logDenom896 x

/-- Squaring tends to infinity on the natural numbers. -/
theorem tendsto_nat_square_atTop :
    Tendsto (fun N : ℕ ↦ N ^ 2) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro M
  refine ⟨max M 1, fun N hN ↦ ?_⟩
  have hMN : M ≤ N := (le_max_left M 1).trans hN
  have hN1 : 1 ≤ N := (le_max_right M 1).trans hN
  calc
    M ≤ N := hMN
    _ = N * 1 := by simp
    _ ≤ N * N := Nat.mul_le_mul_left N hN1
    _ = N ^ 2 := by simp [pow_two]

/-- Pointwise upper comparison in the normalization `x = N²`. -/
theorem fordScale896_sq_le_scale896 (N : ℕ) (hN : 3 ≤ N) :
    fordScale896 (N ^ 2) ≤ scale896 N := by
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hsq3 : 3 ≤ N ^ 2 := hN.trans hNN
  have hdenN : 0 < logDenom896 N := logDenom896_pos hN
  have hdenSq : 0 < logDenom896 (N ^ 2) := logDenom896_pos hsq3
  unfold fordScale896 scale896
  rw [Nat.cast_pow]
  exact div_le_div_of_nonneg_left (by positivity) hdenN
    (logDenom896_le_sq N hN)

/-- Reverse pointwise comparison, with the explicit constant supplied by the
elementary denominator estimate in `Scale.lean`. -/
theorem scale896_le_eight_mul_fordScale896_sq (N : ℕ) (hN : 9 ≤ N) :
    scale896 N ≤ 8 * fordScale896 (N ^ 2) := by
  have hN3 : 3 ≤ N := by omega
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hsq3 : 3 ≤ N ^ 2 := hN3.trans hNN
  have hdenN : 0 < logDenom896 N := logDenom896_pos hN3
  have hdenSq : 0 < logDenom896 (N ^ 2) := logDenom896_pos hsq3
  have hratio : logDenom896 (N ^ 2) / logDenom896 N ≤ 8 := by
    apply (div_le_iff₀ hdenN).2
    simpa [mul_comm] using logDenom896_sq_le N hN
  have hquot_nonneg :
      0 ≤ (N : ℝ) ^ (2 : ℕ) / logDenom896 (N ^ 2) :=
    div_nonneg (by positivity) hdenSq.le
  unfold fordScale896 scale896
  rw [Nat.cast_pow]
  calc
    (N : ℝ) ^ (2 : ℕ) / logDenom896 N =
        (logDenom896 (N ^ 2) / logDenom896 N) *
          ((N : ℝ) ^ (2 : ℕ) / logDenom896 (N ^ 2)) := by
      field_simp
    _ ≤ 8 * ((N : ℝ) ^ (2 : ℕ) / logDenom896 (N ^ 2)) :=
      mul_le_mul_of_nonneg_right hratio hquot_nonneg

/-- Ford's one-parameter scale, pulled back along `N ↦ N²`, is comparable
to the scale in the statement of Problem 896. -/
theorem fordScale896_sq_isTheta_scale896 :
    (fun N : ℕ ↦ fordScale896 (N ^ 2)) =Θ[atTop] scale896 := by
  constructor
  · apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hNN : N ≤ N ^ 2 := by nlinarith
    have hFordNonneg : 0 ≤ fordScale896 (N ^ 2) := by
      unfold fordScale896
      exact div_nonneg (Nat.cast_nonneg _) (logDenom896_pos (hN.trans hNN)).le
    rw [Real.norm_of_nonneg hFordNonneg,
      Real.norm_of_nonneg (scale896_pos hN).le]
    exact fordScale896_sq_le_scale896 N hN
  · apply IsBigO.of_bound 8
    filter_upwards [eventually_ge_atTop 9] with N hN
    have hN3 : 3 ≤ N := by omega
    have hNN : N ≤ N ^ 2 := by nlinarith
    have hFordNonneg : 0 ≤ fordScale896 (N ^ 2) := by
      unfold fordScale896
      exact div_nonneg (Nat.cast_nonneg _)
        (logDenom896_pos (hN3.trans hNN)).le
    rw [Real.norm_of_nonneg (scale896_pos hN3).le,
      Real.norm_of_nonneg hFordNonneg]
    exact scale896_le_eight_mul_fordScale896_sq N hN

/-- The finite upper bound after coercing both cardinalities to `ℝ`. -/
lemma maxF_cast_le_multiplicationTable_card_cast (N : ℕ) :
    (maxF N : ℝ) ≤ ((multiplicationTable N).card : ℝ) := by
  exact_mod_cast maxF_le_multiplicationTable_card N

/-- The cast of `maxF` is `O` of the cast of the full table cardinality,
with implied constant one. -/
theorem maxF_isBigO_multiplicationTable :
    (fun N : ℕ ↦ (maxF N : ℝ)) =O[atTop]
      (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) := by
  apply Filter.Eventually.isBigO
  filter_upwards with N
  have hmax : 0 ≤ (maxF N : ℝ) := Nat.cast_nonneg _
  have htable : 0 ≤ ((multiplicationTable N).card : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hmax, abs_of_nonneg htable] using
    maxF_cast_le_multiplicationTable_card_cast N

/-- A Ford-style multiplication-table upper estimate transfers immediately
to the extremal unique-product count.  The deep estimate is an explicit
parameter of this theorem. -/
theorem maxF_isBigO_scale896_of_multiplicationTable_isBigO
    (hFord :
      (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =O[atTop] scale896) :
    (fun N : ℕ ↦ (maxF N : ℝ)) =O[atTop] scale896 :=
  maxF_isBigO_multiplicationTable.trans hFord

/-- The upper half of a Ford `Θ` estimate suffices for the upper estimate on
`maxF`. -/
theorem maxF_isBigO_scale896_of_multiplicationTable_isTheta
    (hFord :
      (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =Θ[atTop] scale896) :
    (fun N : ℕ ↦ (maxF N : ℝ)) =O[atTop] scale896 :=
  maxF_isBigO_scale896_of_multiplicationTable_isBigO hFord.1

/-! ## Pulling a Ford theorem back along `x = N²` -/

/-- A Ford estimate stated for an abstract table-counting function of `x`
transfers to the concrete `N` by `N` multiplication table once its values at
squares are identified.  Both the analytic estimate and the finite
identification are explicit parameters. -/
theorem multiplicationTable_isBigO_scale896_of_ford_at_squares
    (fordTable : ℕ → ℕ)
    (hFord : (fun x : ℕ ↦ (fordTable x : ℝ)) =O[atTop] fordScale896)
    (hSquares : ∀ N : ℕ,
      fordTable (N ^ 2) = (multiplicationTable N).card) :
    (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =O[atTop] scale896 := by
  have hPullback := hFord.comp_tendsto tendsto_nat_square_atTop
  have hTable :
      (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =O[atTop]
        (fun N : ℕ ↦ fordScale896 (N ^ 2)) := by
    apply hPullback.congr'
    · filter_upwards with N
      change (fordTable (N ^ 2) : ℝ) = ((multiplicationTable N).card : ℝ)
      exact_mod_cast hSquares N
    · rfl
  exact hTable.trans_isTheta fordScale896_sq_isTheta_scale896

/-- The complete elementary upper bridge from a Ford estimate at `x` to the
unique-product maximum at side length `N`. -/
theorem maxF_isBigO_scale896_of_ford_at_squares
    (fordTable : ℕ → ℕ)
    (hFord : (fun x : ℕ ↦ (fordTable x : ℝ)) =O[atTop] fordScale896)
    (hSquares : ∀ N : ℕ,
      fordTable (N ^ 2) = (multiplicationTable N).card) :
    (fun N : ℕ ↦ (maxF N : ℝ)) =O[atTop] scale896 :=
  maxF_isBigO_multiplicationTable.trans
    (multiplicationTable_isBigO_scale896_of_ford_at_squares
      fordTable hFord hSquares)

/-- Variant accepting Ford's estimate in its customary `Θ` form. -/
theorem maxF_isBigO_scale896_of_ford_theta_at_squares
    (fordTable : ℕ → ℕ)
    (hFord : (fun x : ℕ ↦ (fordTable x : ℝ)) =Θ[atTop] fordScale896)
    (hSquares : ∀ N : ℕ,
      fordTable (N ^ 2) = (multiplicationTable N).card) :
    (fun N : ℕ ↦ (maxF N : ℝ)) =O[atTop] scale896 :=
  maxF_isBigO_scale896_of_ford_at_squares fordTable hFord.1 hSquares

/-- Assemble the table upper estimate and an independently established lower
estimate.  The orientation of `IsTheta` is `maxF = O(scale)` together with
`scale = O(maxF)`. -/
theorem maxF_isTheta_scale896_of_upper_and_lower
    (hUpper :
      (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =O[atTop] scale896)
    (hLower : scale896 =O[atTop] (fun N : ℕ ↦ (maxF N : ℝ))) :
    (fun N : ℕ ↦ (maxF N : ℝ)) =Θ[atTop] scale896 :=
  ⟨maxF_isBigO_scale896_of_multiplicationTable_isBigO hUpper, hLower⟩

/-- The same assembly theorem when Ford's table result is supplied in its
usual `Θ` form. -/
theorem maxF_isTheta_scale896_of_table_isTheta_and_lower
    (hFord :
      (fun N : ℕ ↦ ((multiplicationTable N).card : ℝ)) =Θ[atTop] scale896)
    (hLower : scale896 =O[atTop] (fun N : ℕ ↦ (maxF N : ℝ))) :
    (fun N : ℕ ↦ (maxF N : ℝ)) =Θ[atTop] scale896 :=
  maxF_isTheta_scale896_of_upper_and_lower hFord.1 hLower

end Erdos896
