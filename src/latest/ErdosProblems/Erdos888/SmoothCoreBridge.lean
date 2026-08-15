import ErdosProblems.Erdos888.SmoothCore
import ErdosProblems.Erdos888.BlockMajorant

/-!
# The dyadic bridge for the smooth-core term

This module connects the mixed coloured-KST contribution
`2 T M sqrt N` to the one-dimensional Rankin sum `smoothCoreS3`.
-/

open Filter Asymptotics
open scoped BigOperators

namespace Erdos888

noncomputable section

private theorem sqrt_two_pow_bridge (i : ℕ) :
    Real.sqrt ((2 : ℝ) ^ i) = (Real.sqrt 2) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

private theorem sqrtDyadicHead_le (Q : ℕ) (hQ : 0 < Q) :
    (∑ j ∈ Finset.range (Nat.log 2 Q + 1),
      Real.sqrt ((2 : ℝ) ^ (j + 1))) ≤ 8 * Real.sqrt (Q : ℝ) := by
  let r : ℝ := Real.sqrt 2
  have hrpos : 0 < r := Real.sqrt_pos.2 (by norm_num)
  have hrone : 1 < r := by
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp [r]
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hrlower : (4 / 3 : ℝ) ≤ r := by
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp [r]
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  let m := Nat.log 2 Q + 1
  have hgeom : (∑ j ∈ Finset.range m, r ^ j) ≤ 4 * r ^ m := by
    rw [geom_sum_eq (ne_of_gt hrone)]
    apply (div_le_iff₀ (sub_pos.mpr hrone)).2
    have hrpow : 1 ≤ r ^ m := one_le_pow₀ hrone.le
    nlinarith [mul_nonneg (show 0 ≤ r ^ m by positivity)
      (show 0 ≤ 4 * (r - 1) - 1 by nlinarith)]
  have hpowlog : (2 : ℝ) ^ Nat.log 2 Q ≤ (Q : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hQ)
  have hsqrtlog : r ^ Nat.log 2 Q ≤ Real.sqrt (Q : ℝ) := by
    rw [← sqrt_two_pow_bridge]
    exact Real.sqrt_le_sqrt hpowlog
  calc
    (∑ j ∈ Finset.range (Nat.log 2 Q + 1),
        Real.sqrt ((2 : ℝ) ^ (j + 1))) =
        r * ∑ j ∈ Finset.range m, r ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [sqrt_two_pow_bridge, pow_succ]
      dsimp [r]
      ring
    _ ≤ r * (4 * r ^ m) := mul_le_mul_of_nonneg_left hgeom hrpos.le
    _ = 8 * r ^ Nat.log 2 Q := by
      dsimp [m, r]
      have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      ring_nf at ⊢
      rw [hsquare]
      ring
    _ ≤ 8 * Real.sqrt (Q : ℝ) := mul_le_mul_of_nonneg_left hsqrtlog (by norm_num)

private theorem invSqrtDyadicTail_bridge_le (k m : ℕ) :
    (∑ j ∈ Finset.range m,
      1 / Real.sqrt ((2 : ℝ) ^ (k + j))) ≤
      4 / Real.sqrt ((2 : ℝ) ^ k) := by
  let q : ℝ := (Real.sqrt 2)⁻¹
  have hsqrtPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtOne : 1 < Real.sqrt (2 : ℝ) := by
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hq0 : 0 ≤ q := inv_nonneg.mpr hsqrtPos.le
  have hq1 : q < 1 := by
    dsimp [q]
    exact inv_lt_one_of_one_lt₀ hsqrtOne
  have hgeom : (∑ j ∈ Finset.range m, q ^ j) ≤ 4 := by
    have hlt := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hq0 hq1
    have hdenom : (1 - q)⁻¹ ≤ 4 := by
      rw [inv_le_iff_one_le_mul₀' (sub_pos.mpr hq1)]
      dsimp [q]
      have hsqrtLower : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
        have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith [Real.sqrt_nonneg (2 : ℝ)]
      have hinv : (Real.sqrt 2)⁻¹ ≤ 3 / 4 := by
        rw [inv_le_iff_one_le_mul₀' hsqrtPos]
        nlinarith
      linarith
    have hdenom' : q ^ 0 / (1 - q) ≤ 4 := by
      simpa [div_eq_mul_inv] using hdenom
    simpa using hlt.trans hdenom'
  calc
    (∑ j ∈ Finset.range m,
        1 / Real.sqrt ((2 : ℝ) ^ (k + j))) =
        q ^ k * ∑ j ∈ Finset.range m, q ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [sqrt_two_pow_bridge, pow_add]
      dsimp [q]
      rw [inv_pow, inv_pow]
      field_simp
    _ ≤ q ^ k * 4 := mul_le_mul_of_nonneg_left hgeom (pow_nonneg hq0 k)
    _ = 4 / Real.sqrt ((2 : ℝ) ^ k) := by
      rw [sqrt_two_pow_bridge]
      dsimp [q]
      rw [inv_pow]
      field_simp

/-- A purely finite dyadic crossover.  The hypotheses say that `Q` is
within a factor two of the real crossover `B/T`. -/
theorem dyadicMinSqrtCrossover_le {T B : ℝ} {Q i R : ℕ}
    (hT : 0 < T) (hB : 0 ≤ B) (hQ : 0 < Q)
    (hlow : T * Q ≤ B) (hhigh : B ≤ 2 * T * Q) :
    (∑ j ∈ Finset.Ico i R,
      min T (B / (2 : ℝ) ^ j) *
        Real.sqrt ((2 : ℝ) ^ (j + 1))) ≤
      80 * Real.sqrt (B * T) := by
  classical
  let k := Nat.log 2 Q + 1
  let s := Finset.Ico i R
  let slo := s.filter fun j ↦ 2 ^ j ≤ Q
  let shi := s.filter fun j ↦ ¬ 2 ^ j ≤ Q
  have hloSub : slo ⊆ Finset.range k := by
    intro j hj
    have hjQ := (Finset.mem_filter.mp hj).2
    rw [Finset.mem_range]
    exact (Nat.le_log_of_pow_le (by norm_num) hjQ).trans_lt (Nat.lt_succ_self _)
  have hhiSub : shi ⊆ Finset.Ico k R := by
    intro j hj
    have hjs := Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1
    have hQj : Q < 2 ^ j := Nat.lt_of_not_ge (Finset.mem_filter.mp hj).2
    have hj0 : j ≠ 0 := by
      intro hjz
      subst j
      norm_num at hQj
      omega
    have hlogj := Nat.log_lt_of_lt_pow' hj0 hQj
    exact Finset.mem_Ico.mpr ⟨by simpa [k] using hlogj, hjs.2⟩
  have hsqrtBT : 0 ≤ Real.sqrt (B * T) := Real.sqrt_nonneg _
  have hlowRoot : T * Real.sqrt (Q : ℝ) ≤ Real.sqrt (B * T) := by
    have hQreal : (0 : ℝ) ≤ Q := by positivity
    have hBT : 0 ≤ B * T := mul_nonneg hB hT.le
    have hsquareQ := Real.sq_sqrt hQreal
    have hsquareBT := Real.sq_sqrt hBT
    have hlow' : T * (Q : ℝ) ≤ B := by exact_mod_cast hlow
    have hnonneg : 0 ≤ T * Real.sqrt (Q : ℝ) := mul_nonneg hT.le (Real.sqrt_nonneg _)
    apply (sq_le_sq₀ hnonneg hsqrtBT).mp
    rw [mul_pow, hsquareQ, hsquareBT]
    nlinarith
  have hhighRoot : B / Real.sqrt (Q : ℝ) ≤
      2 * Real.sqrt (B * T) := by
    have hsqrtQ : 0 < Real.sqrt (Q : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hQ)
    have hhigh' : B ≤ 2 * T * (Q : ℝ) := by exact_mod_cast hhigh
    rw [div_le_iff₀ hsqrtQ]
    have hsquareQ := Real.sq_sqrt (show (0 : ℝ) ≤ Q by positivity)
    have hsquareBT := Real.sq_sqrt (mul_nonneg hB hT.le)
    have hright : 0 ≤ 2 * Real.sqrt (B * T) * Real.sqrt (Q : ℝ) := by positivity
    by_cases hB0 : B = 0
    · simp [hB0]
    have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    apply (sq_le_sq₀ hB hright).mp
    rw [mul_pow, mul_pow, hsquareBT, hsquareQ]
    nlinarith
  have hlo : (∑ j ∈ slo,
      min T (B / (2 : ℝ) ^ j) * Real.sqrt ((2 : ℝ) ^ (j + 1))) ≤
      8 * Real.sqrt (B * T) := by
    calc
      _ ≤ T * ∑ j ∈ slo, Real.sqrt ((2 : ℝ) ^ (j + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
      _ ≤ T * ∑ j ∈ Finset.range k, Real.sqrt ((2 : ℝ) ^ (j + 1)) := by
        gcongr
      _ ≤ T * (8 * Real.sqrt (Q : ℝ)) := by
        gcongr
        simpa [k] using sqrtDyadicHead_le Q hQ
      _ ≤ 8 * Real.sqrt (B * T) := by nlinarith
  have hhi : (∑ j ∈ shi,
      min T (B / (2 : ℝ) ^ j) * Real.sqrt ((2 : ℝ) ^ (j + 1))) ≤
      72 * Real.sqrt (B * T) := by
    have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
        Real.sqrt_nonneg (2 : ℝ)]
    calc
      _ ≤ ∑ j ∈ shi,
          B / (2 : ℝ) ^ j * Real.sqrt ((2 : ℝ) ^ (j + 1)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
      _ ≤ ∑ j ∈ Finset.Ico k R,
          B / (2 : ℝ) ^ j * Real.sqrt ((2 : ℝ) ^ (j + 1)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hhiSub
          (fun _ _ _ ↦ by positivity)
      _ = B * Real.sqrt 2 * ∑ z ∈ Finset.range (R - k),
          1 / Real.sqrt ((2 : ℝ) ^ (k + z)) := by
        rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        have hpowpos : 0 < (2 : ℝ) ^ (k + z) := by positivity
        rw [pow_succ, Real.sqrt_mul (by positivity)]
        field_simp
        rw [Real.sq_sqrt hpowpos.le]
      _ ≤ B * Real.sqrt 2 *
          (4 / Real.sqrt ((2 : ℝ) ^ k)) := by
        gcongr
        exact invSqrtDyadicTail_bridge_le k (R - k)
      _ ≤ 8 * (B / Real.sqrt (Q : ℝ)) := by
        have hQpow : Q < 2 ^ k := by
          simpa [k] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) Q
        have hsqrtQpow : Real.sqrt (Q : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ k) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast hQpow.le
        have hinv : 1 / Real.sqrt ((2 : ℝ) ^ k) ≤
            1 / Real.sqrt (Q : ℝ) :=
          one_div_le_one_div_of_le (Real.sqrt_pos.2 (by exact_mod_cast hQ)) hsqrtQpow
        calc
          B * Real.sqrt 2 * (4 / Real.sqrt ((2 : ℝ) ^ k)) =
              (4 * B * Real.sqrt 2) *
                (1 / Real.sqrt ((2 : ℝ) ^ k)) := by ring
          _ ≤ (4 * B * Real.sqrt 2) * (1 / Real.sqrt (Q : ℝ)) := by
            gcongr
          _ ≤ (8 * B) * (1 / Real.sqrt (Q : ℝ)) := by
            have hc : 4 * B * Real.sqrt 2 ≤ 8 * B := by
              calc
                4 * B * Real.sqrt 2 ≤ 4 * B * 2 := by
                  exact mul_le_mul_of_nonneg_left hsqrt2 (by positivity)
                _ = 8 * B := by ring
            exact mul_le_mul_of_nonneg_right hc (by positivity)
          _ = 8 * (B / Real.sqrt (Q : ℝ)) := by ring
      _ ≤ 16 * Real.sqrt (B * T) := by nlinarith
      _ ≤ 72 * Real.sqrt (B * T) := by nlinarith [hsqrtBT]
  rw [← Finset.sum_filter_add_sum_filter_not s (fun j ↦ 2 ^ j ≤ Q)]
  change (∑ j ∈ slo,
      min T (B / (2 : ℝ) ^ j) * Real.sqrt ((2 : ℝ) ^ (j + 1))) +
    (∑ j ∈ shi,
      min T (B / (2 : ℝ) ^ j) * Real.sqrt ((2 : ℝ) ^ (j + 1))) ≤
      80 * Real.sqrt (B * T)
  calc
    _ ≤ 8 * Real.sqrt (B * T) + 72 * Real.sqrt (B * T) := add_le_add hlo hhi
    _ = 80 * Real.sqrt (B * T) := by ring

end

end Erdos888
