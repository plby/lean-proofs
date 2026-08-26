import ErdosProblems.Erdos69.CutoffBounds

/-! # A common upper bound for all sampled integers and retained shifts -/

namespace Erdos69.Elementary

def constructionUpperBound (m : ℕ) : ℕ :=
  (constructionModulus m + 1) * (6 * m + retainedLength m + progressionLength m + 3) *
    (constructionMaxDilation m + 1)

theorem constructionResidue_le_modulus (m : ℕ) : constructionResidue m ≤ constructionModulus m :=
  (constructionResidue_lt_product m).le.trans
    (Nat.le_of_dvd (constructionModulus_pos m) (dvd_augmentedModulus _ _))

theorem constructionPoint_add_le_upper (m t r : ℕ) (ht : t ≤ progressionLength m)
    (hr : r ≤ constructionMaxDilation m * (6 * m + retainedLength m)) :
    constructionPoint m t + r ≤ constructionUpperBound m := by
  let Q := constructionModulus m
  let A := constructionMaxDilation m
  let K := 6 * m
  let H := retainedLength m
  let T := progressionLength m
  have hA : 1 ≤ A := constructionMaxDilation_pos m
  have hb : constructionBase m ≤ Q * (K * A + 2) := by
    have hn := constructionResidue_le_modulus m
    unfold constructionBase
    dsimp [Q, K, A]
    nlinarith
  calc
    constructionPoint m t + r ≤ Q * (K * A + 2 + T) + A * (K + H) := by
      unfold constructionPoint
      dsimp [Q, K, A, H, T] at *
      nlinarith
    _ ≤ Q * (A * (K + T + 2)) + A * (K + H) := by
      gcongr
      nlinarith
    _ ≤ (Q + 1) * A * (K + H + T + 2) := by
      have hnonneg := Nat.zero_le (Q * A * H + A * T + 2 * A)
      nlinarith only [hnonneg]
    _ ≤ (Q + 1) * (K + H + T + 3) * (A + 1) := by
      nlinarith
    _ = constructionUpperBound m := rfl

theorem sampled_shift_le_upper (m : ℕ) (t : Fin (progressionLength m)) (r : ConstructionShift m) :
    constructionPoint m t.val + r.val ≤ constructionUpperBound m :=
  constructionPoint_add_le_upper m t.val r.val t.isLt.le (constructionShift_le m r)

theorem sampled_dilation_le_upper (m : ℕ) (t : Fin (progressionLength m)) (i : PatternLabel m) :
    constructionPoint m t.val + constructionDilation m i ≤ constructionUpperBound m := by
  apply constructionPoint_add_le_upper m t.val _ t.isLt.le
  apply (constructionDilation_le_max m i).trans
  have hlen : 1 ≤ 6 * m + retainedLength m := by have h := retainedLength_pos m; omega
  simpa using Nat.mul_le_mul_left (constructionMaxDilation m) hlen

theorem log_nat_add_one_le (n : ℕ) (hn : 0 < n) :
    Real.log (n + 1 : ℕ) ≤ Real.log (n : ℝ) + 1 := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : ((n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * n := by exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have h := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (by norm_num) hpos.ne'] at h
  linarith [log_two_le_one]

theorem log_nat_add_le_log_mul (T C : ℕ) (hT : 0 < T) :
    Real.log (T + C : ℕ) ≤ Real.log (T : ℝ) + Real.log (C + 1 : ℕ) := by
  have hle : T + C ≤ T * (C + 1) := by nlinarith
  have h := Real.log_le_log
    (by exact_mod_cast (show 0 < T + C by omega) : (0 : ℝ) < (T + C : ℕ))
    (by exact_mod_cast hle : ((T + C : ℕ) : ℝ) ≤ (T : ℝ) * (C + 1 : ℕ))
  rwa [Real.log_mul (by positivity) (by positivity)] at h

theorem six_primeCutoff_add_five_le_excluded {m : ℕ} (hm : 0 < m) :
    6 * dilationPrimeCutoff m + 5 ≤ excludedPrimeCutoff m := by
  have hN := patternSize_ge_thirtysix hm
  have hP := dilationPrimeCutoff_pos m
  have hpow : 11 ≤ patternSize m ^ 12 := by
    have h : patternSize m ≤ patternSize m ^ 12 := by
      simpa using Nat.pow_le_pow_right (patternSize_pos m) (show 1 ≤ 12 by omega)
    omega
  apply le_trans _ (polynomial_primeCutoff_le_excluded hm)
  nlinarith

theorem log_constructionUpperBound_le {m : ℕ} (hm : 0 < m) :
    Real.log (constructionUpperBound m : ℝ) ≤
      Real.log (progressionLength m : ℝ) + 2 * excludedPrimeCutoff m := by
  have hQ := constructionModulus_pos m
  have hA := constructionMaxDilation_pos m
  have hT := progressionLength_pos m
  have hlen : 6 * m + retainedLength m ≤ dilationPrimeCutoff m :=
    (total_retainedLength_le_size_pow_five hm).trans (patternSize_pow_five_le_primeCutoff hm)
  have hlogQ := log_nat_add_one_le _ hQ
  have hlogA := log_nat_add_one_le _ hA
  have hlogsum := log_nat_add_le_log_mul (progressionLength m)
    (6 * m + retainedLength m + 3) hT
  have hlogC := Real.log_le_sub_one_of_pos
    (by positivity : (0 : ℝ) < ((6 * m + retainedLength m + 3 + 1 : ℕ) : ℝ))
  have hsum : 6 * m + retainedLength m + progressionLength m + 3 =
      progressionLength m + (6 * m + retainedLength m + 3) := by omega
  unfold constructionUpperBound
  rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), hsum]
  have hsize : (6 : ℝ) * dilationPrimeCutoff m + 5 ≤ excludedPrimeCutoff m := by
    exact_mod_cast six_primeCutoff_add_five_le_excluded hm
  have hlenR : ((6 * m + retainedLength m : ℕ) : ℝ) ≤ dilationPrimeCutoff m := by exact_mod_cast hlen
  push_cast at hlogC hlogsum hlogQ hlogA hlenR ⊢
  linarith [log_constructionModulus_le_excluded hm, log_constructionMaxDilation_le m]

end Erdos69.Elementary
