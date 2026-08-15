import ErdosProblems.Erdos321.SharpLogMass

namespace Erdos321

/-- Real iterated logarithms, with the zeroth iterate equal to the argument. -/
noncomputable def realIteratedLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (realIteratedLog k x)

/-- The product of the first `k` positive-index iterated logarithms. -/
noncomputable def iteratedLogTailProduct : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, x => Real.log x * iteratedLogTailProduct k (Real.log x)

/-- Every retained logarithmic coordinate, including the zeroth, lies above
one common terminal threshold. -/
def LogTowerAbove (B : ℝ) (k : ℕ) (x : ℝ) : Prop :=
  ∀ j ≤ k, B ≤ realIteratedLog j x

/-- Recursive nonvanishing condition needed for ordinary real derivatives of
all logarithms entering a tail product. -/
def LogRegular : ℕ → ℝ → Prop
  | 0, _ => True
  | k + 1, x => x ≠ 0 ∧ LogRegular k (Real.log x)

/-- Recursive positivity condition. -/
def LogPositive : ℕ → ℝ → Prop
  | 0, _ => True
  | k + 1, x => 0 < Real.log x ∧ LogPositive k (Real.log x)

theorem realIteratedLog_succ_shift (k : ℕ) (x : ℝ) :
    realIteratedLog (k + 1) x = realIteratedLog k (Real.log x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega]
      change Real.log (realIteratedLog (k + 1) x) =
        Real.log (realIteratedLog k (Real.log x))
      rw [ih]

/-- Appending one iterate appends exactly one factor. -/
theorem iteratedLogTailProduct_succ (k : ℕ) (x : ℝ) :
    iteratedLogTailProduct (k + 1) x =
      iteratedLogTailProduct k x * realIteratedLog (k + 1) x := by
  induction k generalizing x with
  | zero => simp [iteratedLogTailProduct, realIteratedLog]
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega]
      change Real.log x * iteratedLogTailProduct (k + 1) (Real.log x) = _
      rw [ih (Real.log x), realIteratedLog_succ_shift (k + 1) x]
      change _ = (Real.log x * iteratedLogTailProduct k (Real.log x)) * _
      ring

/-- Closed finite-product form of the recursive tail product. -/
theorem iteratedLogTailProduct_eq_prod (k : ℕ) (x : ℝ) :
    iteratedLogTailProduct k x =
      ∏ i ∈ Finset.range k, realIteratedLog (i + 1) x := by
  induction k with
  | zero => simp [iteratedLogTailProduct]
  | succ k ih =>
      rw [iteratedLogTailProduct_succ, ih, Finset.prod_range_succ]

/-- Above the threshold four, every reverse logarithm step expands by at
least a factor two. -/
theorem two_mul_iteratedLog_succ_le
    {B x : ℝ} {k j : ℕ} (hB : 4 ≤ B)
    (htower : LogTowerAbove B k x) (hj : j + 1 ≤ k) :
    2 * realIteratedLog (j + 1) x ≤ realIteratedLog j x := by
  let y := realIteratedLog (j + 1) x
  let z := realIteratedLog j x
  have hy : 4 ≤ y := hB.trans (htower (j + 1) hj)
  have hz : 4 ≤ z := hB.trans (htower j (by omega))
  have hzpos : 0 < z := by linarith
  have hy_nonneg : 0 ≤ y := by linarith
  have hylog : y = Real.log z := by
    dsimp [y, z]
    rw [show j + 1 = Nat.succ j by omega]
    rfl
  have hexp : Real.exp y = z := by
    rw [hylog, Real.exp_log hzpos]
  have hseries := Real.pow_div_factorial_le_exp y hy_nonneg 2
  norm_num at hseries
  rw [hexp] at hseries
  nlinarith [sq_nonneg (y - 4)]

/-- Iterating the preceding estimate gives geometric separation between any
retained coordinate and the terminal coordinate. -/
theorem pow_two_mul_terminal_iteratedLog_le
    {B x : ℝ} {j d : ℕ} (hB : 4 ≤ B)
    (htower : LogTowerAbove B (j + d) x) :
    (2 : ℝ) ^ d * realIteratedLog (j + d) x ≤ realIteratedLog j x := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprefix : LogTowerAbove B (j + d) x := by
        intro i hi
        exact htower i (by omega)
      have hih := ih hprefix
      have hedge := two_mul_iteratedLog_succ_le hB htower
        (show j + d + 1 ≤ j + (d + 1) by omega)
      have hpow : 0 ≤ (2 : ℝ) ^ d := by positivity
      calc
        (2 : ℝ) ^ (d + 1) * realIteratedLog (j + (d + 1)) x =
            (2 : ℝ) ^ d * (2 * realIteratedLog ((j + d) + 1) x) := by
              have hind : j + (d + 1) = (j + d) + 1 := by omega
              rw [hind, pow_succ]
              ring
        _ ≤ (2 : ℝ) ^ d * realIteratedLog (j + d) x :=
          mul_le_mul_of_nonneg_left hedge hpow
        _ ≤ realIteratedLog j x := hih

/-- A tower uniformly above a positive threshold satisfies the recursive
positivity predicate. -/
theorem logPositive_of_tower
    {B x : ℝ} {k : ℕ} (hB : 0 < B) (htower : LogTowerAbove B k x) :
    LogPositive k x := by
  induction k generalizing x with
  | zero => trivial
  | succ k ih =>
      have hlog : 0 < Real.log x := by
        have h := htower 1 (by omega)
        simpa [realIteratedLog] using lt_of_lt_of_le hB h
      constructor
      · exact hlog
      · apply ih
        intro j hj
        rw [← realIteratedLog_succ_shift j x]
        exact htower (j + 1) (by omega)

/-- A positive logarithmic tower has a nonnegative tail product. -/
theorem iteratedLogTailProduct_nonneg
    {k : ℕ} {x : ℝ} (hpos : LogPositive k x) :
    0 ≤ iteratedLogTailProduct k x := by
  induction k generalizing x with
  | zero => simp [iteratedLogTailProduct]
  | succ k ih =>
      rcases hpos with ⟨hlog, htail⟩
      dsimp [iteratedLogTailProduct]
      exact mul_nonneg hlog.le (ih htail)

/-- A strictly positive logarithmic tower has a strictly positive product. -/
theorem iteratedLogTailProduct_pos
    {k : ℕ} {x : ℝ} (hpos : LogPositive k x) :
    0 < iteratedLogTailProduct k x := by
  induction k generalizing x with
  | zero => simp [iteratedLogTailProduct]
  | succ k ih =>
      rcases hpos with ⟨hlog, htail⟩
      dsimp [iteratedLogTailProduct]
      exact mul_pos hlog (ih htail)

end Erdos321
