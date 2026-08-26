import ErdosProblems.Erdos1188.PrimeLinearLog

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A fully explicit lower bound at every sufficiently large cutoff
-/

namespace Erdos1188

noncomputable section

/-- First binary-log layer. -/
def cutoffLog (x : ℕ) : ℕ := Nat.log 2 x

/-- A positive upper proxy for `log₂ log₂ x`. -/
def cutoffLogLog (x : ℕ) : ℕ := Nat.log 2 (cutoffLog x + 1) + 1

/-- A positive upper proxy for the next iterated logarithm. -/
def cutoffLogLogLog (x : ℕ) : ℕ := Nat.log 2 (cutoffLogLog x) + 1

/-- An explicit frame dimension fitting below cutoff `x`. -/
def lowerFrameIndex (x : ℕ) : ℕ :=
  cutoffLog x / (8 + cutoffLogLog x + cutoffLogLogLog x)

/-- The near-optimal frame cutoff at `lowerFrameIndex x` really is no larger
than `x`. -/
theorem linearLogPrimeCutoff_lowerFrameIndex_le (x : ℕ) (hx : x ≠ 0) :
    linearLogPrimeCutoff (lowerFrameIndex x) ≤ x := by
  let L := cutoffLog x
  let l := cutoffLogLog x
  let ll := cutoffLogLogLog x
  let D := 8 + l + ll
  let m := lowerFrameIndex x
  let R := Nat.log 2 m + 1
  have hDpos : 0 < D := by simp [D]
  have hmL : m ≤ L := by
    simp only [m, lowerFrameIndex, L, l, ll, D]
    exact Nat.div_le_self _ _
  have hRl : R ≤ l := by
    have hm : m ≤ L + 1 := le_trans hmL (Nat.le_succ L)
    exact Nat.add_le_add_right (Nat.log_mono_right hm) 1
  have hll : l < 2 ^ ll := by
    simpa [ll, cutoffLogLogLog] using
      Nat.lt_pow_succ_log_self (b := 2) (by decide) l
  have hRpow : R ≤ 2 ^ ll := le_trans hRl hll.le
  have hpowRl : 2 ^ R ≤ 2 ^ l :=
    Nat.pow_le_pow_right (by decide) hRl
  have hscale : binaryPrimeScale m ≤ 2 ^ (7 + ll + l) := by
    unfold binaryPrimeScale
    change 128 * R * 2 ^ R ≤ _
    calc
      128 * R * 2 ^ R ≤ 128 * 2 ^ ll * 2 ^ l := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 128 hRpow) hpowRl
      _ = 2 ^ (7 + ll + l) := by
        norm_num [pow_add, Nat.mul_assoc]
  have hmD : m * D ≤ L := by
    simp only [m, lowerFrameIndex, L, l, ll, D]
    exact Nat.div_mul_le_self _ _
  have hcut : linearLogPrimeCutoff m ≤ 2 ^ (m * D) := by
    unfold linearLogPrimeCutoff
    calc
      2 ^ m * binaryPrimeScale m ^ m ≤ 2 ^ m * (2 ^ (7 + ll + l)) ^ m :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale m)
      _ = 2 ^ (m * D) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        simp only [D]
        ring
  exact le_trans hcut <| le_trans (Nat.pow_le_pow_right (by decide) hmD)
    (Nat.pow_log_le_self 2 hx)

/-- Every nonzero cutoff whose explicit frame index is at least six satisfies a
double-exponential lower bound. -/
theorem explicit_all_cutoffs_lower (x : ℕ) (hx : x ≠ 0)
    (hlarge : 6 ≤ lowerFrameIndex x) :
    2 ^ (2 ^ (lowerFrameIndex x - 2)) ≤ coveringCount x := by
  exact le_trans (explicit_linearLog_cutoff_lower (lowerFrameIndex x) hlarge)
    (coveringCount_mono (linearLogPrimeCutoff_lowerFrameIndex_le x hx))

/-- Strong all-cutoff form obtained by counting all top-coordinate
injections. -/
theorem explicit_all_cutoffs_lower_strong (x : ℕ) (hx : x ≠ 0)
    (hlarge : 6 ≤ lowerFrameIndex x) :
    2 ^ ((lowerFrameIndex x - 1) * 2 ^ (lowerFrameIndex x - 2)) ≤
      coveringCount x := by
  exact le_trans
    (explicit_linearLog_cutoff_lower_strong (lowerFrameIndex x) hlarge)
    (coveringCount_mono (linearLogPrimeCutoff_lowerFrameIndex_le x hx))

end

end Erdos1188
