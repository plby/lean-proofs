import ErdosProblems.Erdos920.ContainerNumeric
import ErdosProblems.Erdos920.NumericAbsorption

/-!
# The stopping-power inequality in real-logarithmic scale

`ContainerNumeric` proves the exact contraction estimate with a
binary-logarithmic budget.  This file compares that budget with
`A*q*ceil(log q)` and packages explicit parameters for the projective
construction.
-/

namespace Erdos920.StoppingPower

open Erdos920.ContainerNumeric

noncomputable section

/-- A coefficient large enough for all projective contraction blocks. -/
def stoppingCoefficient (t : ℕ) : ℕ :=
  320 * t * t * (t + 1)

/-- The real-logarithmic stopping depth. -/
def stoppingDepth (t q : ℕ) : ℕ :=
  stoppingCoefficient t * q * ⌈Real.log (q : ℝ)⌉₊

/-- The projective contraction parameter. -/
def branchFactor (t q : ℕ) : ℕ := 32 * t * q

/-- The projective ambient terminal bound. -/
def terminalBound (t q : ℕ) : ℕ := 2 * q ^ t

/-! ## Comparing the two logarithmic scales -/

/-- The elementary estimate `q ≤ 4^ceil(log q)`. -/
theorem le_four_pow_ceil_log {q : ℕ} (hq : 2 ≤ q) :
    q ≤ 4 ^ ⌈Real.log (q : ℝ)⌉₊ := by
  let z := ⌈Real.log (q : ℝ)⌉₊
  have hqR : (0 : ℝ) < q := by positivity
  have hlog : Real.log (q : ℝ) ≤ (z : ℝ) := by
    simpa [z] using Nat.le_ceil (Real.log (q : ℝ))
  have hexp : (q : ℝ) ≤ Real.exp (z : ℝ) := by
    rw [← Real.exp_log hqR]
    exact Real.exp_le_exp.mpr hlog
  have hbase : Real.exp 1 ≤ (4 : ℝ) :=
    Real.exp_one_lt_three.le.trans (by norm_num)
  have hpow : Real.exp 1 ^ z ≤ (4 : ℝ) ^ z := by
    exact pow_le_pow_left₀ (Real.exp_pos 1).le hbase z
  have hexp' : Real.exp (z : ℝ) = Real.exp 1 ^ z := by
    simp
  rw [hexp'] at hexp
  exact_mod_cast hexp.trans hpow

/-- Binary logarithm is bounded by twice the ceiling of the natural
logarithm, with one extra copy absorbing the final `+1`. -/
theorem natLogTwo_add_one_le_three_ceil_log {q : ℕ} (hq : 4 ≤ q) :
    Nat.log 2 q + 1 ≤ 3 * ⌈Real.log (q : ℝ)⌉₊ := by
  let L := Nat.log 2 q
  let z := ⌈Real.log (q : ℝ)⌉₊
  have hq0 : q ≠ 0 := by omega
  have hlow : 2 ^ L ≤ q := by
    simpa [L] using Nat.pow_log_le_self 2 hq0
  have hupp : q ≤ 2 ^ (2 * z) := by
    calc
      q ≤ 4 ^ z := by
        simpa [z] using le_four_pow_ceil_log (by omega : 2 ≤ q)
      _ = 2 ^ (2 * z) := by rw [show 4 = 2 ^ 2 by norm_num, pow_mul]
  have hpow : 2 ^ L ≤ 2 ^ (2 * z) := hlow.trans hupp
  have hLz : L ≤ 2 * z :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
  have hz : 1 ≤ z := by
    have hlog : (0 : ℝ) < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    exact Nat.ceil_pos.mpr hlog
  calc
    Nat.log 2 q + 1 = L + 1 := by rfl
    _ ≤ 2 * z + z := Nat.add_le_add hLz hz
    _ = 3 * ⌈Real.log (q : ℝ)⌉₊ := by simp [z]; ring

/-- The exact discrete budget fits in the real-logarithmic budget. -/
theorem contractionBudget_le_stoppingDepth {t q : ℕ}
    (ht : 1 ≤ t) (hq : 4 ≤ q) :
    contractionBudget (branchFactor t q) t q ≤ stoppingDepth t q := by
  let z := ⌈Real.log (q : ℝ)⌉₊
  have hz : 1 ≤ z := by
    have hlog : (0 : ℝ) < Real.log (q : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    exact Nat.ceil_pos.mpr hlog
  have hlog := natLogTwo_add_one_le_three_ceil_log hq
  have hblocks : stoppingBlocks t q ≤ 5 * t * z := by
    calc
      stoppingBlocks t q = t * (Nat.log 2 q + 1) + 2 := rfl
      _ ≤ t * (3 * z) + 2 * z := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_left t (by simpa [z] using hlog)
        · omega
      _ = (3 * t + 2) * z := by ring
      _ ≤ (5 * t) * z := Nat.mul_le_mul_right z (by omega)
      _ = 5 * t * z := by ring
  calc
    contractionBudget (branchFactor t q) t q =
        64 * t * q * stoppingBlocks t q := by
      unfold contractionBudget branchFactor
      ring
    _ ≤ 64 * t * q * (5 * t * z) := Nat.mul_le_mul_left _ hblocks
    _ = 320 * t * t * q * z := by ring
    _ ≤ (320 * t * t * q * z) * (t + 1) :=
      by
        simpa using Nat.mul_le_mul_left (320 * t * t * q * z)
          (show 1 ≤ t + 1 by omega)
    _ = 320 * t * t * (t + 1) * q * z := by ring
    _ = stoppingDepth t q := by simp [stoppingDepth, stoppingCoefficient, z]

/-! ## Projective specialization -/

theorem stoppingCoefficient_pos {t : ℕ} (ht : 1 ≤ t) :
    1 ≤ stoppingCoefficient t := by
  have : 0 < stoppingCoefficient t := by
    simp only [stoppingCoefficient]
    positivity
  omega

/-- **Stopping-power inequality.**  Once the exponent is larger than the
explicit `q*ceil(log q)` depth, replacing `2*K` by `2*K-1` absorbs the whole
terminal factor `2*q^t+1`. -/
theorem projective_stopping_power {t q c : ℕ}
    (ht : 2 ≤ t) (hq : 4 ≤ q) (hc : stoppingDepth t q < c) :
    (2 * branchFactor t q - 1) ^ c * (terminalBound t q + 1) <
      (2 * branchFactor t q) ^ c := by
  apply projective_contraction_stopping
      (t := t) (q := q) (N := terminalBound t q)
      (by omega) (by omega) (by simp [terminalBound]) c
  exact (contractionBudget_le_stoppingDepth (by omega) hq).trans_lt hc

/-- Expanded form, convenient before the abbreviations above are introduced. -/
theorem projective_stopping_power_expanded {t q c : ℕ}
    (ht : 2 ≤ t) (hq : 4 ≤ q)
    (hc : stoppingCoefficient t * q * ⌈Real.log (q : ℝ)⌉₊ < c) :
    (2 * (32 * t * q) - 1) ^ c * (2 * q ^ t + 1) <
      (2 * (32 * t * q)) ^ c := by
  exact projective_stopping_power ht hq hc

/-- Existential packaging with the explicit choices
`Astop = 320*t*t*(t+1)` and `Q = 4`. -/
theorem exists_stopping_parameters (t : ℕ) (ht : 2 ≤ t) :
    ∃ Astop Q : ℕ, 1 ≤ Astop ∧ 2 ≤ Q ∧
      ∀ q c : ℕ, Q ≤ q →
        Astop * q * ⌈Real.log (q : ℝ)⌉₊ < c →
          (2 * (32 * t * q) - 1) ^ c * (2 * q ^ t + 1) <
            (2 * (32 * t * q)) ^ c := by
  refine ⟨stoppingCoefficient t, 4, stoppingCoefficient_pos (by omega),
    by omega, ?_⟩
  intro q c hq hc
  exact projective_stopping_power_expanded ht hq hc

end

end Erdos920.StoppingPower
