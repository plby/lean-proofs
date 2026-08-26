import ErdosProblems.Erdos394.HierarchyParameters
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Dense power-of-sixteen parameters for the hierarchy
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

/-- Binary logarithmic scale attached to the dense grid exponent. -/
def denseHierarchyLog (N : ℕ) : ℕ := Nat.log 2 N

/-- Medium-prime exponents and the corresponding arithmetic parameters. -/
def denseLowerExponent (N : ℕ) : ℕ := denseHierarchyLog N ^ 2
def denseUpperExponent (N : ℕ) : ℕ :=
  N / denseHierarchyLog N ^ 4
def denseHierarchyX (N : ℕ) : ℕ := 16 ^ N
def denseHierarchyZ (N : ℕ) : ℕ := 16 ^ denseLowerExponent N
def denseHierarchyY (N : ℕ) : ℕ := 16 ^ denseUpperExponent N
def denseRootHeight (N : ℕ) : ℕ := 16 ^ denseHierarchyLog N
def denseDilution (N : ℕ) : ℕ := denseHierarchyLog N ^ 60
noncomputable def denseHierarchyOrder (N : ℕ) : ℕ :=
  geometricBrunOrder (denseUpperExponent N)

lemma denseHierarchyOrder_even (N : ℕ) : Even (denseHierarchyOrder N) :=
  geometricBrunOrder_even _

/-- Binary logarithm tends to infinity. -/
theorem tendsto_denseHierarchyLog_atTop :
    Tendsto denseHierarchyLog atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (2 ^ b)] with N hN
  unfold denseHierarchyLog
  exact Nat.le_log_of_pow_le (by norm_num) hN

/-- Every fixed polynomial is eventually dominated by `2^h`. -/
theorem eventually_nat_pow_le_two_pow (a : ℕ) :
    ∀ᶠ h : ℕ in atTop, h ^ a ≤ 2 ^ h := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmallR := (isLittleO_pow_exp_pos_mul_atTop a hlog2).bound
    (by norm_num : (0 : ℝ) < 1)
  have hsmall := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmallR
  filter_upwards [hsmall] with h hh
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ h ^ a),
    one_mul, abs_of_pos (Real.exp_pos _)] at hh
  have hexp : Real.exp (Real.log 2 * (h : ℝ)) = ((2 ^ h : ℕ) : ℝ) := by
    rw [mul_comm]
    calc
      Real.exp ((h : ℝ) * Real.log 2) =
          (Real.exp (Real.log 2)) ^ h := Real.exp_nat_mul _ _
      _ = (2 : ℝ) ^ h := by rw [Real.exp_log (by norm_num)]
      _ = ((2 ^ h : ℕ) : ℝ) := by norm_num
  rw [hexp] at hh
  exact_mod_cast hh

/-- Along the dense exponent `N`, every fixed power of its binary logarithm
is eventually at most `N`. -/
theorem eventually_denseLog_pow_le (a : ℕ) :
    ∀ᶠ N : ℕ in atTop, denseHierarchyLog N ^ a ≤ N := by
  have hpoly := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_nat_pow_le_two_pow a)
  filter_upwards [eventually_gt_atTop 0, hpoly] with N hN hpow
  exact hpow.trans (Nat.pow_log_le_self 2 hN.ne')

/-- The lower medium-prime exponent lies below the upper one eventually. -/
theorem eventually_denseLower_le_upper :
    ∀ᶠ N : ℕ in atTop,
      denseLowerExponent N ≤ denseUpperExponent N := by
  have h6 := eventually_denseLog_pow_le 6
  have hpos := tendsto_denseHierarchyLog_atTop.eventually (eventually_ge_atTop 1)
  filter_upwards [h6, hpos] with N hN hlog
  unfold denseLowerExponent denseUpperExponent
  apply (Nat.le_div_iff_mul_le (pow_pos hlog 4)).2
  simpa [pow_succ, pow_two, mul_assoc, mul_left_comm, mul_comm] using hN

/-- The upper endpoint exponent tends to infinity. -/
theorem tendsto_denseUpperExponent_atTop :
    Tendsto denseUpperExponent atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  have hloglarge := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop (max b 2))
  have h5 := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_nat_pow_le_two_pow 5)
  filter_upwards [eventually_gt_atTop 0, hloglarge, h5] with N hN hlog hpow
  let h := denseHierarchyLog N
  have hhpos : 0 < h := by dsimp [h]; omega
  have htwo : 2 * h ^ 4 ≤ h ^ 5 := by
    have : 2 ≤ h := by dsimp [h]; omega
    calc
      2 * h ^ 4 ≤ h * h ^ 4 := Nat.mul_le_mul_right _ this
      _ = h ^ 5 := by ring
  have hNlower : 2 * h ^ 4 ≤ N := by
    apply htwo.trans
    exact hpow.trans (Nat.pow_log_le_self 2 hN.ne')
  have hbpow : b * h ^ 4 ≤ N := by
    calc
      b * h ^ 4 ≤ h * h ^ 4 := Nat.mul_le_mul_right _ (by dsimp [h]; omega)
      _ = h ^ 5 := by ring
      _ ≤ N := hpow.trans (Nat.pow_log_le_self 2 hN.ne')
  have hbdiv : b ≤ N / h ^ 4 :=
    (Nat.le_div_iff_mul_le (pow_pos hhpos 4)).2 hbpow
  simpa [denseUpperExponent, h] using hbdiv

set_option maxRecDepth 10000 in
/-- Eventually the geometric Brun order at the upper endpoint is at most one
thousand times the binary logarithm. -/
theorem eventually_denseHierarchyOrder_le :
    ∀ᶠ N : ℕ in atTop,
      denseHierarchyOrder N ≤ 1000 * denseHierarchyLog N := by
  have hloglarge := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop 2)
  have hupperpos := tendsto_denseUpperExponent_atTop.eventually
    (eventually_ge_atTop 2)
  filter_upwards [eventually_gt_atTop 0, hloglarge, hupperpos] with N hN hh hJy
  let h := denseHierarchyLog N
  let Jy := denseUpperExponent N
  have hhpos : (0 : ℝ) < h := by positivity
  have hJypos : (0 : ℝ) < Jy := by positivity
  have hJyN : Jy ≤ N := by
    dsimp [Jy, denseUpperExponent]
    exact Nat.div_le_self _ _
  have hNpow : N < 2 ^ (h + 1) := by
    dsimp [h, denseHierarchyLog]
    exact Nat.lt_pow_succ_log_self (by norm_num) N
  have hlogJyN : Real.log (Jy : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hJypos (by exact_mod_cast hJyN)
  have hlogNpow : Real.log (N : ℝ) < Real.log ((2 ^ (h + 1) : ℕ) : ℝ) :=
    Real.strictMonoOn_log
      (show (0 : ℝ) < N by exact_mod_cast hN)
      (show (0 : ℝ) < (2 ^ (h + 1) : ℕ) by positivity)
      (by exact_mod_cast hNpow)
  have hlogpow : Real.log (((2 ^ (h + 1) : ℕ) : ℝ)) =
      (h + 1 : ℕ) * Real.log 2 := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow]
  have hlog2le : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
  have hlogJy : Real.log (Jy : ℝ) < (h + 1 : ℕ) := by
    rw [hlogpow] at hlogNpow
    have hcast : (0 : ℝ) ≤ (h + 1 : ℕ) := by positivity
    nlinarith [mul_lt_mul_of_pos_left hlog2le (show (0 : ℝ) < (h + 1 : ℕ) by positivity)]
  have harg0 : 0 ≤ 100 * (1 + Real.log Jy) := by
    have hJy1 : 1 ≤ Jy := by dsimp [Jy]; omega
    have : 0 ≤ Real.log (Jy : ℝ) := Real.log_nonneg (by exact_mod_cast hJy1)
    positivity
  have hceil := Nat.ceil_lt_add_one harg0
  have hRcast : (denseHierarchyOrder N : ℝ) <
      200 * (1 + Real.log Jy) + 2 := by
    unfold denseHierarchyOrder geometricBrunOrder
    push_cast
    nlinarith
  have hfinal : (denseHierarchyOrder N : ℝ) ≤ 1000 * (h : ℝ) := by
    have hh2 : (2 : ℝ) ≤ h := by exact_mod_cast hh
    push_cast at hlogJy
    nlinarith
  exact_mod_cast hfinal

end Erdos394
