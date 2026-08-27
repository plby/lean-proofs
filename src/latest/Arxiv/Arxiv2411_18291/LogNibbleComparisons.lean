import Arxiv.Arxiv2411_18291.NibbleComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithmic error comparisons for small clique sizes

The parameter `a` is the cube root of the initial regularity error. These
comparisons use coefficients three and four, and will be stopped above
five halves of the target density. Their smaller relative errors retain
room in the finite drift estimates where the reciprocal comparisons fail.
-/

noncomputable section

namespace Arxiv2411_18291

def nibbleLogFactor (k : ℕ) (p : ℝ) : ℝ := 1 - k * Real.log p

def logNibbleDegreeError (k : ℕ) (a D p : ℝ) : ℝ :=
  3 * nibbleLogFactor k p * a ^ 2 * D

def logNibbleCliqueError (k : ℕ) (a g D p : ℝ) : ℝ :=
  4 * (nibbleLogFactor k p) ^ 2 * a ^ 3 * D * g

theorem nibbleLogFactor_one_le (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    1 ≤ nibbleLogFactor k p := by
  have hlog := Real.log_nonpos hp.le hp1
  have hmul := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k (α := ℝ)) hlog
  unfold nibbleLogFactor
  linarith only [hmul]

theorem nibbleLogFactor_sq_mul_pow_le_three {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (nibbleLogFactor k p) ^ 2 * p ^ (k - 1) ≤ 3 := by
  let z := -((k - 1 : ℕ) : ℝ) * Real.log p
  have hlog := Real.log_nonpos hp.le hp1
  have hz : 0 ≤ z := mul_nonneg_of_nonpos_of_nonpos
    (neg_nonpos.mpr (Nat.cast_nonneg _)) hlog
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hL := nibbleLogFactor_one_le k hp hp1
  have hLz : nibbleLogFactor k p ≤ 1 + 3 / 2 * z := by
    have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ (k : ℝ) - 3 by linarith) hlog
    dsimp only [nibbleLogFactor, z]
    rw [hkm]
    linarith only [hm]
  have ht := Real.sum_le_exp_of_nonneg hz 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have hpoly := mul_nonneg (show 0 ≤ 2 * z + 1 by linarith) (sq_nonneg (z - 1))
  have hsq : (nibbleLogFactor k p) ^ 2 ≤ 3 * Real.exp z := by
    have hs := sq_le_sq₀ (by linarith only [hL]) (by positivity) |>.mpr hLz
    nlinarith only [hs, ht, hpoly]
  have hpow : p ^ (k - 1) = Real.exp (-z) := by
    rw [show -z = ((k - 1 : ℕ) : ℝ) * Real.log p by dsimp [z]; ring]
    rw [Real.exp_nat_mul, Real.exp_log hp]
  rw [hpow]
  calc
    _ ≤ (3 * Real.exp z) * Real.exp (-z) :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)
    _ = 3 := by rw [mul_assoc, ← Real.exp_add]; simp

theorem nibbleLogFactor_sq_mul_pow_le_three_of_le {k j : ℕ} (hk : 3 ≤ k)
    (hkj : k - 1 ≤ j) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (nibbleLogFactor k p) ^ 2 * p ^ j ≤ 3 := by
  apply le_trans _ (nibbleLogFactor_sq_mul_pow_le_three hk hp hp1)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hp.le hp1 hkj) (sq_nonneg _)

theorem nibbleLogFactor_hasDerivAt (k : ℕ) {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (nibbleLogFactor k) (-(k : ℝ) / p) p := by
  convert! (hasDerivAt_const p (1 : ℝ)).sub
    (HasDerivAt.const_mul (k : ℝ) (Real.hasDerivAt_log hp)) using 1
  simp [div_eq_mul_inv]

theorem nibbleLogFactor_mul_le_rank {k : ℕ} (hk : 1 ≤ k) {p : ℝ}
    (hp : 0 < p) : nibbleLogFactor k p * p ≤ k := by
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hl
  have hl' := mul_le_mul_of_nonneg_right hl hp.le
  have hid : p⁻¹ * p = 1 := inv_mul_cancel₀ hp.ne'
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp' := mul_nonneg (show 0 ≤ (k : ℝ) - 1 by linarith) hp.le
  have hlp : -Real.log p * p ≤ 1 - p := by nlinarith only [hl', hid]
  have hl'' := mul_le_mul_of_nonneg_left hlp (Nat.cast_nonneg k (α := ℝ))
  unfold nibbleLogFactor
  nlinarith only [hl'', hp']

theorem nibbleLogFactor_weighted_power {k j t : ℕ} (hk : 3 ≤ k)
    (hkt : t + (k - 1) ≤ k * j) {p a c : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hac : a ≤ c ^ k * p ^ k) :
    (nibbleLogFactor k p) ^ 2 * a ^ j ≤ 3 * c ^ (k * j) * p ^ t := by
  have ht : t ≤ k * j := by omega
  have hdecomp : k * j - t + t = k * j := Nat.sub_add_cancel ht
  have hpow : p ^ (k * j) = p ^ (k * j - t) * p ^ t := by
    rw [← pow_add, hdecomp]
  have hb := nibbleLogFactor_sq_mul_pow_le_three_of_le hk
    (show k - 1 ≤ k * j - t by omega) hp hp1
  calc
    _ ≤ (nibbleLogFactor k p) ^ 2 * (c ^ k * p ^ k) ^ j :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hac j) (sq_nonneg _)
    _ = c ^ (k * j) * ((nibbleLogFactor k p) ^ 2 * p ^ (k * j - t)) * p ^ t := by
      rw [mul_pow, ← pow_mul, ← pow_mul, hpow]
      ring
    _ ≤ c ^ (k * j) * 3 * p ^ t :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (pow_nonneg hc _)) (pow_nonneg hp.le _)
    _ = _ := by ring

end Arxiv2411_18291
