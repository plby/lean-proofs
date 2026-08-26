import Mathlib

/-!
# Quantitative parameters for the first small prime block

Finite subblock counts, threshold gaps, and the exponential scalar budget
are proved explicitly. The global block schedule is not assumed here.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrLogBlockIndices (H p q : ℝ) : Finset ℕ :=
  Finset.Icc (Nat.floor (H * p)) (Nat.floor (H * q))

theorem mrLogBlockIndices_parameter_bounds {H p q : ℝ}
    (hH : 1 ≤ H) (_hp : 0 ≤ p) (hq : 0 ≤ q) {r : ℕ}
    (hr : r ∈ mrLogBlockIndices H p q) : p - 1 ≤ (r : ℝ) / H ∧ (r : ℝ) / H ≤ q := by
  have hH0 : 0 < H := by linarith
  obtain ⟨hrlo, hrhi⟩ := Finset.mem_Icc.mp hr
  have hfloor : H * p < (Nat.floor (H * p) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hrlo' : (Nat.floor (H * p) : ℝ) ≤ r := by exact_mod_cast hrlo
  have hrhi' : (r : ℝ) ≤ H * q :=
    (Nat.cast_le.mpr hrhi).trans (Nat.floor_le (mul_nonneg hH0.le hq))
  constructor
  · apply (le_div_iff₀ hH0).mpr
    nlinarith
  · apply (div_le_iff₀ hH0).mpr
    nlinarith

theorem card_mrLogBlockIndices_le {H p q : ℝ} (hHq : 1 ≤ H * q) :
    ((mrLogBlockIndices H p q).card : ℝ) ≤ 2 * H * q := by
  have hc : (mrLogBlockIndices H p q).card ≤ Nat.floor (H * q) + 1 := by
    rw [mrLogBlockIndices, Nat.card_Icc]
    omega
  have hc' : ((mrLogBlockIndices H p q).card : ℝ) ≤ (Nat.floor (H * q) : ℝ) + 1 := by
    exact_mod_cast hc
  have hf := Nat.floor_le (by linarith : 0 ≤ H * q)
  nlinarith

theorem mrLogBlock_covering_cost_le
    {H Hprev p q pprev qprev : ℝ}
    (hH : 0 ≤ H) (_hHprev : 0 ≤ Hprev) (hq : 0 ≤ q) (hqprev : 0 ≤ qprev)
    (hHle : Hprev ≤ H) (hqle : qprev ≤ q)
    (hcur : 1 ≤ H * q) (hprev : 1 ≤ Hprev * qprev) :
    H * q * (mrLogBlockIndices H p q).card * (mrLogBlockIndices Hprev pprev qprev).card ≤
      4 * H ^ 3 * q ^ 3 := by
  have hcard := card_mrLogBlockIndices_le (p := p) hcur
  have hcardprev := card_mrLogBlockIndices_le (p := pprev) hprev
  have hscale : 2 * Hprev * qprev ≤ 2 * H * q := by gcongr
  calc
    _ ≤ H * q * (2 * H * q) * (2 * H * q) := by
      gcongr
      exact hcardprev.trans hscale
    _ = _ := by ring

def mrThresholdExponent (eta j : ℝ) : ℝ :=
  1 / 4 - eta * (1 + 1 / (2 * j))

theorem mrThresholdExponent_bounds {eta j : ℝ}
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1 / 6) (hj : 1 ≤ j) :
    0 ≤ mrThresholdExponent eta j ∧ mrThresholdExponent eta j ≤ 1 / 4 := by
  have hj0 : 0 < j := by linarith
  have hinv0 : 0 ≤ 1 / (2 * j) := by positivity
  have hinv : 1 / (2 * j) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  unfold mrThresholdExponent
  constructor <;> nlinarith

theorem mrThresholdExponent_gap {eta j : ℝ} (heta : 0 ≤ eta) (hj : 2 ≤ j) :
    eta / (2 * j ^ 2) ≤ mrThresholdExponent eta j - mrThresholdExponent eta (j - 1) := by
  have hj0 : 0 < j := by linarith
  have hjm : 0 < j - 1 := by linarith
  have heq : mrThresholdExponent eta j - mrThresholdExponent eta (j - 1) =
      eta / (2 * j * (j - 1)) := by
    unfold mrThresholdExponent
    field_simp
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left heta (by positivity)
  nlinarith

theorem amplification_cost_le_of_block_range
    {p q u v delta : ℝ} (hp : 2 ≤ p) (hu : p - 1 ≤ u) (hv : 1 ≤ v) (hvq : v ≤ q)
    (hsep : 6 * Real.log (2 * q) / (p - 1) ≤ delta) :
    6 * Real.log (2 * v) / u ≤ delta := by
  have hp0 : 0 < p - 1 := by linarith
  have hu0 : 0 < u := hp0.trans_le hu
  have hq1 : 1 ≤ q := hv.trans hvq
  have hlog : 0 ≤ Real.log (2 * q) := Real.log_nonneg (by linarith)
  calc
    _ ≤ 6 * Real.log (2 * q) / u := by
      apply div_le_div_of_nonneg_right ?_ hu0.le
      gcongr
    _ ≤ 6 * Real.log (2 * q) / (p - 1) :=
      div_le_div_of_nonneg_left (by positivity) hp0 hu
    _ ≤ delta := hsep

/-- The complete scalar absorption of the covering prefactor. -/
theorem firstSmallBlock_scalar_budget
    {H q j qprev p u v alpha delta : ℝ}
    (_hH : 0 ≤ H) (_hq : 0 ≤ q) (hj : 1 ≤ j) (hqprev : 2 ≤ qprev)
    (hu : 0 ≤ u) (huprev : u ≤ qprev) (hvp : p - 1 ≤ v)
    (_halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1 / 4)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hresolution : H ^ 3 * q ^ 3 ≤ j ^ 6 * Real.exp qprev)
    (hsep : 4 * qprev + 8 * Real.log j ≤ delta * p) :
    H ^ 3 * q ^ 3 * Real.exp ((1 + 2 * alpha) * u - delta * v) ≤
      1 / (j ^ 2 * Real.exp qprev) := by
  have hj0 : 0 < j := by linarith
  have hlocal : (1 + 2 * alpha) * u - delta * v ≤ 2 * qprev - delta * p := by
    have ha := mul_le_mul_of_nonneg_right halpha1 hu
    have hd := mul_le_mul_of_nonneg_left hvp hdelta0
    nlinarith
  calc
    _ ≤ (j ^ 6 * Real.exp qprev) * Real.exp (2 * qprev - delta * p) :=
      mul_le_mul hresolution (Real.exp_le_exp.mpr hlocal) (Real.exp_pos _).le (by positivity)
    _ = j ^ 6 * Real.exp (3 * qprev - delta * p) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ j ^ 6 * Real.exp (-qprev - 8 * Real.log j) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ = 1 / (j ^ 2 * Real.exp qprev) := by
      have hjexp : Real.exp (Real.log j) = j := Real.exp_log hj0
      have hjeight : Real.exp (8 * Real.log j) = j ^ 8 := by
        simpa only [Nat.cast_ofNat, hjexp] using Real.exp_nat_mul (Real.log j) 8
      rw [Real.exp_sub, Real.exp_neg, hjeight]
      field_simp

/-- The source partition resolution, expressed in logarithmic endpoints. -/
def mrLogBlockResolution (eta p₁ q₁ j : ℝ) : ℝ :=
  j ^ 2 * Real.exp ((1 / 6 - eta) * p₁ - Real.log q₁ / 3)

theorem mrLogBlockResolution_one_le {eta p₁ q₁ j : ℝ} (hj : 1 ≤ j)
    (hbase : 0 ≤ (1 / 6 - eta) * p₁ - Real.log q₁ / 3) :
    1 ≤ mrLogBlockResolution eta p₁ q₁ j := by
  have hjpow : (1 : ℝ) ≤ j ^ 2 := one_le_pow₀ hj
  have he := Real.one_le_exp_iff.mpr hbase
  unfold mrLogBlockResolution
  nlinarith

theorem mrLogBlockResolution_mono {eta p₁ q₁ i j : ℝ} (hi : 0 ≤ i) (hij : i ≤ j) :
    mrLogBlockResolution eta p₁ q₁ i ≤ mrLogBlockResolution eta p₁ q₁ j := by
  unfold mrLogBlockResolution
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hi hij 2) (Real.exp_pos _).le

theorem mrLogBlockResolution_cube (eta p₁ q₁ j : ℝ) :
    mrLogBlockResolution eta p₁ q₁ j ^ 3 =
      j ^ 6 * Real.exp ((1 / 2 - 3 * eta) * p₁ - Real.log q₁) := by
  unfold mrLogBlockResolution
  rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
  change j ^ 6 * Real.exp (3 * ((1 / 6 - eta) * p₁ - Real.log q₁ / 3)) = _
  congr 2
  ring

/-- The source resolution satisfies the prefactor bound used in the
class estimate, with the logarithmic endpoint hypotheses explicit. -/
theorem mrLogBlockResolution_prefactor_le
    {eta p₁ q₁ j q qprev : ℝ}
    (heta : 0 ≤ eta) (hp₁ : 0 ≤ p₁) (hq₁ : 1 ≤ q₁)
    (hpq : p₁ ≤ qprev) (hq : 1 ≤ q) (hlogq : 3 * Real.log q ≤ qprev / 2) :
    mrLogBlockResolution eta p₁ q₁ j ^ 3 * q ^ 3 ≤ j ^ 6 * Real.exp qprev := by
  have hq0 : 0 < q := by linarith
  have hlogq₁ : 0 ≤ Real.log q₁ := Real.log_nonneg hq₁
  have hexponent : ((1 / 2 - 3 * eta) * p₁ - Real.log q₁) + 3 * Real.log q ≤ qprev := by
    nlinarith [mul_nonneg heta hp₁]
  have hqexp : Real.exp (3 * Real.log q) = q ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hq0] using Real.exp_nat_mul (Real.log q) 3
  rw [mrLogBlockResolution_cube, ← hqexp, mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by positivity)

end

end Erdos67b
