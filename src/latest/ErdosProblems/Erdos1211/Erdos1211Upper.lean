import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import ErdosProblems.Erdos1211.Erdos1211DensityNat

namespace Erdos1211Upper

open scoped BigOperators Topology
open Filter Finset Set

attribute [local instance] Classical.propDecidable
noncomputable section

/-- The unit `2 + sqrt 3`, encoded by its action on Pell pairs. -/
def pellPair : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | n + 1 =>
      let z := pellPair n
      (2 * z.1 + 3 * z.2, z.1 + 2 * z.2)

/-- Integer logarithmic block endpoints: `1,4,15,56,...`. -/
def scale (n : ℕ) : ℕ := (pellPair n).2

@[simp] lemma pellPair_zero : pellPair 0 = (2, 1) := rfl

@[simp] lemma pellPair_succ (n : ℕ) :
    pellPair (n + 1) =
      (2 * (pellPair n).1 + 3 * (pellPair n).2,
        (pellPair n).1 + 2 * (pellPair n).2) := by
  simp [pellPair]

lemma pellPair_pos (n : ℕ) : 0 < (pellPair n).1 ∧ 0 < (pellPair n).2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pellPair_succ]
      omega

@[simp] lemma scale_zero : scale 0 = 1 := rfl

@[simp] lemma scale_succ (n : ℕ) :
    scale (n + 1) = (pellPair n).1 + 2 * scale n := by
  simp [scale]

lemma scale_pos (n : ℕ) : 0 < scale n := (pellPair_pos n).2

lemma scale_strictMono : StrictMono scale := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [scale_succ]
  have hp := (pellPair_pos n).1
  have hq := scale_pos n
  omega

lemma scale_add_two (n : ℕ) :
    scale (n + 2) + scale n = 4 * scale (n + 1) := by
  simp only [scale, pellPair_succ]
  omega

lemma scale_two_mul_le_add_two (n : ℕ) :
    2 * scale (n + 1) ≤ scale (n + 2) := by
  have hrec := scale_add_two n
  have h := scale_strictMono.monotone (Nat.le_add_right n 1)
  omega

def threshold (n : ℕ) : ℕ := 2 ^ scale n

lemma threshold_pos (n : ℕ) : 0 < threshold n := by
  simp [threshold]

lemma threshold_strictMono : StrictMono threshold := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact Nat.pow_lt_pow_right (by norm_num) (scale_strictMono (Nat.lt_succ_self n))

lemma threshold_square_le_next_same_color (n : ℕ) :
    threshold (n + 1) ^ 2 ≤ threshold (n + 2) := by
  rw [threshold, threshold, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num) (by
    rw [mul_comm]
    exact scale_two_mul_le_add_two n)

lemma add_one_le_scale (n : ℕ) : n + 1 ≤ scale n := by
  induction n with
  | zero => simp
  | succ n ih =>
      change n + 2 ≤ scale (n + 1)
      have hstep : scale n < scale (n + 1) := scale_strictMono (Nat.lt_succ_self n)
      omega

lemma exists_lt_threshold (n : ℕ) : ∃ k : ℕ, n < threshold (k + 1) := by
  refine ⟨n, lt_of_lt_of_le n.lt_two_pow_self ?_⟩
  rw [threshold]
  exact Nat.pow_le_pow_right (by norm_num) (by
    have h := add_one_le_scale (n + 1)
    omega)

/-- The least logarithmic block whose right endpoint is above `n`. -/
noncomputable def blockIndex (n : ℕ) : ℕ := Nat.find (exists_lt_threshold n)

lemma lt_threshold_succ_blockIndex (n : ℕ) :
    n < threshold (blockIndex n + 1) := by
  exact Nat.find_spec (exists_lt_threshold n)

lemma blockIndex_mono : Monotone blockIndex := by
  intro x y hxy
  apply Nat.find_min' (exists_lt_threshold x)
  exact hxy.trans_lt (lt_threshold_succ_blockIndex y)

lemma threshold_blockIndex_le {n : ℕ} (hn : 2 ≤ n) :
    threshold (blockIndex n) ≤ n := by
  by_cases hzero : blockIndex n = 0
  · simpa [threshold, hzero] using hn
  · have hpred : blockIndex n - 1 < blockIndex n := Nat.sub_one_lt hzero
    have hmin := Nat.find_min (exists_lt_threshold n) hpred
    simp only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hzero)] at hmin
    exact le_of_not_gt hmin

lemma lt_threshold_of_blockIndex_le {x k : ℕ} (hxk : blockIndex x ≤ k) :
    x < threshold (k + 1) := by
  exact (lt_threshold_succ_blockIndex x).trans_le
    (threshold_strictMono.monotone (Nat.add_le_add_right hxk 1))

lemma exists_le_threshold (n : ℕ) : ∃ k : ℕ, n ≤ threshold (k + 1) := by
  obtain ⟨k, hk⟩ := exists_lt_threshold n
  exact ⟨k, hk.le⟩

/-- Closed-right block convention: block `k` is `(threshold k, threshold (k+1)]`. -/
noncomputable def closedBlockIndex (n : ℕ) : ℕ := Nat.find (exists_le_threshold n)

lemma le_threshold_succ_closedBlockIndex (n : ℕ) :
    n ≤ threshold (closedBlockIndex n + 1) := Nat.find_spec (exists_le_threshold n)

lemma closedBlockIndex_mono : Monotone closedBlockIndex := by
  intro x y hxy
  apply Nat.find_min' (exists_le_threshold x)
  exact hxy.trans (le_threshold_succ_closedBlockIndex y)

lemma threshold_closedBlockIndex_lt {n : ℕ} (hn : 3 ≤ n) :
    threshold (closedBlockIndex n) < n := by
  by_cases hzero : closedBlockIndex n = 0
  · rw [hzero, threshold, scale_zero]
    norm_num
    omega
  · have hpred : closedBlockIndex n - 1 < closedBlockIndex n := Nat.sub_one_lt hzero
    have hmin := Nat.find_min (exists_le_threshold n) hpred
    simp only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hzero)] at hmin
    exact lt_of_not_ge hmin

lemma le_threshold_of_closedBlockIndex_le {x k : ℕ}
    (hxk : closedBlockIndex x ≤ k) : x ≤ threshold (k + 1) := by
  exact (le_threshold_succ_closedBlockIndex x).trans
    (threshold_strictMono.monotone (Nat.add_le_add_right hxk 1))

lemma finset_sum_lt_sq_of_lt {T : ℕ} (hT : 0 < T) {F : Finset ℕ}
    (hF : ∀ x ∈ F, x < T) : ∑ x ∈ F, x < T ^ 2 := by
  by_cases hFempty : F = ∅
  · simp [hFempty, hT]
  have hne : F.Nonempty := Finset.nonempty_iff_ne_empty.2 hFempty
  have hsum : ∑ x ∈ F, x < ∑ _x ∈ F, T :=
    Finset.sum_lt_sum_of_nonempty hne hF
  have hcard : F.card ≤ T := by
    simpa using Finset.card_le_card (t := Finset.range T)
      (fun x hx ↦ Finset.mem_range.2 (hF x hx))
  calc
    ∑ x ∈ F, x < F.card * T := by simpa using hsum
    _ ≤ T * T := Nat.mul_le_mul_right T hcard
    _ = T ^ 2 := by ring

lemma finset_sum_le_sq_of_pos_le {T : ℕ} {F : Finset ℕ}
    (hF : ∀ x ∈ F, 0 < x ∧ x ≤ T) : ∑ x ∈ F, x ≤ T ^ 2 := by
  have hsub : F ⊆ Finset.Icc 1 T := by
    intro x hx
    exact Finset.mem_Icc.2 ⟨hF x hx |>.1, hF x hx |>.2⟩
  have hcard : F.card ≤ T := by
    have := Finset.card_le_card hsub
    simpa using this
  calc
    ∑ x ∈ F, x ≤ ∑ _x ∈ F, T := by
      apply Finset.sum_le_sum
      exact fun x hx ↦ hF x hx |>.2
    _ = F.card * T := by simp
    _ ≤ T * T := Nat.mul_le_mul_right T hcard
    _ = T ^ 2 := by ring

lemma sum_Ico_inv_succ_le_log_ratio
    {m U : ℕ} (hm : 1 ≤ m) (hmU : m ≤ U) :
    (∑ k ∈ Finset.Ico m U, (((k + 1 : ℕ) : ℝ))⁻¹) ≤
      Real.log ((U : ℝ) / (m : ℝ)) := by
  calc
    (∑ k ∈ Finset.Ico m U, (((k + 1 : ℕ) : ℝ))⁻¹) ≤
        ∑ k ∈ Finset.Ico m U,
          (Real.log (k + 1 : ℕ) - Real.log k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkData := Finset.mem_Ico.mp hk
      have hkPos : (0 : ℝ) < k := by exact_mod_cast hm.trans hkData.1
      have hksPos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hratioPos : 0 < ((k + 1 : ℕ) : ℝ) / (k : ℝ) := div_pos hksPos hkPos
      have hlog := Real.one_sub_inv_le_log_of_pos hratioPos
      rw [Real.log_div hksPos.ne' hkPos.ne'] at hlog
      have hinv : ((((k + 1 : ℕ) : ℝ) / (k : ℝ))⁻¹) =
          (k : ℝ) / (k + 1 : ℕ) := by field_simp
      rw [hinv] at hlog
      have hid : (((k + 1 : ℕ) : ℝ))⁻¹ =
          1 - (k : ℝ) / (k + 1 : ℕ) := by
        push_cast
        field_simp
        ring
      rw [hid]
      exact hlog
    _ = Real.log U - Real.log m := Finset.sum_Ico_sub (fun k : ℕ ↦ Real.log k) hmU
    _ = Real.log ((U : ℝ) / (m : ℝ)) := by
      rw [Real.log_div
        (by exact_mod_cast (show U ≠ 0 by omega))
        (by exact_mod_cast (show m ≠ 0 by omega))]

lemma sum_Ioc_inv_eq_sum_Ico_inv_succ (a N : ℕ) :
    (∑ n ∈ Finset.Ioc a N, (n : ℝ)⁻¹) =
      ∑ k ∈ Finset.Ico a N, (((k + 1 : ℕ) : ℝ))⁻¹ := by
  apply Finset.sum_bij (fun n _ ↦ n - 1)
  · intro n hn
    simp only [Finset.mem_Ioc, Finset.mem_Ico] at hn ⊢
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Ioc] at hn₁ hn₂
    omega
  · intro k hk
    refine ⟨k + 1, ?_, ?_⟩
    · simp only [Finset.mem_Ioc, Finset.mem_Ico] at hk ⊢
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [Nat.sub_add_cancel (by omega)]

lemma sum_Ioc_inv_le_log_ratio {m U : ℕ} (hm : 1 ≤ m) (hmU : m ≤ U) :
    (∑ n ∈ Finset.Ioc m U, (n : ℝ)⁻¹) ≤
      Real.log ((U : ℝ) / (m : ℝ)) := by
  rw [sum_Ioc_inv_eq_sum_Ico_inv_succ]
  exact sum_Ico_inv_succ_le_log_ratio hm hmU

lemma log_threshold_square_div (n : ℕ) :
    Real.log (((threshold (n + 1) ^ 2 : ℕ) : ℝ) / threshold n) =
      ((2 * scale (n + 1) : ℕ) - scale n) * Real.log 2 := by
  have hscale : scale n ≤ 2 * scale (n + 1) := by
    exact (scale_strictMono.monotone (Nat.le_add_right n 1)).trans
      (Nat.le_mul_of_pos_left _ (by norm_num))
  have hnum : ((((threshold (n + 1) ^ 2 : ℕ) : ℝ)) ≠ 0) := by
    have hp : 0 < threshold (n + 1) ^ 2 := Nat.pow_pos (threshold_pos (n + 1))
    exact_mod_cast hp.ne'
  have hden : (((threshold n : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (threshold_pos n).ne'
  rw [Real.log_div hnum hden]
  simp only [threshold, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  push_cast [Nat.cast_sub hscale]
  ring

def b : ℝ := 2 + Real.sqrt 3
def d : ℝ := 2 - Real.sqrt 3
def sharp : ℝ := (2 + Real.sqrt 3) / 4

lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num

lemma sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

lemma b_pos : 0 < b := by unfold b; positivity
lemma two_lt_b : 2 < b := by unfold b; linarith [sqrt_three_pos]
lemma one_lt_b : 1 < b := lt_trans one_lt_two two_lt_b

lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]

lemma d_pos : 0 < d := by unfold d; linarith [sqrt_three_lt_two]
lemma d_lt_one : d < 1 := by
  unfold d
  have hsqrt_gt_one : 1 < Real.sqrt 3 := by nlinarith [sqrt_three_sq, sqrt_three_pos]
  linarith

lemma b_sq : b ^ 2 = 4 * b - 1 := by
  unfold b
  nlinarith [sqrt_three_sq]

lemma b_mul_conj : b * d = 1 := by
  unfold b d
  nlinarith [sqrt_three_sq]

lemma conj_eq_inv_b : d = b⁻¹ := by
  field_simp [b_pos.ne']
  simpa [mul_comm] using b_mul_conj

lemma sharp_eq_b_div_four : sharp = b / 4 := rfl

lemma one_sub_inv_four_b : 1 - 1 / (4 * b) = sharp := by
  rw [sharp_eq_b_div_four]
  field_simp [b_pos.ne']
  nlinarith [b_sq]

lemma pellPair_plus_closed (n : ℕ) :
    ((pellPair n).1 : ℝ) + Real.sqrt 3 * (pellPair n).2 = b ^ (n + 1) := by
  induction n with
  | zero => simp [b]
  | succ n ih =>
      rw [pellPair_succ]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [pow_succ']
      rw [← ih]
      unfold b
      nlinarith [sqrt_three_sq]

lemma pellPair_minus_closed (n : ℕ) :
    ((pellPair n).1 : ℝ) - Real.sqrt 3 * (pellPair n).2 =
      d ^ (n + 1) := by
  induction n with
  | zero =>
      simp [d]
  | succ n ih =>
      rw [pellPair_succ]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [pow_succ' d, ← ih]
      unfold d
      nlinarith [sqrt_three_sq]

lemma scale_cast_formula (n : ℕ) :
    2 * Real.sqrt 3 * (scale n : ℝ) =
      b ^ (n + 1) - (2 - Real.sqrt 3) ^ (n + 1) := by
  have hp := pellPair_plus_closed n
  have hm := pellPair_minus_closed n
  unfold scale
  simp only [d] at hm
  linarith

lemma scale_cast_formula' (n : ℕ) :
    (scale n : ℝ) = (b ^ (n + 1) - d ^ (n + 1)) / (2 * Real.sqrt 3) := by
  have h := scale_cast_formula n
  rw [eq_div_iff (mul_ne_zero (by norm_num) sqrt_three_pos.ne')]
  simpa [d, mul_comm] using h

lemma abs_d_div_b_lt_one : |d / b| < 1 := by
  rw [abs_of_pos (div_pos d_pos b_pos), div_lt_one b_pos]
  unfold d b
  linarith [sqrt_three_pos]

lemma scale_ratio_formula (n : ℕ) :
    (scale n : ℝ) / scale (n + 1) =
      (1 - (d / b) ^ (n + 1)) / (b - d * (d / b) ^ (n + 1)) := by
  have hrpos : 0 < d / b := div_pos d_pos b_pos
  have hrlt : d / b < 1 := (div_lt_one b_pos).2 (by
    unfold d b
    linarith [sqrt_three_pos])
  have hrpow : (d / b) ^ (n + 1) < 1 :=
    pow_lt_one₀ hrpos.le hrlt (by omega)
  have hright : b - d * (d / b) ^ (n + 1) ≠ 0 := by
    have : d * (d / b) ^ (n + 1) < b := by
      calc
        d * (d / b) ^ (n + 1) < d * 1 := mul_lt_mul_of_pos_left hrpow d_pos
        _ < b := by unfold d b; linarith [sqrt_three_pos]
    linarith
  have hleft : (scale (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (scale_pos (n + 1)).ne'
  have hnum : b ^ (n + 1) - d ^ (n + 1) =
      b ^ (n + 1) * (1 - (d / b) ^ (n + 1)) := by
    rw [div_pow]
    field_simp [b_pos.ne']
  have hden : b ^ (n + 1 + 1) - d ^ (n + 1 + 1) =
      b ^ (n + 1) * (b - d * (d / b) ^ (n + 1)) := by
    rw [div_pow]
    field_simp [b_pos.ne']
    ring
  apply (div_eq_div_iff hleft hright).2
  rw [scale_cast_formula', scale_cast_formula']
  rw [hnum, hden]
  field_simp [b_pos.ne', sqrt_three_pos.ne', hright]

lemma tendsto_scale_ratio :
    Tendsto (fun n : ℕ ↦ (scale n : ℝ) / scale (n + 1)) atTop (nhds b⁻¹) := by
  have hpow₀ : Tendsto (fun n : ℕ ↦ (d / b) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one abs_d_div_b_lt_one
  have hpow : Tendsto (fun n : ℕ ↦ (d / b) ^ (n + 1)) atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).2 hpow₀
  rw [show b⁻¹ = (1 - 0) / (b - d * 0) by simp]
  rw [funext scale_ratio_formula]
  exact (tendsto_const_nhds.sub hpow).div
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow)) (by simpa using b_pos.ne')

lemma endpoint_ratio_identity (i j : ℕ) :
    (((scale (i + 2 * j + 2) : ℝ) - scale i) /
        (4 * scale (i + 2 * j + 1) : ℝ)) =
      1 - ((scale (i + 2 * j) : ℝ) + scale i) /
        (4 * scale (i + 2 * j + 1) : ℝ) := by
  have hrec := scale_add_two (i + 2 * j)
  have hden : (scale (i + 2 * j + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (scale_pos (i + 2 * j + 1)).ne'
  have hrecR :
      (scale (i + 2 * j + 2) : ℝ) + scale (i + 2 * j) =
        4 * scale (i + 2 * j + 1) := by exact_mod_cast hrec
  rw [div_eq_iff (mul_ne_zero (by norm_num) hden)]
  field_simp [hden]
  nlinarith [hrecR]

lemma tendsto_endpoint_ratio (i : ℕ) :
    Tendsto
      (fun j : ℕ ↦ ((scale (i + 2 * j + 2) : ℝ) - scale i) /
        (4 * scale (i + 2 * j + 1) : ℝ))
      atTop (nhds sharp) := by
  let k : ℕ → ℕ := fun j ↦ i + 2 * j
  have hk : Tendsto k atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro N
    refine ⟨N, fun j hj ↦ ?_⟩
    dsimp [k]
    omega
  have hratio : Tendsto
      (fun j ↦ (scale (k j) : ℝ) / scale (k j + 1)) atTop (nhds b⁻¹) :=
    tendsto_scale_ratio.comp hk
  have hdenNat : Tendsto (fun j ↦ scale (k j + 1)) atTop atTop :=
    scale_strictMono.tendsto_atTop.comp ((tendsto_add_atTop_nat 1).comp hk)
  have hdenReal : Tendsto (fun j ↦ (scale (k j + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hdenNat
  have hsmall : Tendsto
      (fun j ↦ (scale i : ℝ) / scale (k j + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hdenReal
  have hlim : Tendsto
      (fun j ↦ 1 - (1 / 4 : ℝ) *
        ((scale (k j) : ℝ) / scale (k j + 1) +
          (scale i : ℝ) / scale (k j + 1)))
      atTop (nhds (1 - (1 / 4 : ℝ) * (b⁻¹ + 0))) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul (hratio.add hsmall))
  convert hlim using 1
  · apply funext
    intro j
    rw [endpoint_ratio_identity i j]
    dsimp [k]
    have hne : (scale (i + 2 * j + 1) : ℝ) ≠ 0 := by
      exact_mod_cast (scale_pos (i + 2 * j + 1)).ne'
    field_simp
  · congr 1
    rw [← one_sub_inv_four_b]
    field_simp [b_pos.ne']
    ring

def logWindowWidth (i j : ℕ) : ℤ :=
  2 * (scale (i + 2 * j + 1) : ℤ) - scale (i + 2 * j)

lemma twice_logWindowWidth (i j : ℕ) :
    2 * logWindowWidth i j =
      (scale (i + 2 * j + 2) : ℤ) - scale (i + 2 * j) := by
  have hrec := scale_add_two (i + 2 * j)
  simp only [logWindowWidth]
  omega

lemma logWindowWidth_telescope (i K : ℕ) :
    2 * (∑ j ∈ Finset.range (K + 1), logWindowWidth i j) =
      (scale (i + 2 * K + 2) : ℤ) - scale i := by
  induction K with
  | zero =>
      simpa using twice_logWindowWidth i 0
  | succ K ih =>
      rw [Finset.sum_range_succ, mul_add, ih, twice_logWindowWidth]
      have hk : i + 2 * (K + 1) = i + 2 * K + 2 := by omega
      rw [hk]
      ring

def natLogWindowWidth (i j : ℕ) : ℕ :=
  2 * scale (i + 2 * j + 1) - scale (i + 2 * j)

lemma twice_natLogWindowWidth (i j : ℕ) :
    2 * natLogWindowWidth i j =
      scale (i + 2 * j + 2) - scale (i + 2 * j) := by
  have hrec := scale_add_two (i + 2 * j)
  have hle : scale (i + 2 * j) ≤ 2 * scale (i + 2 * j + 1) :=
    (scale_strictMono.monotone (Nat.le_add_right _ 1)).trans
      (Nat.le_mul_of_pos_left _ (by norm_num))
  simp only [natLogWindowWidth]
  omega

lemma natLogWindowWidth_prefix_telescope (i K : ℕ) :
    2 * (∑ j ∈ Finset.range K, natLogWindowWidth i j) =
      scale (i + 2 * K) - scale i := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, mul_add, ih, twice_natLogWindowWidth]
      have hiK : i ≤ i + 2 * K := Nat.le_add_right _ _
      have hscale : scale i ≤ scale (i + 2 * K) :=
        scale_strictMono.monotone hiK
      have hscaleNext : scale (i + 2 * K) ≤ scale (i + 2 * K + 2) :=
        scale_strictMono.monotone (by omega)
      have hid := Nat.sub_add_sub_cancel hscaleNext hscale
      have hk : i + 2 * (K + 1) = i + 2 * K + 2 := by omega
      rw [hk]
      simpa only [add_comm] using hid

def endpointRatio (i K : ℕ) : ℝ :=
  ((scale (i + 2 * K + 2) : ℝ) - scale i) /
    (4 * scale (i + 2 * K + 1) : ℝ)

lemma endpointRatio_tendsto (i : ℕ) :
    Tendsto (endpointRatio i) atTop (nhds sharp) := by
  change Tendsto
    (fun j : ℕ ↦ ((scale (i + 2 * j + 2) : ℝ) - scale i) /
      (4 * scale (i + 2 * j + 1) : ℝ)) atTop (nhds sharp)
  exact tendsto_endpoint_ratio i

lemma ideal_inside_window_bound (i K : ℕ) {t : ℝ}
    (hlower : (scale (i + 2 * K) : ℝ) ≤ t)
    (hupper : t ≤ 2 * scale (i + 2 * K + 1)) :
    ((scale (i + 2 * K) : ℝ) - scale i) / 2 +
        (t - scale (i + 2 * K)) ≤ endpointRatio i K * t := by
  have hrecNat := scale_add_two (i + 2 * K)
  have hrec :
      (scale (i + 2 * K + 2) : ℝ) + scale (i + 2 * K) =
        4 * scale (i + 2 * K + 1) := by exact_mod_cast hrecNat
  have hscalePos : (0 : ℝ) < scale (i + 2 * K + 1) := by
    exact_mod_cast scale_pos (i + 2 * K + 1)
  have hden : (0 : ℝ) < 4 * scale (i + 2 * K + 1) := by positivity
  rw [endpointRatio, div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [show (0 : ℝ) ≤ (scale i : ℕ) by positivity]

lemma ideal_after_window_bound (i K : ℕ) {t : ℝ}
    (hlower : (2 * scale (i + 2 * K + 1) : ℕ) ≤ t) :
    ((scale (i + 2 * K + 2) : ℝ) - scale i) / 2 ≤
      endpointRatio i K * t := by
  have hnum : (0 : ℝ) ≤ (scale (i + 2 * K + 2) : ℝ) - scale i := by
    exact sub_nonneg.mpr (by
      exact_mod_cast scale_strictMono.monotone (by omega : i ≤ i + 2 * K + 2))
  have hscalePos : (0 : ℝ) < scale (i + 2 * K + 1) := by
    exact_mod_cast scale_pos (i + 2 * K + 1)
  have hden : (0 : ℝ) < 4 * scale (i + 2 * K + 1) := by positivity
  have hhalf : (4 * scale (i + 2 * K + 1) : ℝ) / 2 ≤ t := by
    have hlowerR : (2 * scale (i + 2 * K + 1) : ℝ) ≤ t := by
      exact_mod_cast hlower
    nlinarith
  rw [endpointRatio, div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_left hhalf hnum]

/-! ### The extremal colouring and its subset-sum cover -/

def pellColor (n : ℕ) : Fin 2 :=
  if n ≤ 2 then 0
  else ⟨closedBlockIndex n % 2, Nat.mod_lt _ (by norm_num)⟩

def colorClass (i : Fin 2) : Set ℕ := {n | pellColor n = i}

def window (i : Fin 2) (j : ℕ) : Finset ℕ :=
  Finset.Ioc (threshold (i.val + 2 * j))
    (threshold (i.val + 2 * j + 1) ^ 2)

def windowCover (i : Fin 2) : Set ℕ :=
  {n | n ≤ 3} ∪ {n | ∃ j : ℕ, n ∈ window i j}

lemma pellColor_of_three_le {n : ℕ} (hn : 3 ≤ n) :
    pellColor n =
      ⟨closedBlockIndex n % 2, Nat.mod_lt _ (by norm_num)⟩ := by
  rw [pellColor, if_neg (by omega)]

lemma exists_large_mem_of_three_lt_sum {F : Finset ℕ}
    (hF : 3 < ∑ x ∈ F, x) : ∃ m ∈ F, 3 ≤ m := by
  by_contra hnot
  push Not at hnot
  have hsub : F ⊆ Finset.range 3 := by
    intro x hx
    exact Finset.mem_range.mpr (hnot x hx)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun x hxF hx ↦ Nat.zero_le x)
  norm_num at hsum
  omega

lemma sum_le_max_square {F : Finset ℕ} {m : ℕ}
    (hmax : ∀ x ∈ F, x ≤ m) {T : ℕ} (hmT : m ≤ T) :
    ∑ x ∈ F, x ≤ T ^ 2 := by
  have hsumErase : ∑ x ∈ F.erase 0, x = ∑ x ∈ F, x := by
    by_cases h0 : 0 ∈ F
    · have h := Finset.sum_erase_add F (fun x : ℕ ↦ x) h0
      simpa using h
    · rw [Finset.erase_eq_self.mpr h0]
  rw [← hsumErase]
  apply finset_sum_le_sq_of_pos_le
  intro x hx
  have hxF := Finset.mem_of_mem_erase hx
  have hx0 := (Finset.mem_erase.mp hx).1
  exact ⟨Nat.pos_of_ne_zero hx0, (hmax x hxF).trans hmT⟩

lemma finite_monochromatic_sum_mem_windowCover (i : Fin 2) {F : Finset ℕ}
    (hmono : ∀ x ∈ F, pellColor x = i) :
    (∑ x ∈ F, x) ∈ windowCover i := by
  let s := ∑ x ∈ F, x
  by_cases hs : s ≤ 3
  · exact Or.inl hs
  have hs3 : 3 < s := lt_of_not_ge hs
  obtain ⟨m, hmF, hm3⟩ := exists_large_mem_of_three_lt_sum hs3
  have hFne : F.Nonempty := ⟨m, hmF⟩
  let M := F.max' hFne
  have hMF : M ∈ F := Finset.max'_mem F hFne
  have hmM : m ≤ M := Finset.le_max' F m hmF
  have hM3 : 3 ≤ M := hm3.trans hmM
  have hmax : ∀ x ∈ F, x ≤ M := fun x hx ↦ Finset.le_max' F x hx
  let k := closedBlockIndex M
  have hMk : threshold k < M := by
    dsimp only [k]
    exact threshold_closedBlockIndex_lt hM3
  have hMk' : M ≤ threshold (k + 1) := by
    dsimp only [k]
    exact le_threshold_succ_closedBlockIndex M
  have hcolorM := hmono M hMF
  have hpar : k % 2 = i.val := by
    rw [pellColor_of_three_le hM3] at hcolorM
    exact congrArg Fin.val hcolorM
  let j := k / 2
  have hk : k = i.val + 2 * j := by
    have hmod := Nat.mod_add_div k 2
    dsimp only [j]
    omega
  have hsumLower : threshold k < s := by
    have hMsum : M ≤ s :=
      Finset.single_le_sum (f := fun x : ℕ ↦ x) (fun _ _ ↦ Nat.zero_le _) hMF
    exact hMk.trans_le hMsum
  have hsumUpper : s ≤ threshold (k + 1) ^ 2 := by
    exact sum_le_max_square hmax hMk'
  apply Or.inr
  refine ⟨j, ?_⟩
  rw [window, ← hk]
  exact Finset.mem_Ioc.mpr ⟨hsumLower, hsumUpper⟩

def monochromaticSubsetSums (i : Fin 2) : Set ℕ :=
  {s : ℕ | ∃ F : Finset ℕ, (∀ x ∈ F, x ∈ colorClass i) ∧
    s = ∑ x ∈ F, x}

lemma monochromaticSubsetSums_subset_windowCover (i : Fin 2) :
    monochromaticSubsetSums i ⊆ windowCover i := by
  rintro s ⟨F, hF, rfl⟩
  exact finite_monochromatic_sum_mem_windowCover i (fun x hx ↦ hF x hx)

/-! ### Harmonic mass of the covering windows -/

def fullWindows (i : Fin 2) (K : ℕ) : Finset ℕ :=
  (Finset.range K).biUnion (window i)

def currentWindowBelow (i : Fin 2) (K N : ℕ) : Finset ℕ :=
  window i K ∩ Finset.Ico 1 N

def smallPositive : Finset ℕ := Finset.Icc 1 3

def smallMass : ℝ := ∑ n ∈ smallPositive, (n : ℝ)⁻¹

lemma pairwiseDisjoint_windows (i : Fin 2) (K : ℕ) :
    (↑(Finset.range K) : Set ℕ).PairwiseDisjoint (window i) := by
  intro a ha b hb hab
  change Disjoint (window i a) (window i b)
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have hxa' := Finset.mem_Ioc.mp hxa
  have hxb' := Finset.mem_Ioc.mp hxb
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · have hend : threshold (i.val + 2 * a + 1) ^ 2 ≤
        threshold (i.val + 2 * b) := by
      calc
        threshold (i.val + 2 * a + 1) ^ 2 ≤
            threshold (i.val + 2 * a + 2) :=
          threshold_square_le_next_same_color (i.val + 2 * a)
        _ ≤ threshold (i.val + 2 * b) :=
          threshold_strictMono.monotone (by omega)
    omega
  · have hend : threshold (i.val + 2 * b + 1) ^ 2 ≤
        threshold (i.val + 2 * a) := by
      calc
        threshold (i.val + 2 * b + 1) ^ 2 ≤
            threshold (i.val + 2 * b + 2) :=
          threshold_square_le_next_same_color (i.val + 2 * b)
        _ ≤ threshold (i.val + 2 * a) :=
          threshold_strictMono.monotone (by omega)
    omega

lemma sum_window_le (i : Fin 2) (j : ℕ) :
    (∑ n ∈ window i j, (n : ℝ)⁻¹) ≤
      (natLogWindowWidth i.val j : ℝ) * Real.log 2 := by
  let k := i.val + 2 * j
  have hm : 1 ≤ threshold k := (threshold_pos k)
  have hmU : threshold k ≤ threshold (k + 1) ^ 2 := by
    have hmono : threshold k ≤ threshold (k + 1) :=
      threshold_strictMono.monotone (Nat.le_add_right k 1)
    exact hmono.trans (Nat.le_pow (a := threshold (k + 1)) (by norm_num : 0 < 2))
  have h := sum_Ioc_inv_le_log_ratio hm hmU
  rw [log_threshold_square_div k] at h
  have hscale : scale k ≤ 2 * scale (k + 1) := by
    exact (scale_strictMono.monotone (Nat.le_add_right k 1)).trans
      (Nat.le_mul_of_pos_left _ (by norm_num))
  rw [natLogWindowWidth, Nat.cast_sub (by simpa [k] using hscale)]
  simpa only [window, k] using h

lemma sum_fullWindows (i : Fin 2) (K : ℕ) :
    ∑ n ∈ fullWindows i K, (n : ℝ)⁻¹ =
      ∑ j ∈ Finset.range K, ∑ n ∈ window i j, (n : ℝ)⁻¹ := by
  exact Finset.sum_biUnion (pairwiseDisjoint_windows i K)

lemma sum_fullWindows_le (i : Fin 2) (K : ℕ) :
    (∑ n ∈ fullWindows i K, (n : ℝ)⁻¹) ≤
      ((scale (i.val + 2 * K) : ℝ) - scale i.val) / 2 * Real.log 2 := by
  rw [sum_fullWindows]
  have hsum :
      (∑ j ∈ Finset.range K, ∑ n ∈ window i j, (n : ℝ)⁻¹) ≤
        ∑ j ∈ Finset.range K,
          (natLogWindowWidth i.val j : ℝ) * Real.log 2 := by
    apply Finset.sum_le_sum
    intro j hj
    exact sum_window_le i j
  have hscale : scale i.val ≤ scale (i.val + 2 * K) :=
    scale_strictMono.monotone (Nat.le_add_right _ _)
  have htelNat := natLogWindowWidth_prefix_telescope i.val K
  have htel :
      2 * (∑ j ∈ Finset.range K, (natLogWindowWidth i.val j : ℝ)) =
        (scale (i.val + 2 * K) : ℝ) - scale i.val := by
    exact_mod_cast htelNat
  calc
    (∑ j ∈ Finset.range K, ∑ n ∈ window i j, (n : ℝ)⁻¹) ≤
        ∑ j ∈ Finset.range K,
          (natLogWindowWidth i.val j : ℝ) * Real.log 2 := hsum
    _ = (∑ j ∈ Finset.range K, (natLogWindowWidth i.val j : ℝ)) *
          Real.log 2 := by rw [Finset.sum_mul]
    _ = ((scale (i.val + 2 * K) : ℝ) - scale i.val) / 2 *
          Real.log 2 := by rw [← htel]; ring

lemma sum_currentWindowBelow_le_log {i : Fin 2} {K N : ℕ}
    (hlower : threshold (i.val + 2 * K) < N) :
    (∑ n ∈ currentWindowBelow i K N, (n : ℝ)⁻¹) ≤
      Real.log (N : ℝ) - (scale (i.val + 2 * K) : ℝ) * Real.log 2 := by
  let m := threshold (i.val + 2 * K)
  have hm : 1 ≤ m := threshold_pos _
  have hmN : m ≤ N := hlower.le
  have hsub : currentWindowBelow i K N ⊆ Finset.Ioc m N := by
    intro x hx
    have hxw := Finset.mem_Ioc.mp (Finset.mem_inter.mp hx).1
    have hxN := Finset.mem_Ico.mp (Finset.mem_inter.mp hx).2
    exact Finset.mem_Ioc.mpr ⟨hxw.1, hxN.2.le⟩
  have hsumSub :
      (∑ n ∈ currentWindowBelow i K N, (n : ℝ)⁻¹) ≤
        ∑ n ∈ Finset.Ioc m N, (n : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn hnnot
    positivity
  have hlog := sum_Ioc_inv_le_log_ratio hm hmN
  calc
    (∑ n ∈ currentWindowBelow i K N, (n : ℝ)⁻¹) ≤
        ∑ n ∈ Finset.Ioc m N, (n : ℝ)⁻¹ := hsumSub
    _ ≤ Real.log ((N : ℝ) / m) := hlog
    _ = Real.log (N : ℝ) - (scale (i.val + 2 * K) : ℝ) * Real.log 2 := by
      rw [Real.log_div (by exact_mod_cast (show N ≠ 0 by omega))
        (by exact_mod_cast (show m ≠ 0 by omega))]
      simp only [m, threshold, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]

lemma sum_currentWindowBelow_le_full (i : Fin 2) (K N : ℕ) :
    (∑ n ∈ currentWindowBelow i K N, (n : ℝ)⁻¹) ≤
      (natLogWindowWidth i.val K : ℝ) * Real.log 2 := by
  have hsub : currentWindowBelow i K N ⊆ window i K := Finset.inter_subset_left
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n hn hnnot ↦ by positivity)).trans (sum_window_le i K)

/-! ### Locating an arbitrary cutoff among the same-colour windows -/

lemma exists_sameWindow_bound (i : Fin 2) (N : ℕ) :
    ∃ K : ℕ, N ≤ threshold (i.val + 2 * K + 2) := by
  obtain ⟨k, hk⟩ := exists_le_threshold N
  refine ⟨k, hk.trans ?_⟩
  exact threshold_strictMono.monotone (by omega)

noncomputable def sameWindowIndex (i : Fin 2) (N : ℕ) : ℕ :=
  Nat.find (exists_sameWindow_bound i N)

lemma le_threshold_sameWindowIndex (i : Fin 2) (N : ℕ) :
    N ≤ threshold (i.val + 2 * sameWindowIndex i N + 2) :=
  Nat.find_spec (exists_sameWindow_bound i N)

lemma threshold_sameWindowIndex_lt {i : Fin 2} {N : ℕ}
    (hK : 0 < sameWindowIndex i N) :
    threshold (i.val + 2 * sameWindowIndex i N) < N := by
  let K := sameWindowIndex i N
  have hpred : K - 1 < K := Nat.sub_one_lt (Nat.ne_of_gt hK)
  have hmin := Nat.find_min (exists_sameWindow_bound i N) hpred
  have hKform : i.val + 2 * (K - 1) + 2 = i.val + 2 * K := by omega
  rw [hKform] at hmin
  exact lt_of_not_ge hmin

lemma sameWindowIndex_tendsto (i : Fin 2) :
    Tendsto (sameWindowIndex i) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro K₀
  refine ⟨threshold (i.val + 2 * K₀ + 2) + 1, fun N hN ↦ ?_⟩
  by_contra hnot
  have hKle : sameWindowIndex i N ≤ K₀ := Nat.le_of_not_ge hnot
  have hbound := le_threshold_sameWindowIndex i N
  have hmono : threshold (i.val + 2 * sameWindowIndex i N + 2) ≤
      threshold (i.val + 2 * K₀ + 2) :=
    threshold_strictMono.monotone (by omega)
  omega

def coverBelow (i : Fin 2) (N : ℕ) : Finset ℕ :=
  (Finset.Ico 1 N).filter fun n ↦ n ∈ windowCover i

lemma coverBelow_subset_components (i : Fin 2) (N : ℕ) :
    coverBelow i N ⊆
      smallPositive ∪
        (fullWindows i (sameWindowIndex i N) ∪
          currentWindowBelow i (sameWindowIndex i N) N) := by
  intro x hx
  have hxData := Finset.mem_filter.mp hx
  have hxCut := Finset.mem_Ico.mp hxData.1
  rcases hxData.2 with hxsmall | ⟨j, hxwindow⟩
  · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hxCut.1, hxsmall⟩)
  · apply Finset.mem_union_right
    let K := sameWindowIndex i N
    have hjK : j ≤ K := by
      by_contra hnot
      have hKj : K < j := Nat.lt_of_not_ge hnot
      have hbound := le_threshold_sameWindowIndex i N
      change N ≤ threshold (i.val + 2 * K + 2) at hbound
      have hmono : threshold (i.val + 2 * K + 2) ≤
          threshold (i.val + 2 * j) :=
        threshold_strictMono.monotone (by omega)
      have hxlower := (Finset.mem_Ioc.mp hxwindow).1
      omega
    rcases lt_or_eq_of_le hjK with hjKlt | rfl
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_range.mpr hjKlt, hxwindow⟩
    · apply Finset.mem_union_right
      exact Finset.mem_inter.mpr ⟨hxwindow, hxData.1⟩

lemma sum_union_le_add {A B : Finset ℕ} :
    (∑ n ∈ A ∪ B, (n : ℝ)⁻¹) ≤
      (∑ n ∈ A, (n : ℝ)⁻¹) + ∑ n ∈ B, (n : ℝ)⁻¹ := by
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B)
    (f := fun n : ℕ ↦ (n : ℝ)⁻¹)
  have hinter : 0 ≤ ∑ n ∈ A ∩ B, (n : ℝ)⁻¹ := by positivity
  linarith

lemma harmonic_windowCover_le_components (i : Fin 2) (N : ℕ) :
    Erdos1211DensityNat.harmonicPrefix (windowCover i) N ≤
      smallMass +
        (∑ n ∈ fullWindows i (sameWindowIndex i N), (n : ℝ)⁻¹) +
        ∑ n ∈ currentWindowBelow i (sameWindowIndex i N) N, (n : ℝ)⁻¹ := by
  rw [Erdos1211DensityNat.harmonicPrefix_eq_sum_filter]
  rw [show (Finset.Ico 1 N).filter (fun n ↦ n ∈ windowCover i) =
      coverBelow i N by rfl]
  have hsub :
      (∑ n ∈ coverBelow i N, (n : ℝ)⁻¹) ≤
        ∑ n ∈ smallPositive ∪
          (fullWindows i (sameWindowIndex i N) ∪
            currentWindowBelow i (sameWindowIndex i N) N), (n : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (coverBelow_subset_components i N)
    intro n hn hnnot
    positivity
  calc
    (∑ n ∈ coverBelow i N, (n : ℝ)⁻¹) ≤
        ∑ n ∈ smallPositive ∪
          (fullWindows i (sameWindowIndex i N) ∪
            currentWindowBelow i (sameWindowIndex i N) N), (n : ℝ)⁻¹ := hsub
    _ ≤ (∑ n ∈ smallPositive, (n : ℝ)⁻¹) +
          ∑ n ∈ fullWindows i (sameWindowIndex i N) ∪
            currentWindowBelow i (sameWindowIndex i N) N, (n : ℝ)⁻¹ :=
      sum_union_le_add
    _ ≤ smallMass +
          (∑ n ∈ fullWindows i (sameWindowIndex i N), (n : ℝ)⁻¹) +
          ∑ n ∈ currentWindowBelow i (sameWindowIndex i N) N, (n : ℝ)⁻¹ := by
      unfold smallMass
      linarith [sum_union_le_add
        (A := fullWindows i (sameWindowIndex i N))
        (B := currentWindowBelow i (sameWindowIndex i N) N)]

lemma log_threshold (n : ℕ) :
    Real.log (threshold n : ℝ) = (scale n : ℝ) * Real.log 2 := by
  simp only [threshold, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]

lemma log_threshold_square (n : ℕ) :
    Real.log ((threshold n ^ 2 : ℕ) : ℝ) =
      2 * (scale n : ℝ) * Real.log 2 := by
  rw [Nat.cast_pow, Real.log_pow, log_threshold]
  ring

def upperEnvelope (i : Fin 2) (N : ℕ) : ℝ :=
  endpointRatio i.val (sameWindowIndex i N) +
    smallMass / Real.log (N : ℝ)

lemma logRatio_windowCover_le_upperEnvelope (i : Fin 2) {N : ℕ}
    (hN : 2 ≤ N) (hK : 0 < sameWindowIndex i N) :
    Erdos1211DensityNat.logRatio (windowCover i) N ≤ upperEnvelope i N := by
  let K := sameWindowIndex i N
  let k := i.val + 2 * K
  let t := Real.log (N : ℝ) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hNR : (1 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hlowerNat : threshold k < N := by
    dsimp only [k, K]
    exact threshold_sameWindowIndex_lt hK
  have hlowerLog : Real.log (threshold k : ℝ) < Real.log (N : ℝ) := by
    apply Real.strictMonoOn_log
    · change (0 : ℝ) < threshold k
      exact_mod_cast threshold_pos k
    · change (0 : ℝ) < N
      exact_mod_cast Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.one_lt_two hN)
    · exact_mod_cast hlowerNat
  have hlowerT : (scale k : ℝ) ≤ t := by
    rw [log_threshold] at hlowerLog
    dsimp only [t]
    apply (le_div_iff₀ hlog2).2
    exact hlowerLog.le
  have hcomponents := harmonic_windowCover_le_components i N
  have hprev := sum_fullWindows_le i K
  by_cases hinside : N ≤ threshold (k + 1) ^ 2
  · have hcurr := sum_currentWindowBelow_le_log
      (i := i) (K := K) (N := N) hlowerNat
    have hupperLog : Real.log (N : ℝ) ≤
        Real.log ((threshold (k + 1) ^ 2 : ℕ) : ℝ) := by
      apply Real.strictMonoOn_log.monotoneOn
      · change (0 : ℝ) < N
        exact_mod_cast Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.one_lt_two hN)
      · change (0 : ℝ) < ((threshold (k + 1) ^ 2 : ℕ) : ℝ)
        exact_mod_cast Nat.pow_pos (threshold_pos (k + 1))
      · exact_mod_cast hinside
    have hupperT : t ≤ 2 * scale (k + 1) := by
      rw [log_threshold_square] at hupperLog
      dsimp only [t]
      apply (div_le_iff₀ hlog2).2
      nlinarith
    have hideal := ideal_inside_window_bound i.val K
      (t := t) (by simpa only [k] using hlowerT)
      (by simpa only [k] using hupperT)
    have htlog : t * Real.log 2 = Real.log (N : ℝ) := by
      dsimp only [t]
      field_simp
    have hmain :
        ((scale k : ℝ) - scale i.val) / 2 * Real.log 2 +
            (Real.log (N : ℝ) - (scale k : ℝ) * Real.log 2) ≤
          endpointRatio i.val K * Real.log (N : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hideal hlog2.le
      have hmul' :
          (((scale k : ℝ) - scale i.val) / 2 + (t - scale k)) * Real.log 2 ≤
            endpointRatio i.val K * t * Real.log 2 := by
        simpa only [k] using hmul
      calc
        ((scale k : ℝ) - scale i.val) / 2 * Real.log 2 +
              (Real.log (N : ℝ) - (scale k : ℝ) * Real.log 2) =
            (((scale k : ℝ) - scale i.val) / 2 + (t - scale k)) *
              Real.log 2 := by rw [← htlog]; ring
        _ ≤ endpointRatio i.val K * t * Real.log 2 := hmul'
        _ = endpointRatio i.val K * Real.log (N : ℝ) := by
          rw [mul_assoc, htlog]
    have hmass : Erdos1211DensityNat.harmonicPrefix (windowCover i) N ≤
        smallMass + endpointRatio i.val K * Real.log (N : ℝ) := by
      dsimp only [K] at hcomponents hprev hcurr ⊢
      dsimp only [k] at hmain
      linarith
    rw [Erdos1211DensityNat.logRatio, upperEnvelope]
    apply (div_le_iff₀ hlogN).2
    field_simp
    linarith
  · have hafterNat : threshold (k + 1) ^ 2 < N := Nat.lt_of_not_ge hinside
    have hafterLog : Real.log ((threshold (k + 1) ^ 2 : ℕ) : ℝ) <
        Real.log (N : ℝ) := by
      apply Real.strictMonoOn_log
      · change (0 : ℝ) < ((threshold (k + 1) ^ 2 : ℕ) : ℝ)
        exact_mod_cast Nat.pow_pos (threshold_pos (k + 1))
      · change (0 : ℝ) < N
        exact_mod_cast Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.one_lt_two hN)
      · exact_mod_cast hafterNat
    have hafterT : (2 * scale (k + 1) : ℕ) ≤ t := by
      rw [log_threshold_square] at hafterLog
      dsimp only [t]
      have hreal : (2 : ℝ) * scale (k + 1) ≤
          Real.log (N : ℝ) / Real.log 2 := by
        apply (le_div_iff₀ hlog2).2
        nlinarith
      exact_mod_cast hreal
    have hcurr := sum_currentWindowBelow_le_full i K N
    have hideal := ideal_after_window_bound i.val K
      (t := t) (by simpa only [k] using hafterT)
    have htlog : t * Real.log 2 = Real.log (N : ℝ) := by
      dsimp only [t]
      field_simp
    have hwidthCast :
        (natLogWindowWidth i.val K : ℝ) =
          2 * scale (k + 1) - scale k := by
      have hscale : scale k ≤ 2 * scale (k + 1) := by
        exact (scale_strictMono.monotone (Nat.le_add_right k 1)).trans
          (Nat.le_mul_of_pos_left _ (by norm_num))
      rw [natLogWindowWidth, Nat.cast_sub (by simpa only [k] using hscale)]
      push_cast
      simp only [k]
    have hrecNat := scale_add_two k
    have hrec : (scale (k + 2) : ℝ) + scale k = 4 * scale (k + 1) := by
      exact_mod_cast hrecNat
    have hmain :
        ((scale k : ℝ) - scale i.val) / 2 * Real.log 2 +
            (natLogWindowWidth i.val K : ℝ) * Real.log 2 ≤
          endpointRatio i.val K * Real.log (N : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hideal hlog2.le
      have hmul' :
          ((scale (k + 2) : ℝ) - scale i.val) / 2 * Real.log 2 ≤
            endpointRatio i.val K * t * Real.log 2 := by
        simpa only [k] using hmul
      calc
        ((scale k : ℝ) - scale i.val) / 2 * Real.log 2 +
              (natLogWindowWidth i.val K : ℝ) * Real.log 2 =
            ((scale (k + 2) : ℝ) - scale i.val) / 2 * Real.log 2 := by
          rw [hwidthCast]
          nlinarith
        _ ≤ endpointRatio i.val K * t * Real.log 2 := hmul'
        _ = endpointRatio i.val K * Real.log (N : ℝ) := by
          rw [mul_assoc, htlog]
    have hmass : Erdos1211DensityNat.harmonicPrefix (windowCover i) N ≤
        smallMass + endpointRatio i.val K * Real.log (N : ℝ) := by
      dsimp only [K] at hcomponents hprev hcurr ⊢
      dsimp only [k] at hmain
      linarith
    rw [Erdos1211DensityNat.logRatio, upperEnvelope]
    apply (div_le_iff₀ hlogN).2
    field_simp
    linarith

lemma upperEnvelope_tendsto (i : Fin 2) :
    Tendsto (upperEnvelope i) atTop (nhds sharp) := by
  have hmain : Tendsto
      (fun N : ℕ ↦ endpointRatio i.val (sameWindowIndex i N))
      atTop (nhds sharp) :=
    (endpointRatio_tendsto i.val).comp (sameWindowIndex_tendsto i)
  have hsmall : Tendsto
      (fun N : ℕ ↦ smallMass / Real.log (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Erdos1211DensityNat.tendsto_log_nat_atTop
  change Tendsto
    (fun N : ℕ ↦ endpointRatio i.val (sameWindowIndex i N) +
      smallMass / Real.log (N : ℝ)) atTop (nhds sharp)
  simpa only [add_zero] using hmain.add hsmall

theorem upperLogDensity_windowCover_le_sharp (i : Fin 2) :
    Erdos1211DensityNat.upperLogDensity (windowCover i) ≤ sharp := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply Erdos1211DensityNat.upperLogDensity_le_of_eventually_le
  have hN : ∀ᶠ N : ℕ in atTop, 2 ≤ N := Filter.eventually_ge_atTop 2
  have hK : ∀ᶠ N : ℕ in atTop, 0 < sameWindowIndex i N := by
    have hge : ∀ᶠ N : ℕ in atTop, 1 ≤ sameWindowIndex i N :=
      (sameWindowIndex_tendsto i).eventually (Filter.eventually_ge_atTop 1)
    exact hge.mono (fun _ h ↦ Nat.zero_lt_of_lt h)
  have henv : ∀ᶠ N : ℕ in atTop, upperEnvelope i N < sharp + ε :=
    (upperEnvelope_tendsto i).eventually (Iio_mem_nhds (lt_add_of_pos_right sharp hε))
  filter_upwards [hN, hK, henv] with N hN hK henv
  exact (logRatio_windowCover_le_upperEnvelope i hN hK).trans henv.le

theorem upperLogDensity_monochromaticSubsetSums_le_sharp (i : Fin 2) :
    Erdos1211DensityNat.upperLogDensity (monochromaticSubsetSums i) ≤ sharp := by
  exact (Erdos1211DensityNat.upperLogDensity_mono
    (monochromaticSubsetSums_subset_windowCover i)).trans
      (upperLogDensity_windowCover_le_sharp i)

lemma colorClass_disjoint : Disjoint (colorClass 0) (colorClass 1) := by
  rw [Set.disjoint_left]
  intro n hn0 hn1
  exact Fin.zero_ne_one (hn0.symm.trans hn1)

lemma colorClass_union : colorClass 0 ∪ colorClass 1 = Set.univ := by
  ext n
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  generalize hcolor : pellColor n = i
  fin_cases i
  · exact Or.inl hcolor
  · exact Or.inr hcolor

end

end Erdos1211Upper
