import ErdosProblems.Erdos67b.MRTLogDyadicBlocks

/-! # Admissible lower scales in the anchored logarithmic window -/

namespace Erdos67b

noncomputable section

def mrtLogGoodBlockIndex (K W : ℕ) (R : ℝ) : ℕ :=
  K + ⌈Real.log W / (R * Real.log 2)⌉₊

theorem mrtLogWindowBlockCount_le {W : ℕ} (hlog : 1 ≤ Real.log W) :
    (mrtLogWindowBlockCount W : ℝ) ≤ 4 * Real.log W := by
  have hh := mrtDyadicBlockCount_le_log hlog
  simp only [mrtDyadicBlockCount, mrtLogWindowBlockCount, Nat.cast_add,
    Nat.cast_one, Nat.cast_ofNat] at hh ⊢
  linarith only [hh, hlog]

theorem mrtLogGoodBlockIndex_le (K : ℕ) {W : ℕ} (hW : 1 ≤ W) {R : ℝ} (hR : 1 ≤ R) :
    (mrtLogGoodBlockIndex K W R : ℝ) ≤ K + 1 + 2 * Real.log W / R := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hlog : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW)
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have htwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ Real.log W / (R * Real.log 2) by positivity)).le
  have hquot : Real.log W / (R * Real.log 2) ≤ 2 * Real.log W / R := by
    apply (div_le_div_iff₀ (mul_pos hRpos htwoPos) hRpos).2
    nlinarith only [mul_le_mul_of_nonneg_left htwo (mul_nonneg hlog hRpos.le)]
  simp only [mrtLogGoodBlockIndex, Nat.cast_add]
  linarith only [hceil, hquot]

theorem mrtGood_index_log_lower {K W j : ℕ} {R : ℝ} (hR : 0 < R)
    (hj : mrtLogGoodBlockIndex K W R ≤ j) :
    (K : ℝ) * Real.log 2 + Real.log W / R ≤ (j : ℝ) * Real.log 2 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.le_ceil (Real.log W / (R * Real.log 2))
  have hindex : (K : ℝ) + (⌈Real.log W / (R * Real.log 2)⌉₊ : ℝ) ≤ j := by
    exact_mod_cast hj
  have hceil := mul_le_mul_of_nonneg_right hc htwo.le
  have htotal := mul_le_mul_of_nonneg_right hindex htwo.le
  have hcancel : (Real.log W / (R * Real.log 2)) * Real.log 2 = Real.log W / R := by
    field_simp
  rw [hcancel] at hceil
  linarith only [hceil, htotal]

theorem mrtLog_natDiv_lower {Y w : ℕ} (hw : 0 < w) (hYw : w ≤ Y) :
    Real.log Y - Real.log (2 * (w : ℝ)) ≤ Real.log ((Y / w : ℕ) : ℝ) := by
  have hY : 0 < Y := hw.trans_le hYw
  have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
  have hwreal : (0 : ℝ) < w := by exact_mod_cast hw
  have hbound := (mrtLogWindow_lower_bounds hw hYw).2
  have hmul : (Y : ℝ) ≤ (2 * (w : ℝ)) * ((Y / w : ℕ) : ℝ) := by exact_mod_cast hbound
  have hfloor : (Y : ℝ) / (2 * w) ≤ ((Y / w : ℕ) : ℝ) :=
    (div_le_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hmul)
  have hh := Real.log_le_log (div_pos hYreal (by positivity)) hfloor
  simpa only [Real.log_div hYreal.ne' (by positivity : 2 * (w : ℝ) ≠ 0)] using hh

theorem mrtLog_dyadicAnchor {N : ℕ} (hN : 0 < N) (j : ℕ) :
    Real.log ((2 ^ j * N : ℕ) : ℝ) = (j : ℝ) * Real.log 2 + Real.log N := by
  push_cast
  rw [Real.log_mul (by positivity) (by exact_mod_cast Nat.ne_of_gt hN), Real.log_pow]

theorem mrtLog_window_upper {X W N : ℕ} (hX : 0 < X) (hW : 0 < W) (hN : 0 < N)
    (hupper : X ≤ 2 * W * N) :
    Real.log X ≤ Real.log 2 + Real.log W + Real.log N := by
  have hh := Real.log_le_log (by exact_mod_cast hX : (0 : ℝ) < X)
    (show (X : ℝ) ≤ 2 * W * N by exact_mod_cast hupper)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hWR : (W : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hW
  rw [Real.log_mul (by positivity : (2 : ℝ) * W ≠ 0) hNR,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hWR] at hh
  exact hh

theorem mrtGood_dyadic_scale {X W N w Y₀ K j : ℕ} {R : ℝ}
    (hX : 0 < X) (hW : 0 < W) (hN : 0 < N) (hw : 0 < w) (hR : 1 ≤ R)
    (hupper : X ≤ 2 * W * N) (hK : max Y₀ (4 * w) ≤ 2 ^ K)
    (hj : mrtLogGoodBlockIndex K W R ≤ j) :
    Y₀ ≤ 2 ^ j * N ∧
      Real.log X ≤ R * Real.log (((2 ^ j * N) / w : ℕ) : ℝ) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hjK : K ≤ j := (Nat.le_add_right K _).trans hj
  have hscale : 2 ^ K ≤ 2 ^ j * N :=
    (Nat.pow_le_pow_right (by norm_num) hjK).trans (Nat.le_mul_of_pos_right _ hN)
  have hY : Y₀ ≤ 2 ^ j * N := ((le_max_left _ _).trans hK).trans hscale
  have hwY : 4 * w ≤ 2 ^ j * N := ((le_max_right _ _).trans hK).trans hscale
  have hlogfloor := mrtLog_natDiv_lower hw (show w ≤ 2 ^ j * N by omega)
  have hlogY := mrtLog_dyadicAnchor hN j
  have hindex := mrtGood_index_log_lower hRpos hj
  have hlogK : Real.log 2 + Real.log (2 * (w : ℝ)) ≤ (K : ℝ) * Real.log 2 := by
    have hfour : 4 * w ≤ 2 ^ K := (le_max_right _ _).trans hK
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < 4 * w)
      (show (4 : ℝ) * w ≤ 2 ^ K by exact_mod_cast hfour)
    rw [show (4 : ℝ) * w = 2 * (2 * w) by ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * (w : ℝ) ≠ 0),
      Real.log_pow] at hh
    exact hh
  have hfloor : Real.log 2 + Real.log W / R + Real.log N ≤
      Real.log (((2 ^ j * N) / w : ℕ) : ℝ) := by
    linarith only [hlogfloor, hlogY, hindex, hlogK]
  have hbase : 0 ≤ Real.log 2 + Real.log N :=
    add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by exact_mod_cast hN))
  refine ⟨hY, ?_⟩
  calc
    _ ≤ Real.log 2 + Real.log W + Real.log N := mrtLog_window_upper hX hW hN hupper
    _ ≤ R * (Real.log 2 + Real.log N) + Real.log W := by
      have hh := mul_le_mul_of_nonneg_right hR hbase
      nlinarith only [hh]
    _ = R * (Real.log 2 + Real.log W / R + Real.log N) := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfloor hRpos.le

end

end Erdos67b
