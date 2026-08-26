import ErdosProblems.Erdos421.PrimeMinorantReference

/-! # The fixed short width and its required prime-free interval length -/

namespace Erdos421

open Filter Topology

noncomputable def primeShortWidth (X : ℝ) : ℝ := 16 * Real.pi / X ^ (899 / 1000 : ℝ)

noncomputable def primeShortLength (X : ℝ) : ℝ := 1 + 64 * Real.pi * X ^ (101 / 1000 : ℝ)

theorem primeShortWidth_pos {X : ℝ} (hX : 0 < X) : 0 < primeShortWidth X := by
  dsimp only [primeShortWidth]
  positivity

theorem primeShortLength_eq {X : ℝ} (hX : 0 < X) :
    1 + 4 * primeShortWidth X * X = primeShortLength X := by
  have hpow : X ^ (101 / 1000 : ℝ) * X ^ (899 / 1000 : ℝ) = X := by
    rw [← Real.rpow_add hX]
    norm_num
  have heq : X ^ (101 / 1000 : ℝ) = X / X ^ (899 / 1000 : ℝ) :=
    (eq_div_iff (Real.rpow_pos_of_pos hX _).ne').mpr hpow
  dsimp only [primeShortWidth, primeShortLength]
  rw [heq]
  ring

theorem primeShortLength_mono {X Y : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) :
    primeShortLength X ≤ primeShortLength Y := by
  unfold primeShortLength
  have hm : 64 * Real.pi * X ^ (101 / 1000 : ℝ) ≤ 64 * Real.pi * Y ^ (101 / 1000 : ℝ) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hX hXY (by norm_num : (0 : ℝ) ≤ 101 / 1000)) (by positivity)
  exact add_le_add le_rfl hm

theorem eventually_reference_width_small {L r : ℝ} (hL : 2 ≤ L) (hr : 0 < r) :
    ∀ᶠ X : ℕ in atTop, (Real.log X) ^ (-L) ≤ r := by
  have hlim := (tendsto_rpow_neg_atTop (by linarith : 0 < L)).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact (hlim.eventually (gt_mem_nhds hr)).mono (fun _ h ↦ h.le)

end Erdos421
