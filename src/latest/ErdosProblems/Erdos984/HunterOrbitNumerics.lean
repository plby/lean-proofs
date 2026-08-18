/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterOrbitBounds

/-!
# Numerical simplification of the orbit second moment
-/

open Set Function MeasureTheory AddCircle
open scoped BigOperators

namespace Erdos984

noncomputable section

lemma hunterRankWitness_le_div_eighty (D : ℕ) (hD : 400 ≤ D) :
    hunterRankWitness D ≤ D / 80 := by
  simp only [hunterRankWitness]
  omega

lemma hunterResonancePower_le (D : ℕ) (hD : 400 ≤ D) :
    (2 * hunterKernelPower D + 1) ^ hunterRankWitness D ≤ D ^ (4 * D) := by
  have hDpos : 0 < D := by omega
  have hbase := two_mul_hunterKernelPower_add_one_le D (by omega)
  have hrank := hunterRankWitness_le_div_eighty D hD
  calc
    (2 * hunterKernelPower D + 1) ^ hunterRankWitness D ≤
        (D ^ 252) ^ hunterRankWitness D :=
      Nat.pow_le_pow_left hbase _
    _ ≤ (D ^ 252) ^ (D / 80) :=
      Nat.pow_le_pow_right (pow_pos hDpos _) hrank
    _ = D ^ (252 * (D / 80)) := by rw [← pow_mul]
    _ ≤ D ^ (4 * D) := by
      apply Nat.pow_le_pow_right hDpos
      omega

lemma hunterKernelMean_lower_power (D : ℕ) (hD : 2 ≤ D) :
    ((D : ℝ) ^ (252 * D))⁻¹ ≤ hunterKernelMean D := by
  have hDreal : (0 : ℝ) < D := by positivity
  have hbaseNat := two_mul_hunterKernelPower_add_one_le D hD
  have hbase : ((2 * hunterKernelPower D + 1 : ℕ) : ℝ) ≤
      (D : ℝ) ^ 252 := by exact_mod_cast hbaseNat
  have hleft : 0 < (D : ℝ) ^ 252 := pow_pos hDreal _
  have hright : 0 < (((2 * hunterKernelPower D + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < 2 * hunterKernelPower D + 1 by omega)
  have hinv : ((D : ℝ) ^ 252)⁻¹ ≤
      (((2 * hunterKernelPower D + 1 : ℕ) : ℝ))⁻¹ := by
    exact (inv_le_inv₀ hleft hright).2 hbase
  calc
    ((D : ℝ) ^ (252 * D))⁻¹ = (((D : ℝ) ^ 252)⁻¹) ^ D := by
      rw [inv_pow, ← pow_mul]
    _ ≤ ((((2 * hunterKernelPower D + 1 : ℕ) : ℝ))⁻¹) ^ D :=
      pow_le_pow_left₀ (by positivity) hinv D
    _ = ((1 : ℝ) / (2 * hunterKernelPower D + 1)) ^ D := by
      rw [one_div]
      push_cast
      rfl
    _ ≤ hunterKernelMean D := hunterKernelMean_lower D

lemma one_div_hunterPhaseTolerance (D : ℕ) (hD : 0 < D) :
    1 / hunterPhaseTolerance D = (D : ℝ) ^ (99000 * D) := by
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  rw [hunterPhaseTolerance, hunterX, Nat.cast_pow]
  rw [show 100000 * D = 1000 * D + 99000 * D by omega, pow_add]
  field_simp

lemma hunter_nonresonant_term_le_mean_sq_X_sq
    (D : ℕ) (hD : 400 ≤ D) :
    hunterKernelMean D * (1 / hunterPhaseTolerance D) ^ 2 ≤
      hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hmean := hunterKernelMean_lower_power D (by omega)
  have hphase : (1 / hunterPhaseTolerance D) ^ 2 =
      (D : ℝ) ^ (198000 * D) := by
    rw [one_div_hunterPhaseTolerance D (by omega), ← pow_mul]
    congr 1
    ring
  have hX : (hunterX D : ℝ) ^ 2 = (D : ℝ) ^ (200000 * D) := by
    simp only [hunterX, Nat.cast_pow]
    rw [← pow_mul]
    congr 1
    ring
  have hpower : (1 / hunterPhaseTolerance D) ^ 2 ≤
      ((D : ℝ) ^ (252 * D))⁻¹ * (hunterX D : ℝ) ^ 2 := by
    rw [hphase, hX]
    rw [show 200000 * D = 252 * D + 199748 * D by ring, pow_add]
    field_simp
    exact pow_le_pow_right₀ hDreal (by omega : 198000 * D ≤ 199748 * D)
  calc
    hunterKernelMean D * (1 / hunterPhaseTolerance D) ^ 2 ≤
        hunterKernelMean D *
          (((D : ℝ) ^ (252 * D))⁻¹ * (hunterX D : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hpower (hunterKernelMean_pos D).le
    _ ≤ hunterKernelMean D *
          (hunterKernelMean D * (hunterX D : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hmean (sq_nonneg _)
      · exact (hunterKernelMean_pos D).le
    _ = hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 := by ring

lemma hunter_fourD_add_one_le_fiveD (D : ℕ) (hD : 2 ≤ D) :
    D ^ (4 * D) + 1 ≤ D ^ (5 * D) := by
  have hDpos : 0 < D := by omega
  have hpowpos : 0 < D ^ (4 * D) := pow_pos hDpos _
  have hpowone : 1 ≤ D ^ (4 * D) := by omega
  have hpowtwo : 2 ≤ D ^ D := by
    calc
      2 ≤ D := hD
      _ ≤ D ^ D := by
        rw [show D ^ D = D ^ ((D - 1) + 1) by congr 1 <;> omega, pow_succ]
        exact Nat.le_mul_of_pos_left D (pow_pos hDpos _)
  calc
    D ^ (4 * D) + 1 ≤ 2 * D ^ (4 * D) := by omega
    _ ≤ D ^ D * D ^ (4 * D) := Nat.mul_le_mul_right _ hpowtwo
    _ = D ^ (5 * D) := by rw [← pow_add]; congr 1; ring

/-- At the explicit parameter scale, the normalized second moment costs at
most `D^(5D)`. -/
lemma integral_normSq_hunterOrbitKernelSum_le_power
    (D : ℕ) (hD : 400 ≤ D) {theta : UnitAddTorus (Fin D)}
    (htheta : HunterTypicalRotation D theta)
    (a d : ℕ) (hd : 0 < d) (hdN : d < hunterN D) :
    ∫ center : UnitAddTorus (Fin D),
        Complex.normSq (hunterOrbitKernelSum D theta a d center) ≤
      (D ^ (5 * D) : ℕ) * hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 := by
  have hraw := integral_normSq_hunterOrbitKernelSum_le
    D (by omega) htheta a d hd hdN
  have hres := hunterResonancePower_le D hD
  have hnonres := hunter_nonresonant_term_le_mean_sq_X_sq D hD
  have hfactor := hunter_fourD_add_one_le_fiveD D (by omega)
  calc
    ∫ center : UnitAddTorus (Fin D),
        Complex.normSq (hunterOrbitKernelSum D theta a d center) ≤
      ((2 * hunterKernelPower D + 1) ^ hunterRankWitness D : ℕ) *
          hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 +
        hunterKernelMean D * (1 / hunterPhaseTolerance D) ^ 2 := hraw
    _ ≤ (D ^ (4 * D) : ℕ) *
          hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 +
        hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2 := by
      apply add_le_add
      · gcongr
      · exact hnonres
    _ = ((D ^ (4 * D) + 1 : ℕ) : ℝ) *
          (hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2) := by
      push_cast
      ring
    _ ≤ (D ^ (5 * D) : ℕ) *
          (hunterKernelMean D ^ 2 * (hunterX D : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hfactor
      · positivity
    _ = (D ^ (5 * D) : ℕ) * hunterKernelMean D ^ 2 *
          (hunterX D : ℝ) ^ 2 := by ring

end

end Erdos984
