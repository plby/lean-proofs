/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsorptionPowers

/-! # Exact tolerance roots and the source smallness exponents -/

namespace Erdos4b.FGKMT

noncomputable section

def coveringTolerance (δ : ℝ) (j : ℕ) : ℝ := δ ^ (1 / (10 : ℝ) ^ j)

def coveringRoot (η : ℝ) : ℝ := η ^ (1 / 30 : ℝ)

theorem coveringTolerance_pos {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    0 < coveringTolerance δ j := Real.rpow_pos_of_pos hδ _

theorem coveringTolerance_le_one {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (j : ℕ) :
    coveringTolerance δ j ≤ 1 := Real.rpow_le_one hδ0 hδ1 (by positivity)

theorem coveringTolerance_pow {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) :
    coveringTolerance δ j ^ (10 ^ j) = δ := by
  simpa only [coveringTolerance, Nat.cast_pow, Nat.cast_ofNat, one_div] using
    (Real.rpow_inv_natCast_pow hδ (n := 10 ^ j) (by positivity))

theorem coveringTolerance_successor {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) :
    coveringTolerance δ (j + 1) = coveringTolerance δ j ^ (1 / 10 : ℝ) := by
  unfold coveringTolerance
  rw [← Real.rpow_mul hδ]
  congr 1
  rw [pow_succ]
  field_simp

theorem delta_le_coveringTolerance_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {j : ℕ} (hj : 1 ≤ j) : δ ≤ coveringTolerance δ j ^ 2 := by
  have ht0 : 0 ≤ coveringTolerance δ j := Real.rpow_nonneg hδ0 _
  have ht1 := coveringTolerance_le_one hδ0 hδ1 j
  have hpow : 2 ≤ 10 ^ j := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (10 : ℕ)) hj
    norm_num at h
    omega
  calc
    δ = coveringTolerance δ j ^ (10 ^ j) := (coveringTolerance_pow hδ0 j).symm
    _ ≤ _ := absorption_power_antitone ht0 ht1 hpow

theorem coveringTolerance_small {δ S : ℝ} (hδ : 0 ≤ δ) (hS : 0 < S) (j : ℕ)
    (hsmall : δ ≤ (1 / S) ^ (10 ^ (j + 2))) :
    coveringTolerance δ j ≤ (1 / S) ^ 100 := by
  have htol0 : 0 ≤ coveringTolerance δ j := Real.rpow_nonneg hδ _
  apply (pow_le_pow_iff_left₀ htol0 (by positivity : 0 ≤ (1 / S) ^ 100)
    (by positivity : (10 : ℕ) ^ j ≠ 0)).mp
  rw [coveringTolerance_pow hδ j, ← pow_mul]
  have hexp : 10 ^ (j + 2) = 100 * 10 ^ j := by rw [pow_add]; norm_num; ring
  simpa only [hexp] using hsmall

theorem coveringRoot_pos {η : ℝ} (hη : 0 < η) : 0 < coveringRoot η :=
  Real.rpow_pos_of_pos hη _

theorem coveringRoot_thirtieth {η : ℝ} (hη : 0 ≤ η) : coveringRoot η ^ 30 = η := by
  simpa only [coveringRoot, one_div, Nat.cast_ofNat] using
    (Real.rpow_inv_natCast_pow hη (n := 30) (by norm_num))

theorem coveringRoot_cube {η : ℝ} (hη : 0 ≤ η) :
    coveringRoot η ^ 3 = η ^ (1 / 10 : ℝ) := by
  rw [coveringRoot, ← Real.rpow_natCast, ← Real.rpow_mul hη]
  norm_num

theorem coveringRoot_sixtieth {η : ℝ} (hη : 0 ≤ η) : coveringRoot η ^ 60 = η ^ 2 := by
  rw [show 60 = 30 * 2 from rfl, pow_mul, coveringRoot_thirtieth hη]

theorem coveringRoot_scaled_le_one {η S : ℝ} (hη : 0 ≤ η) (hS : 0 < S)
    (hsmall : η ≤ (1 / S) ^ 90) : S ^ 3 * coveringRoot η ≤ 1 := by
  have hpower : (S ^ 3 * coveringRoot η) ^ 30 ≤ 1 := by
    calc
      _ = S ^ 90 * η := by rw [mul_pow, ← pow_mul, coveringRoot_thirtieth hη]
      _ ≤ S ^ 90 * (1 / S) ^ 90 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by field_simp
  by_contra hnot
  have hbig := one_lt_pow₀ (lt_of_not_ge hnot) (by norm_num : 30 ≠ 0)
  linarith

theorem covering_stage_root_conditions {δ S : ℝ} (hδ : 0 < δ) (hS : 256 ≤ S)
    {j : ℕ} (hj : 1 ≤ j) (hsmall : δ ≤ (1 / S) ^ (10 ^ (j + 2))) :
    let z := coveringRoot (coveringTolerance δ j)
    0 < z ∧ z ^ 30 = coveringTolerance δ j ∧ z ^ 3 = coveringTolerance δ (j + 1) ∧
      S ^ 3 * z ≤ 1 ∧ δ ≤ z ^ 60 := by
  intro z
  have hSpos : 0 < S := by linarith
  have hinv0 : 0 ≤ 1 / S := by positivity
  have hinv1 : 1 / S ≤ 1 := (div_le_one hSpos).mpr (by linarith)
  have hδ1 : δ ≤ 1 := hsmall.trans (pow_le_one₀ hinv0 hinv1)
  have htpos := coveringTolerance_pos hδ j
  have ht := (coveringTolerance_small hδ.le hSpos j hsmall).trans
    (absorption_power_antitone hinv0 hinv1 (by norm_num : 90 ≤ 100))
  refine ⟨coveringRoot_pos htpos, coveringRoot_thirtieth htpos.le, ?_,
    coveringRoot_scaled_le_one htpos.le hSpos ht, ?_⟩
  · exact (coveringRoot_cube htpos.le).trans (coveringTolerance_successor hδ.le j).symm
  · rw [show z ^ 60 = coveringTolerance δ j ^ 2 from coveringRoot_sixtieth htpos.le]
    exact delta_le_coveringTolerance_sq hδ.le hδ1 hj

theorem covering_smallness_mono {δ S : ℝ} (hS : 1 ≤ S) {j m : ℕ} (hjm : j ≤ m)
    (hsmall : δ ≤ (1 / S) ^ (10 ^ (m + 2))) : δ ≤ (1 / S) ^ (10 ^ (j + 2)) := by
  have hSpos : 0 < S := by linarith
  exact hsmall.trans (absorption_power_antitone (by positivity)
    ((div_le_one hSpos).mpr hS)
    (Nat.pow_le_pow_right (by norm_num : 1 ≤ (10 : ℕ)) (by omega)))

end

end Erdos4b.FGKMT
