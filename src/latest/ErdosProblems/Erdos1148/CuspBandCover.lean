import ErdosProblems.Erdos1148.FundamentalFrameHeight
import ErdosProblems.Erdos1148.DyadicBandCover

/-! # Covering an intrinsic cusp truncated at a prescribed maximum height -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

lemma exists_dyadic_height_index {H h : ℝ} (hH : 0 < H) (hh : H ≤ h) {J : ℕ}
    (hmax : h < (2 : ℝ) ^ J * H) :
    ∃ j : Fin J, h ∈ Set.Icc ((2 : ℝ) ^ j.val * H) (2 * ((2 : ℝ) ^ j.val * H)) := by
  have hratio : 1 ≤ h / H := (le_div_iff₀ hH).mpr (by simpa using hh)
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hjJ : j < J := by
    by_contra h
    have hpow : (2 : ℝ) ^ J ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt h)
    have hlower := (le_div_iff₀ hH).mp (hpow.trans hj)
    linarith
  refine ⟨⟨j, hjJ⟩, (le_div_iff₀ hH).mp hj, ?_⟩
  have hu := (div_lt_iff₀ hH).mp hj'
  dsimp only
  rw [pow_succ] at hu
  nlinarith

theorem cusp_sdiff_subset_dyadicFrameBands {H Y : ℝ} (hH : 2 ≤ H) (hY : 0 < Y)
    {J : ℕ} (hmax : Y < (2 : ℝ) ^ J * H) :
    modularCusp H \ modularCusp Y ⊆
      ⋃ j : Fin J, modularFrameBand ((2 : ℝ) ^ j.val * H)
        (mul_pos (pow_pos (by norm_num) _) (by linarith)) := by
  intro x hx
  obtain ⟨z, θ, hz, hθ, hframe⟩ := exists_modular_fundamental_frame x
  have hlow : H < Real.sqrt z.im := sqrt_im_gt_height_of_frame_mem_cusp hz θ hH
    (by rw [hframe]; exact hx.1)
  have hupp : Real.sqrt z.im ≤ Y := by
    have him := frame_im_le_height_sq_of_not_mem_cusp z θ hY (by rw [hframe]; exact hx.2)
    have h := Real.sqrt_le_sqrt him
    simpa only [Real.sqrt_sq hY.le] using h
  have hH0 : 0 < H := by linarith
  obtain ⟨j, hj⟩ := exists_dyadic_height_index hH0 hlow.le (hupp.trans_lt hmax)
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  let p : frameBoxParameters (-(1 / 2)) ((2 : ℝ) ^ j.val * H) (-Real.pi)
      1 ((2 : ℝ) ^ j.val * H) (2 * Real.pi) :=
    ⟨(z.re, Real.sqrt z.im, θ), by
      refine ⟨?_, ?_, ?_⟩
      · have hre := abs_le.mp hz.2
        constructor <;> linarith
      · constructor
        · exact hj.1
        · linarith [hj.2]
      · constructor <;> linarith [hθ.1, hθ.2]⟩
  refine ⟨p, ?_⟩
  change modularMk (cuspFrame z.re (Real.sqrt z.im) θ _) = x
  rw [cuspFrame, ← upperHalfPlane_toSL2R_eq_frame]
  exact hframe

theorem cusp_mass_sq_le_pair_mass_of_height_cap (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    {H Y δ : ℝ} (hH : 2 ≤ H) (hY : 0 < Y) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcap : μ (modularCusp Y) = 0) {J : ℕ} (hmax : Y < (2 : ℝ) ^ J * H) :
    μ.real (modularCusp H) ^ 2 ≤
      (2 * (2 * Real.pi + 1) * ((4 / 3) / (δ ^ 3 * H ^ 2) + J / δ ^ 2)) *
        (μ.prod μ).real (modularClosePairs (5 * δ)) := by
  have hlow : 0 < H := by linarith
  have hmono : μ.real (modularCusp H) ≤
      μ.real (⋃ j : Fin J, modularFrameBand ((2 : ℝ) ^ j.val * H) (by positivity)) := by
    rw [← measureReal_sdiff_null (μ := μ) (s₁ := modularCusp H) (s₂ := modularCusp Y)
      (by simp only [Measure.real, hcap, ENNReal.toReal_zero])]
    exact measureReal_mono (cusp_sdiff_subset_dyadicFrameBands hH hY hmax)
  exact (pow_le_pow_left₀ measureReal_nonneg hmono 2).trans
    (dyadicBand_mass_sq_le_pair_mass μ hlow hδ hδ1 J)

end Erdos1148.DukeArithmetic
