import ErdosProblems.Erdos587.LatticeBounds
import ErdosProblems.Erdos587.Periodization

/-! A one-sixth frequency moment for a fixed dilated Schwartz weight. -/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

lemma sixth_root_le_one_add {x : ℝ} (hx : 0 ≤ x) : x ^ (1 / 6 : ℝ) ≤ 1 + x := by
  by_cases hx1 : x ≤ 1
  · have hh := Real.rpow_le_one hx hx1 (by norm_num : (0 : ℝ) ≤ 1 / 6)
    linarith
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1)
      (by norm_num : (1 / 6 : ℝ) ≤ 1)
    rw [Real.rpow_one] at hh
    linarith

lemma sixth_root_frequency_trade {σ : ℝ} (hσ : 0 < σ) (m : ℤ) :
    |(m : ℝ)| ^ (1 / 6 : ℝ) ≤ σ ^ (-(1 / 6 : ℝ)) * (1 + σ * |(m : ℝ)|) := by
  have hh := sixth_root_le_one_add (mul_nonneg hσ.le (abs_nonneg (m : ℝ)))
  rw [Real.mul_rpow hσ.le (abs_nonneg (m : ℝ))] at hh
  have hcancel : σ ^ (-(1 / 6 : ℝ)) * σ ^ (1 / 6 : ℝ) = 1 := by
    rw [← Real.rpow_add hσ]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hσ.le (-(1 / 6 : ℝ)))
  simpa only [← mul_assoc, hcancel, one_mul] using hscaled

theorem exists_scaled_schwartz_sixth_moment (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      Summable (fun m : ℤ => ‖(σ : ℂ) * g (σ * m)‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)) ∧
      (∑' m : ℤ, ‖(σ : ℂ) * g (σ * m)‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)) ≤
        C * σ ^ (-(1 / 6 : ℝ)) := by
  obtain ⟨A, hA, hdecay⟩ := exists_schwartz_absolute_decay_bound g 3
  refine ⟨5 * A, by positivity, ?_⟩
  intro σ hσ hσ1
  obtain ⟨hkernel, hkernelBound⟩ := normalized_lattice_kernel_bound hσ hσ1
  have hpoint (m : ℤ) : ‖(σ : ℂ) * g (σ * m)‖ * |(m : ℝ)| ^ (1 / 6 : ℝ) ≤
      (A * σ ^ (-(1 / 6 : ℝ))) * (σ / (1 + σ * |(m : ℝ)|) ^ 2) := by
    have hd := hdecay (σ * m)
    rw [abs_mul, abs_of_pos hσ] at hd
    have hbase : 0 < 1 + σ * |(m : ℝ)| := by positivity
    have hg : ‖g (σ * m)‖ ≤ A / (1 + σ * |(m : ℝ)|) ^ 3 :=
      (le_div_iff₀ (pow_pos hbase 3)).mpr (by simpa only [mul_comm] using hd)
    have hc : ‖(σ : ℂ) * g (σ * m)‖ ≤ A * σ / (1 + σ * |(m : ℝ)|) ^ 3 := by
      calc
        _ = σ * ‖g (σ * m)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
        _ ≤ σ * (A / (1 + σ * |(m : ℝ)|) ^ 3) := mul_le_mul_of_nonneg_left hg hσ.le
        _ = _ := by ring
    calc
      _ ≤ (A * σ / (1 + σ * |(m : ℝ)|) ^ 3) *
          (σ ^ (-(1 / 6 : ℝ)) * (1 + σ * |(m : ℝ)|)) :=
        mul_le_mul hc (sixth_root_frequency_trade hσ m) (by positivity) (by positivity)
      _ = _ := by field_simp
  have hnonneg (m : ℤ) : 0 ≤ ‖(σ : ℂ) * g (σ * m)‖ * |(m : ℝ)| ^ (1 / 6 : ℝ) := by positivity
  have hs : Summable (fun m : ℤ => ‖(σ : ℂ) * g (σ * m)‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)) := by
    apply (hkernel.mul_left (A * σ ^ (-(1 / 6 : ℝ)))).of_norm_bounded
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg m)]
    exact hpoint m
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' m : ℤ, (A * σ ^ (-(1 / 6 : ℝ))) * (σ / (1 + σ * |(m : ℝ)|) ^ 2) :=
      hs.tsum_le_tsum hpoint (hkernel.mul_left _)
    _ = (A * σ ^ (-(1 / 6 : ℝ))) * ∑' m : ℤ, σ / (1 + σ * |(m : ℝ)|) ^ 2 := tsum_mul_left
    _ ≤ (A * σ ^ (-(1 / 6 : ℝ))) * 5 := mul_le_mul_of_nonneg_left hkernelBound (by positivity)
    _ = _ := by ring

theorem exists_scaledFourierCoeff_sixth_moment (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      Summable (fun m : ℤ => ‖scaledFourierCoeff g σ m‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)) ∧
      (∑' m : ℤ, ‖scaledFourierCoeff g σ m‖ * |(m : ℝ)| ^ (1 / 6 : ℝ)) ≤
        C * σ ^ (-(1 / 6 : ℝ)) := by
  exact exists_scaled_schwartz_sixth_moment (𝓕 g : 𝓢(ℝ, ℂ))

end Erdos587
