import ErdosProblems.Erdos421.AdditiveWindowScale

/-! # Logarithmic windows compared with a fixed additive scale on a short block -/

namespace Erdos421

theorem exists_local_logarithmic_window_comparison :
    ∃ K : ℝ, 0 < K ∧ ∀ B z : ℕ, ∀ δ a η x : ℝ,
      0 < δ → δ ≤ 1 / 2 → 0 < a → 0 ≤ η →
      a ≤ x → x ≤ (1 + η) * a → 1 ≤ δ * a →
      |logarithmicRoughWindow B z δ (Real.log x) - additiveRoughWindow B z (δ * a) x| ≤
        K * (δ + a⁻¹ + η) := by
  obtain ⟨K₁, hK₁, hlog⟩ := exists_logarithmicRoughWindow_additive_comparison
  obtain ⟨K₂, hK₂, hscale⟩ := exists_additiveRoughWindow_scale_bound
  refine ⟨K₁ + K₂, by positivity, ?_⟩
  intro B z δ a η x hδ hδ1 ha hη hax hxa hδa
  have hx : 0 < x := ha.trans_le hax
  have hY : 0 < δ * a := mul_pos hδ ha
  have hYZ : δ * a ≤ δ * x := mul_le_mul_of_nonneg_left hax hδ.le
  have hZη : δ * x ≤ (1 + η) * (δ * a) := by
    have h := mul_le_mul_of_nonneg_left hxa hδ.le
    nlinarith
  have h₁ := hlog B z δ x hδ hδ1 hx
  have h₂ := hscale B z (δ * a) (δ * x) η x hY hYZ hZη hη (hδa.trans hYZ) hx.le
  have hinv : x⁻¹ ≤ a⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha hax
  have h₁' : |logarithmicRoughWindow B z δ (Real.log x) - additiveRoughWindow B z (δ * x) x| ≤
      K₁ * (δ + a⁻¹) := h₁.trans
    (mul_le_mul_of_nonneg_left (add_le_add_right hinv δ) hK₁.le)
  have htri := abs_sub_le (logarithmicRoughWindow B z δ (Real.log x))
    (additiveRoughWindow B z (δ * x) x) (additiveRoughWindow B z (δ * a) x)
  rw [abs_sub_comm (additiveRoughWindow B z (δ * x) x)] at htri
  have hbase : 0 ≤ δ + a⁻¹ := by positivity
  nlinarith [mul_nonneg hK₁.le hη, mul_nonneg hK₂.le hbase]

theorem logarithmicRoughWindow_continuous (B z : ℕ) (δ : ℝ) :
    Continuous (logarithmicRoughWindow B z δ) := by
  unfold logarithmicRoughWindow
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro n hn
  apply continuous_const.mul
  unfold logarithmicIntegerWeight
  have harg : Continuous (fun y : ℝ ↦ (y - Real.log (n : ℝ)) / δ) :=
    (continuous_id.sub continuous_const).div_const δ
  exact ((oneSidedSchwartzWindow.continuous.comp harg).const_smul (δ⁻¹ : ℝ)).const_smul
    ((n : ℝ)⁻¹ : ℝ)

end Erdos421
