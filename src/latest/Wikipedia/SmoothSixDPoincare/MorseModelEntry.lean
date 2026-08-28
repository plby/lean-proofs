import Wikipedia.SmoothSixDPoincare.MorseModelFlow

/-!
# Strict entry into the lower sublevel with a Morse handle adjoined

Positive-time trajectories from the model attachment enter its interior.
In particular, the boundary is crossed immediately; forward invariance
alone would not imply this condition needed for continuous stopping times.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Strict descent holds away from the critical center, including the extreme Morse indices. -/
theorem quadratic_descentFlow_lt {t : ℝ} (ht : 0 < t) {z : N × P} (hz : z ≠ 0) :
    quadratic (descentFlow t z) < quadratic z := by
  have h₁ := (sq_le_sq₀ (norm_nonneg z.1) (norm_nonneg (descentFlow t z).1)).mpr
    (norm_fst_le_descentFlow ht.le z)
  have h₂ := (sq_le_sq₀ (norm_nonneg (descentFlow t z).2) (norm_nonneg z.2)).mpr
    (norm_snd_descentFlow_le ht.le z)
  by_cases hu : z.1 = 0
  · have hv : z.2 ≠ 0 := fun hv => hz (Prod.ext hu hv)
    have hvnorm : ‖(descentFlow t z).2‖ < ‖z.2‖ := by
      rw [norm_descentFlow_snd]
      exact mul_lt_of_lt_one_left (norm_pos_iff.mpr hv)
        (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
    have hv₂ := (sq_lt_sq₀ (norm_nonneg (descentFlow t z).2) (norm_nonneg z.2)).mpr hvnorm
    exact add_lt_add_of_le_of_lt (neg_le_neg h₁) hv₂
  · have hunorm : ‖z.1‖ < ‖(descentFlow t z).1‖ := by
      rw [norm_descentFlow_fst]
      exact lt_mul_of_one_lt_left (norm_pos_iff.mpr hu) (Real.one_lt_exp_iff.mpr ht)
    have hu₂ := (sq_lt_sq₀ (norm_nonneg z.1) (norm_nonneg (descentFlow t z).1)).mpr hunorm
    exact add_lt_add_of_lt_of_le (neg_lt_neg hu₂) h₂

/-- Every positive-time point of a forward trajectory from the attachment is interior. -/
theorem descentFlow_mem_interior_lower_union_handle {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    {z : N × P} (hz : z ∈ {w | quadratic w ≤ -(ρ ^ 2)} ∪ range (modelMap ρ)) :
    descentFlow t z ∈ interior ({w | quadratic w ≤ -(ρ ^ 2)} ∪ range (modelMap ρ)) := by
  have hc : Continuous (quadratic (N := N) (P := P)) :=
    (continuous_fst.norm.pow 2).neg.add (continuous_snd.norm.pow 2)
  rw [mem_lower_union_handle_iff hρ] at hz
  rcases hz with hq | hv
  · have hne : z ≠ 0 := by
      intro h
      have hq' : (0 : ℝ) ≤ -(ρ ^ 2) := by simpa [h, quadratic] using hq
      nlinarith [sq_pos_of_pos hρ]
    have hlt : quadratic (descentFlow t z) < -(ρ ^ 2) :=
      (quadratic_descentFlow_lt ht hne).trans_le hq
    apply mem_interior.mpr
    refine ⟨{w | quadratic w < -(ρ ^ 2)}, ?_, isOpen_lt hc continuous_const, hlt⟩
    intro w hw
    exact Or.inl (show quadratic w ≤ -(ρ ^ 2) from le_of_lt hw)
  · have hlt : ‖(descentFlow t z).2‖ < ρ := by
      rw [norm_descentFlow_snd]
      calc
        _ ≤ Real.exp (-t) * ρ := mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le
        _ < ρ := mul_lt_of_lt_one_left hρ (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
    apply mem_interior.mpr
    refine ⟨{w : N × P | ‖w.2‖ < ρ}, ?_, isOpen_lt continuous_snd.norm continuous_const, hlt⟩
    intro w hw
    exact (mem_lower_union_handle_iff hρ w).mpr (Or.inr hw.le)

end Wikipedia.SmoothSixDPoincare.MorseHandle
