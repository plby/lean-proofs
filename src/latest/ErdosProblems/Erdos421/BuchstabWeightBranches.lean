import ErdosProblems.Erdos421.BuchstabWeightRegularity

/-! # Smooth branch conditions for the finite Buchstab prime weights -/

namespace Erdos421

theorem inverse_buchstab_branch_conditions {X a b : ℝ} (ha : 1 < a)
    (harg : ∀ t ∈ Set.Icc a b, 1 ≤ logarithmicBuchstabArgument X t) :
    (∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) (logarithmicBuchstabArgument X t)) ∧
    ContinuousOn (fun t ↦ deriv (fun u : ℝ ↦ u⁻¹) (logarithmicBuchstabArgument X t))
      (Set.Icc a b) ∧
    (∀ t ∈ Set.Icc a b, |(logarithmicBuchstabArgument X t)⁻¹| ≤ 1) ∧
    (∀ t ∈ Set.Icc a b, |deriv (fun u : ℝ ↦ u⁻¹) (logarithmicBuchstabArgument X t)| ≤ 2) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < logarithmicBuchstabArgument X t :=
    fun t ht ↦ lt_of_lt_of_le zero_lt_one (harg t ht)
  have hsub : Set.Icc a b ⊆ Set.Ioi 1 := fun _ ht ↦ ha.trans_le ht.1
  have hc := (logarithmicBuchstabArgument_continuousOn X).mono hsub
  refine ⟨fun t ht ↦ (hasDerivAt_inv (hpos t ht).ne').differentiableAt, ?_, ?_, ?_⟩
  · simp only [deriv_inv]
    exact ((hc.pow 2).inv₀ (fun t ht ↦ pow_ne_zero 2 (hpos t ht).ne')).neg
  · intro t ht
    rw [abs_of_pos (inv_pos.mpr (hpos t ht))]
    exact (inv_le_one₀ (hpos t ht)).mpr (harg t ht)
  · intro t ht
    rw [deriv_inv, abs_neg, abs_inv, abs_of_nonneg (sq_nonneg _)]
    exact ((inv_le_one₀ (sq_pos_of_pos (hpos t ht))).mpr
      (one_le_pow₀ (harg t ht))).trans (by norm_num)

theorem upper_buchstab_branch_conditions (n : ℕ) {X a b : ℝ} (ha : 1 < a)
    (harg : ∀ t ∈ Set.Icc a b, 2 ≤ logarithmicBuchstabArgument X t) :
    (∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (buchstabExtension n) (logarithmicBuchstabArgument X t)) ∧
    ContinuousOn (fun t ↦ deriv (buchstabExtension n) (logarithmicBuchstabArgument X t))
      (Set.Icc a b) ∧
    (∀ t ∈ Set.Icc a b, |buchstabExtension n (logarithmicBuchstabArgument X t)| ≤ 1) ∧
    (∀ t ∈ Set.Icc a b, |deriv (buchstabExtension n) (logarithmicBuchstabArgument X t)| ≤ 2) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < logarithmicBuchstabArgument X t := by
    intro t ht
    have h := harg t ht
    linarith
  have hsub : Set.Icc a b ⊆ Set.Ioi 1 := fun _ ht ↦ ha.trans_le ht.1
  have hc := (logarithmicBuchstabArgument_continuousOn X).mono hsub
  refine ⟨fun t ht ↦ (buchstabExtension_hasDerivAt n (hpos t ht).ne').differentiableAt, ?_, ?_, ?_⟩
  · exact (buchstabExtension_deriv_continuousOn n).comp hc (fun t ht ↦ hpos t ht)
  · intro t ht
    rw [buchstabExtension_eq n (harg t ht), abs_of_pos (finiteBuchstab_pos _ _)]
    exact finiteBuchstab_le_one _ (by have h := harg t ht; linarith)
  · intro t ht
    exact (buchstabExtension_deriv_abs_le n (harg t ht)).trans
      (div_le_self (by norm_num : (0 : ℝ) ≤ 2) (by have h := harg t ht; linarith))

end Erdos421
