import Wikipedia.SmoothSixDPoincare.BumpTranslationDiffeomorph

/-!
# Uniform small translations for a smooth compactly supported family

Compact support of the whole parameter-space function gives one Lipschitz
constant. Every spatial slice has that same constant, so one positive
translation radius works for every parameter. The actual slice support
remains compact and the resulting diffeomorphism is fixed outside it.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold NNReal

namespace Wikipedia.SmoothSixDPoincare.SmallPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem lipschitzWith_slice {β : ℝ × E → ℝ} {k : ℝ≥0} (hβ : LipschitzWith k β) (t : ℝ) :
    LipschitzWith k (fun x : E => β (t, x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (β (t, x)) (β (t, y)) ≤ (k : ℝ) * dist (t, x) (t, y) := hβ.dist_le_mul _ _
    _ = (k : ℝ) * dist x y := by
      rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist x y)]

omit [NormedSpace ℝ E] in
theorem hasCompactSupport_slice {β : ℝ × E → ℝ} (hβ : HasCompactSupport β) (t : ℝ) :
    HasCompactSupport (fun x : E => β (t, x)) := by
  have hleft : LeftInverse Prod.snd (fun x : E => (t, x)) := fun _ => rfl
  exact hβ.comp_isClosedEmbedding (hleft.isClosedEmbedding (by fun_prop) (by fun_prop))

omit [NormedSpace ℝ E] in
theorem tsupport_slice_subset (β : ℝ × E → ℝ) (t : ℝ) :
    tsupport (fun x : E => β (t, x)) ⊆ (fun x : E => (t, x)) ⁻¹' tsupport β :=
  tsupport_comp_subset_preimage β (continuous_const.prodMk continuous_id)

variable [FiniteDimensional ℝ E]

/-- One actual radius works uniformly for every member of the smooth supported family. -/
theorem exists_uniform_radius_bumpTranslation {β : ℝ × E → ℝ}
    (hs : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, ∀ a : E, ‖a‖ < ε →
      ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
        (∀ x, d x = x + β (t, x) • a) ∧
        ∀ x ∉ tsupport (fun y : E => β (t, y)), d x = x := by
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hs (by simp)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨((k : ℝ) + 1)⁻¹, inv_pos.mpr hkpos, ?_⟩
  intro t a ha
  have hmul : ((k : ℝ) + 1) * ‖a‖ < 1 := by
    calc
      ((k : ℝ) + 1) * ‖a‖ < ((k : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ :=
        mul_lt_mul_of_pos_left ha hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hsmall : k * ‖a‖₊ < 1 := by
    have hr : (k : ℝ) * ‖a‖ < 1 := by nlinarith [norm_nonneg a]
    exact hr
  have hslice : ContDiff ℝ ∞ (fun x : E => β (t, x)) :=
    hs.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨bumpTranslation hslice (lipschitzWith_slice hk t) a hsmall, fun _ => rfl, ?_⟩
  intro x hx
  apply bumpTranslation_eq_of_zero
  by_contra hne
  exact hx (subset_tsupport (fun y : E => β (t, y)) hne)

end Wikipedia.SmoothSixDPoincare.SmallPerturbation
