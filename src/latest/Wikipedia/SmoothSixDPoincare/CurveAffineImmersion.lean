import Wikipedia.SmoothSixDPoincare.WeightedDerivativePerturbation

/-!
# Small affine perturbations of smooth curves are immersive

The proved weighted-derivative argument applies with the scalar weight `t`.
Its derivative has zero kernel, so a small generic vector parameter gives an
everywhere-injective actual curve derivative in target dimension at least three.
Multiplying the weight by a compact cutoff localizes the native construction.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.CurveImmersion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

def perturb (f : ℝ → F) (a : F) : ℝ → F := WeightedPerturbation.perturb f id a

/-- A genuine small affine curve perturbation has injective derivative at every point. -/
theorem exists_small_affine_immersion {f : ℝ → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 3 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ ContDiff ℝ ∞ (perturb f a) ∧
      ∀ t, Injective (fderiv ℝ (perturb f a) t) := by
  have hd : Module.finrank ℝ ℝ + Module.finrank ℝ ℝ < Module.finrank ℝ F := by
    simp only [Module.finrank_self]
    omega
  obtain ⟨a, ha, hs, hker⟩ := WeightedPerturbation.exists_small_parameter_with_common_kernel
    (I := 𝓘(ℝ, ℝ)) (b := id) (β := id) contMDiff_id hf contDiff_id hd hε
  refine ⟨a, ha, hs, ?_⟩
  intro t u v huv
  have hz : fderiv ℝ (perturb f a) t (u - v) = 0 := by rw [map_sub, huv, sub_self]
  have hzero := ((hker t (u - v)).mp hz).2
  have huv0 : u - v = 0 := by simpa only [fderiv_id, ContinuousLinearMap.id_apply] using hzero
  exact sub_eq_zero.mp huv0

def weight (β : ℝ → ℝ) (t : ℝ) : ℝ := β t * t

theorem contDiff_weight {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (weight β) := hβ.mul contDiff_id

theorem hasCompactSupport_weight {β : ℝ → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (weight β) := hβ.mul_right (f' := id)

theorem tsupport_weight_subset (β : ℝ → ℝ) : tsupport (weight β) ⊆ tsupport β :=
  tsupport_mul_subset_left (f := β) (g := id)

theorem weight_eq_zero {β : ℝ → ℝ} {t : ℝ} (ht : β t = 0) : weight β t = 0 := by
  simp only [weight, ht, zero_mul]

end Wikipedia.SmoothSixDPoincare.CurveImmersion
