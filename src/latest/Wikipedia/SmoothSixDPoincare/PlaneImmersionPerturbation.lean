import Wikipedia.SmoothSixDPoincare.PlaneSingularParameters
import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension

/-!
# Arbitrarily small affine immersion perturbations of a plane map

The bad parameters lie in two smooth images of dimension `dim F + 3`.
The parameter space has dimension `2 * dim F`, so its bad subset has dense
complement when `dim F ≥ 4`. This yields actual everywhere-injective
Fréchet derivatives for a small affine perturbation.
-/

noncomputable section

open Set
open scoped ContDiff Manifold ENNReal

namespace Wikipedia.SmoothSixDPoincare.PlaneImmersion

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The singular parameters occupy at most `dim F + 3` dimensions. -/
theorem dimH_bad_parameters_le {f : Plane → F} (hf : ContDiff ℝ ∞ f) :
    dimH (range (badFirst f) ∪ range (badSecond f)) ≤
      (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
  have hfirst : dimH (range (badFirst f)) ≤ (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [← image_univ]
    exact GeneralPosition.dimH_image_manifold_le isOpen_univ
      (contDiff_badFirst hf).contMDiff.contMDiffOn
  have hsecond : dimH (range (badSecond f)) ≤ (Module.finrank ℝ (Plane × (ℝ × F)) : ℝ≥0∞) := by
    rw [← image_univ]
    exact GeneralPosition.dimH_image_manifold_le isOpen_univ
      (contDiff_badSecond hf).contMDiff.contMDiffOn
  rw [dimH_union]
  exact max_le hfirst hsecond

/-- The complement of all singular parameters is dense in the actual two-column parameter space. -/
theorem dense_good_parameters {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 4 ≤ Module.finrank ℝ F) : Dense (range (badFirst f) ∪ range (badSecond f))ᶜ := by
  have hd : Module.finrank ℝ (Plane × (ℝ × F)) < Module.finrank ℝ (F × F) := by
    change Module.finrank ℝ ((ℝ × ℝ) × (ℝ × F)) < Module.finrank ℝ (F × F)
    simp only [Module.finrank_prod, Module.finrank_self]
    omega
  exact dense_compl_of_dimH_lt_finrank
    ((dimH_bad_parameters_le hf).trans_lt (Nat.cast_lt.mpr hd))

/-- A smooth plane map into dimension at least four has an arbitrarily small affine perturbation
whose actual derivative is injective at every point. -/
theorem exists_small_affine_immersion {f : Plane → F} (hf : ContDiff ℝ ∞ f)
    (hdim : 4 ≤ Module.finrank ℝ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : F × F, ‖A‖ < ε ∧ ContDiff ℝ ∞ (perturb f A) ∧
      ∀ x, Function.Injective (fderiv ℝ (perturb f A) x) := by
  obtain ⟨A, hA, hnorm⟩ := (dense_good_parameters hf hdim).exists_dist_lt 0 hε
  refine ⟨A, ?_, ?_, ?_⟩
  · simpa only [dist_zero_left] using hnorm
  · exact (contDiff_perturb_family hf).comp (contDiff_const.prodMk contDiff_id)
  · intro x
    rw [fderiv_perturb hf]
    exact injective_add_linearMap_of_not_bad f hA x

end Wikipedia.SmoothSixDPoincare.PlaneImmersion
