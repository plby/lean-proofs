import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul

/-!
# Small localized perturbations avoiding a lower-dimensional smooth image

The bad translation parameters form a smooth image of the product of the
two source manifolds. Its dimension bound gives actual arbitrarily small
good parameters. A smooth cutoff localizes the perturbation while preserving
all points where the cutoff vanishes.

This supplies a local general-position ingredient, not a Whitney trick or
a handle-cancellation theorem.
-/

noncomputable section

open Set
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

variable {E E' F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold J ∞ Y]
  [LindelofSpace (X × Y)]

/-- Small cutoff-weighted translations avoid a smooth image wherever the cutoff is nonzero. -/
theorem exists_small_localized_image_avoidance {f : X → F} {g : Y → F} {β : X → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hg : ContMDiff J 𝓘(ℝ, F) ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧ ∀ x, β x ≠ 0 → ∀ y, f x + β x • a ≠ g y := by
  let s : Set (X × Y) := {p | β p.1 ≠ 0}
  let bad : X × Y → F := fun p => (β p.1)⁻¹ • (g p.2 - f p.1)
  have hs : IsOpen s := isOpen_ne_fun (hβ.continuous.comp continuous_fst) continuous_const
  have hb : ContMDiffOn (I.prod J) 𝓘(ℝ, F) ∞ bad s :=
    ((hβ.comp contMDiff_fst).contMDiffOn.inv₀ (fun _ hp => hp)).smul
      ((hg.comp contMDiff_snd).sub (hf.comp contMDiff_fst)).contMDiffOn
  have hd : Module.finrank ℝ (E × E') < Module.finrank ℝ F := by
    simpa only [Module.finrank_prod] using hdim
  have hdense := GeneralPosition.dense_compl_manifold_image hs hb hd
  obtain ⟨a, ha, haε⟩ := hdense.exists_dist_lt 0 hε
  refine ⟨a, ?_, ?_⟩
  · simpa only [dist_zero_left] using haε
  · intro x hx y hxy
    apply ha
    refine ⟨(x, y), hx, ?_⟩
    change (β x)⁻¹ • (g y - f x) = a
    rw [← hxy, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hx, one_smul]

/-- If the fixed part already avoids the obstacle, the whole perturbed map avoids it. -/
theorem exists_small_relative_image_avoidance {f : X → F} {g : Y → F} {β : X → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, F) ∞ f) (hg : ContMDiff J 𝓘(ℝ, F) ∞ g)
    (hβ : ContMDiff I 𝓘(ℝ, ℝ) ∞ β)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ F)
    (hfixed : ∀ x, β x = 0 → f x ∉ range g) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : F, ‖a‖ < ε ∧
      ContMDiff I 𝓘(ℝ, F) ∞ (fun x => f x + β x • a) ∧
      Disjoint (range (fun x => f x + β x • a)) (range g) ∧
      ∀ x, β x = 0 → f x + β x • a = f x := by
  obtain ⟨a, ha, havoid⟩ := exists_small_localized_image_avoidance hf hg hβ hdim hε
  refine ⟨a, ha, hf.add (hβ.smul contMDiff_const), ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro z ⟨x, rfl⟩ ⟨y, hy⟩
    by_cases hx : β x = 0
    · apply hfixed x hx
      exact ⟨y, by simpa only [hx, zero_smul, add_zero] using hy⟩
    · exact havoid x hx y hy.symm
  · intro x hx
    rw [hx, zero_smul, add_zero]

end Wikipedia.SmoothSixDPoincare
