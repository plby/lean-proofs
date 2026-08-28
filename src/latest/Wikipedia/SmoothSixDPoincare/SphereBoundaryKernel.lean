import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The boundary tangent-kernel condition for an actual sphere extension

The defining function is `‖x‖² - 1`. Its derivative kernel is the tangent
hyperplane of the sphere. Mathlib identifies that hyperplane with the range
of the native derivative of sphere inclusion. Thus any smooth ambient
extension of an immersive sphere map has trivial common kernel with the
defining-function derivative, even if it is radially constant.
-/

noncomputable section

open Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace Wikipedia.SmoothSixDPoincare.SphereBoundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def definingFunction (x : E) : ℝ := ‖x‖ ^ 2 - 1

theorem contDiff_definingFunction : ContDiff ℝ ∞ (definingFunction (E := E)) :=
  (contDiff_id.norm_sq (𝕜 := ℝ)).sub contDiff_const

omit [InnerProductSpace ℝ E] in
theorem definingFunction_eq_zero_iff (x : E) :
    definingFunction x = 0 ↔ x ∈ Metric.sphere (0 : E) 1 := by
  simp only [definingFunction, Metric.mem_sphere, dist_zero_right]
  constructor
  · intro h
    nlinarith [norm_nonneg x]
  · intro h
    rw [h]
    norm_num

theorem fderiv_definingFunction (x : E) :
    fderiv ℝ (definingFunction (E := E)) x = 2 • innerSL ℝ x :=
  ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.sub_const 1).fderiv

theorem fderiv_definingFunction_eq_zero_iff (x v : E) :
    fderiv ℝ (definingFunction (E := E)) x v = 0 ↔ inner ℝ x v = 0 := by
  rw [fderiv_definingFunction]
  rw [two_smul, add_apply]
  change inner ℝ x v + inner ℝ x v = 0 ↔ inner ℝ x v = 0
  constructor
  · intro h
    linarith
  · intro h
    rw [h, add_zero]

variable [FiniteDimensional ℝ E] {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

omit [FiniteDimensional ℝ E] in
/-- A genuine smooth extension of an immersive sphere map satisfies the tangent common-kernel
condition needed to repair its boundary derivative. No radial derivative is assumed. -/
theorem common_kernel_of_immersive_sphere_extension {f : E → N}
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {γ : Metric.sphere (0 : E) 1 → N}
    (hext : ∀ x : Metric.sphere (0 : E) 1, f x.1 = γ x)
    (hγ : ∀ x, Function.Injective (mfderiv (𝓡 n) J γ x)) :
    ∀ y, definingFunction y = 0 → ∀ v : E, mfderiv 𝓘(ℝ, E) J f y v = 0 →
      fderiv ℝ (definingFunction (E := E)) y v = 0 → v = 0 := by
  intro y hy v hfv hρv
  let x : Metric.sphere (0 : E) 1 := ⟨y, (definingFunction_eq_zero_iff y).mp hy⟩
  have hinner : inner ℝ y v = 0 := (fderiv_definingFunction_eq_zero_iff y v).mp hρv
  have hrange : v ∈ (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : E) 1 → E) x).range := by
    rw [range_mvfderiv_subtypeVal]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hinner
  obtain ⟨w, hw⟩ := hrange
  change (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w = v at hw
  have hextfun : (f ∘ (Subtype.val : Metric.sphere (0 : E) 1 → E)) = γ := funext hext
  have hchain : mfderiv (𝓡 n) J γ x = (mfderiv 𝓘(ℝ, E) J f y).comp
      (mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) := by
    rw [← hextfun, mfderiv_comp x (hf.mdifferentiableAt (by simp))
      ((contMDiff_coe_sphere (m := (∞ : ℕ∞ω))).mdifferentiableAt (by simp))]
  have hγzero : mfderiv (𝓡 n) J γ x w = 0 := by
    rw [hchain]
    change (mfderiv 𝓘(ℝ, E) J f y)
      ((mfderiv (𝓡 n) 𝓘(ℝ, E) (Subtype.val : Metric.sphere (0 : E) 1 → E) x) w) = 0
    rw [hw]
    exact hfv
  have hwzero : w = 0 := (hγ x) (by simpa only [map_zero] using hγzero)
  rw [hwzero, map_zero] at hw
  exact hw.symm

end Wikipedia.SmoothSixDPoincare.SphereBoundary
