import Wikipedia.HopfProblem.DegreeCollapseOrbitPreservingNormalization

/-!
# Positive scalar height changes retain the native critical geometry

Only an auxiliary height function is rescaled. Its actual native
derivative, critical set, and descending directions are proved to agree
with the original ones after the prescribed positive scalar factor.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem mfderiv_height_div_const {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (r : ℝ) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => f y / r) x =
      r⁻¹ • mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x := by
  have heq : (fun y => f y / r) = r⁻¹ • f := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact (hf.hasMFDerivAt.const_smul r⁻¹).mfderiv

theorem mvfderiv_height_div_const {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) (r : ℝ)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (fun y => f y / r) x v = mvfderiv 𝓘(ℝ, E) f x v / r := by
  have heq : (fun y => f y / r) = (fun y => r⁻¹ * f y) := by
    ext y
    simp only [div_eq_mul_inv, mul_comm]
  rw [heq, mvfderiv_fun_mul mdifferentiableAt_const hf]
  have hconst : mvfderiv 𝓘(ℝ, E) (fun _ : M => r⁻¹) x = 0 := by
    simp [mvfderiv, mfderiv_const]
  simp [hconst, div_eq_mul_inv, mul_comm]

theorem criticalPoints_height_div_const {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {r : ℝ} (hr : r ≠ 0) :
    ManifoldMorse.criticalPoints E (fun y => f y / r) = ManifoldMorse.criticalPoints E f := by
  ext x
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun y => f y / r) x = 0 ↔
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x = 0
  rw [mfderiv_height_div_const (hf.mdifferentiableAt (by simp))]
  exact smul_eq_zero.trans (or_iff_right (inv_ne_zero hr))

theorem descending_height_div_const_iff {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) {r : ℝ} (hr : 0 < r)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv 𝓘(ℝ, E) (fun y => f y / r) x v < 0 ↔ mvfderiv 𝓘(ℝ, E) f x v < 0 := by
  rw [mvfderiv_height_div_const hf r]
  rw [div_lt_iff₀ hr, zero_mul]

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
