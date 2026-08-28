import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# The cubic source coordinate used to straighten the embedded cusp

The function x cubed plus x is strictly increasing, onto, and has everywhere
positive derivative. Its actual global inverse is smooth by the analytic
inverse-function theorem. No inverse formula or smoothness is assumed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

def cubic (x : ℝ) : ℝ := x ^ 3 + x

theorem contDiff_cubic : ContDiff ℝ ∞ cubic := contDiff_id.pow 3 |>.add contDiff_id

theorem hasDerivAt_cubic (x : ℝ) : HasDerivAt cubic (3 * x ^ 2 + 1) x := by
  convert ((hasDerivAt_id x).pow 3).add (hasDerivAt_id x) using 1 <;> first | rfl | norm_num [cubic]

theorem strictMono_cubic : StrictMono cubic := by
  intro x y hxy
  have hp : x ^ 3 < y ^ 3 := (by decide : Odd 3).strictMono_pow hxy
  change x ^ 3 + x < y ^ 3 + y
  linarith

theorem surjective_cubic : Surjective cubic := by
  intro y
  let R : ℝ := |y| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpow : 0 ≤ R ^ 3 := pow_nonneg hR _
  have hleft : cubic (-R) ≤ y := by
    have hy := neg_abs_le y
    dsimp [cubic]
    rw [neg_pow]
    dsimp [R] at *
    linarith
  have hright : y ≤ cubic R := by
    have hy := le_abs_self y
    dsimp [cubic, R] at *
    linarith
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (show -R ≤ R by linarith)
    contDiff_cubic.continuous.continuousOn ⟨hleft, hright⟩
  exact ⟨x, hx⟩

theorem isLocalDiffeomorph_cubic : IsLocalDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ cubic := by
  intro x
  have hne : 3 * x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
  have hinv : (fderiv ℝ cubic x).IsInvertible := by
    refine ⟨(LinearEquiv.smulOfNeZero ℝ ℝ (3 * x ^ 2 + 1) hne).toContinuousLinearEquiv, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    change (3 * x ^ 2 + 1) * v = fderiv ℝ cubic x v
    rw [fderiv_eq_deriv_mul, (hasDerivAt_cubic x).deriv]
  obtain ⟨Φ, hx, _, hΦ⟩ := NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    isOpen_univ (mem_univ x) contDiff_cubic.contDiffOn hinv
  exact ⟨Φ, hx, fun y _ ↦ congrFun hΦ.symm y⟩

def cubicDiffeomorph : ℝ ≃ₘ[ℝ] ℝ :=
  isLocalDiffeomorph_cubic.diffeomorphOfBijective ⟨strictMono_cubic.injective, surjective_cubic⟩

theorem cubicDiffeomorph_apply (x : ℝ) : cubicDiffeomorph x = cubic x := rfl

def cubicInverse : ℝ → ℝ := cubicDiffeomorph.symm

theorem contDiff_cubicInverse : ContDiff ℝ ∞ cubicInverse :=
  cubicDiffeomorph.symm.contMDiff.contDiff

theorem cubicInverse_cubic (x : ℝ) : cubicInverse (cubic x) = x :=
  cubicDiffeomorph.symm_apply_apply x

theorem cubic_cubicInverse (x : ℝ) : cubic (cubicInverse x) = x :=
  cubicDiffeomorph.apply_symm_apply x

theorem cubicInverse_zero : cubicInverse 0 = 0 := by
  simpa only [cubic, zero_pow (by decide : 3 ≠ 0), add_zero] using cubicInverse_cubic 0

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
