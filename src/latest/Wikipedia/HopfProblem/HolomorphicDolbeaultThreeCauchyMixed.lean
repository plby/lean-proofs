import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCauchyOperations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Actual mixed antiholomorphic derivatives commute

This is a consequence of the real Schwarz theorem for the second Fréchet
derivative, with arbitrary constant complex directions.  The local statement
needs only twice continuous differentiability at the point.
-/

noncomputable section

open Complex
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The real derivative of a fixed antiholomorphic directional coefficient is
the same coefficient of the actual second real derivative. -/
theorem fderiv_dbar_apply_of_contDiffAt {f : E → ℂ} {q : E}
    (hf : ContDiffAt ℝ 2 f q) (v w : E) :
    fderiv ℝ (fun x => dbar f x w) q v =
      antiPart (fderiv ℝ (fderiv ℝ f) q v) w := by
  let T : (E →L[ℝ] ℂ) →L[ℝ] ℂ :=
    (ContinuousLinearMap.apply ℝ ℂ w).comp antiPartLinear
  have h₁ : ContDiffAt ℝ 1 (fderiv ℝ f) q := hf.fderiv_right (by norm_num)
  change fderiv ℝ (T ∘ fderiv ℝ f) q v = _
  rw [(T.hasFDerivAt.comp q (h₁.differentiableAt one_ne_zero).hasFDerivAt).fderiv]
  rfl

/-- Two antiholomorphic constant-direction derivatives commute at every
twice continuously differentiable point. -/
theorem dbar_dbar_of_contDiffAt {f : E → ℂ} {q : E}
    (hf : ContDiffAt ℝ 2 f q) (v w : E) :
    dbar (fun x => dbar f x w) q v = dbar (fun x => dbar f x v) q w := by
  change antiPart (fderiv ℝ (fun x => dbar f x w) q) v =
    antiPart (fderiv ℝ (fun x => dbar f x v) q) w
  simp only [antiPart_apply, fderiv_dbar_apply_of_contDiffAt hf]
  have hs := hf.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField, le_refl])
  rw [hs v w, hs v (I • w), hs (I • v) w, hs (I • v) (I • w)]
  ring

/-- In particular, the actual differential of a smooth function is
antiholomorphically closed in all constant directions. -/
theorem dbar_dbar {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (q v w : E) :
    dbar (fun x => dbar f x w) q v = dbar (fun x => dbar f x v) q w := by
  apply dbar_dbar_of_contDiffAt (q := q) ?_ v w
  exact hf.contDiffAt.of_le (by
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree
