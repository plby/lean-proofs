import Wikipedia.NoExoticSixSphere.OrthogonalIndexEstimate

/-! # The rotating sine-field variation equals an exponential sandwich -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.OrthogonalTestFieldSandwich

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform
open NoExoticSixSphere.OrthogonalPaths NoExoticSixSphere.OrthogonalExponential
open NoExoticSixSphere.SkewConjugation NoExoticSixSphere.OrthogonalIndexTestField
open NoExoticSixSphere.OrthogonalIndexTransport

variable {d : ℕ}

local instance sandwichNormedAlgebraRat :
    NormedAlgebra ℚ (Vector d →L[ℝ] Vector d) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Vector d →L[ℝ] Vector d)

theorem conjugate_smul (a : OrthogonalOperators d) (c : ℝ) (K : SkewOperators d) :
    conjugate a (c • K) = c • conjugate a K := by
  apply Subtype.ext
  change a.val.val * (c • K.val) * (inverse a).val.val =
    c • (a.val.val * K.val * (inverse a).val.val)
  rw [mul_smul_comm, smul_mul_assoc]

theorem exp_conjugate (a : OrthogonalOperators d) (K : SkewOperators d) :
    exp (conjugate a K) = a * exp K * a⁻¹ := by
  have hs : SemiconjBy a.val.val K.val (conjugate a K).val := by
    apply ContinuousLinearMap.ext
    intro x
    change a.val.val (K.val x) = a.val.val (K.val ((inverse a).val.val (a.val.val x)))
    rw [inverse_apply_self]
  have he : a * exp K = exp (conjugate a K) * a := by
    apply Subtype.ext
    apply Subtype.ext
    exact hs.exp_right
  calc
    exp (conjugate a K) = exp (conjugate a K) * a * a⁻¹ :=
      (mul_inv_cancel_right _ _).symm
    _ = a * exp K * a⁻¹ := congrArg (fun b : OrthogonalOperators d ↦ b * a⁻¹) he.symm

theorem family_eq_sandwich (K C : SkewOperators d) (s t : ℝ) :
    NoExoticSixSphere.OrthogonalExponentialVariation.family
      (fun r ↦ (1 : OrthogonalOperators d) * exp (r • K)) (field K C) (s, t) =
        exp ((1 / 2 : ℝ) • (t • K)) * exp ((s * Real.sin (Real.pi * t)) • C) *
          exp ((1 / 2 : ℝ) • (t • K)) := by
  have hh : t • ((-1 / 2 : ℝ) • K) = -((1 / 2 : ℝ) • (t • K)) := by
    rw [smul_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  have hprod : exp (t • K) * exp (t • ((-1 / 2 : ℝ) • K)) =
      exp ((1 / 2 : ℝ) • (t • K)) := by
    rw [smul_smul, ← exp_add_smul, smul_smul]
    congr 2
    ring
  rw [NoExoticSixSphere.OrthogonalExponentialVariation.family, one_mul,
    field, transport, smul_smul, ← conjugate_smul, exp_conjugate]
  dsimp only
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, hprod, hh, exp_neg, inv_inv]

end Wikipedia.HomotopyGroupsOfSpheres.OrthogonalTestFieldSandwich
