import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsCoordinates
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic

/-!
# Full antiholomorphic differential identities for the original period coordinates

The differential is the actual antiholomorphic part of the real Fréchet
derivative on `ℂ × ComplexPlane₂`. The two identities below include every
base and fibre direction. They follow from the original period equations and
the genuine holomorphy of the three original period functions.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms

open HolomorphicDolbeaultThree

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- Holomorphic factors contribute no additional antiholomorphic term. -/
theorem dbar_holomorphic_mul {f g : E → ℂ} {q : E}
    (hf : DifferentiableAt ℂ f q) (hg : DifferentiableAt ℝ g q) :
    dbar (fun w => f w * g w) q = f q • dbar g q := by
  rw [dbar, fderiv_fun_mul (hf.restrictScalars ℝ) hg, antiPart_add,
    antiPart_complex_smul, antiPart_complex_smul]
  change f q • dbar g q + g q • dbar f q = _
  rw [dbar_zero_of_differentiableAt hf, smul_zero, add_zero]

end Calculus

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The full coordinate covectors vary jointly real-smoothly in the actual
base and fibre coordinates on the original open domain. -/
theorem coordinate_dbar_contDiffOn (j : Fin 4) :
    ContDiffOn ℝ ∞ (dbar (coordinate P j))
      (Smooth.baseProductDomain U ComplexPlane₂) := by
  exact antiPartLinear.contDiff.comp_contDiffOn
    ((coordinate_contDiffOn P j).fderiv_of_isOpen
      (Smooth.baseProductDomain_isOpen U ComplexPlane₂) (by simp))

/-- The full third-coordinate differential is the stated combination of
the first two actual marked-coordinate differentials. -/
theorem dbar_coordinate_two (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    dbar (coordinate P 2) q =
      -(6 * Smooth.muValue P q.1) • dbar (coordinate P 0) q -
        Smooth.tauValue P q.1 • dbar (coordinate P 1) q := by
  have h0 := coordinate_differentiableAt P 0 q hq
  have h1 := coordinate_differentiableAt P 1 q hq
  have hm := (mu_differentiableAt P q hq).const_mul (6 : ℂ)
  have ht := tau_differentiableAt P q hq
  have hz : DifferentiableAt ℂ (fun w : ℂ × ComplexPlane₂ => w.2 0) q := by
    fun_prop
  have ha : DifferentiableAt ℝ
      (fun w => 6 * Smooth.muValue P w.1 * coordinate P 0 w) q :=
    (hm.restrictScalars ℝ).mul h0
  have hb : DifferentiableAt ℝ
      (fun w => Smooth.tauValue P w.1 * coordinate P 1 w) q :=
    (ht.restrictScalars ℝ).mul h1
  have hs : DifferentiableAt ℝ
      (fun w => 6 * Smooth.muValue P w.1 * coordinate P 0 w +
        Smooth.tauValue P w.1 * coordinate P 1 w) q := ha.add hb
  have hadd : dbar (fun w => 6 * Smooth.muValue P w.1 * coordinate P 0 w +
      Smooth.tauValue P w.1 * coordinate P 1 w) q =
      dbar (fun w => 6 * Smooth.muValue P w.1 * coordinate P 0 w) q +
        dbar (fun w => Smooth.tauValue P w.1 * coordinate P 1 w) q :=
    dbar_add ha hb
  have hsub : dbar (fun w : ℂ × ComplexPlane₂ => w.2 0 -
      (6 * Smooth.muValue P w.1 * coordinate P 0 w +
        Smooth.tauValue P w.1 * coordinate P 1 w)) q =
      dbar (fun w : ℂ × ComplexPlane₂ => w.2 0) q -
        dbar (fun w => 6 * Smooth.muValue P w.1 * coordinate P 0 w +
          Smooth.tauValue P w.1 * coordinate P 1 w) q := by
    unfold dbar antiPart
    rw [fderiv_fun_sub (hz.restrictScalars ℝ) hs, map_sub]
  rw [dbar_congr (coordinate_two_eventuallyEq P q hq), hsub,
    dbar_zero_of_differentiableAt hz,
    hadd, dbar_holomorphic_mul hm h0, dbar_holomorphic_mul ht h1]
  simp only [neg_smul]
  abel

/-- The full fourth-coordinate differential satisfies the second original
period relation, with the original holomorphic coefficients. -/
theorem dbar_coordinate_three (q : ℂ × ComplexPlane₂)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) :
    dbar (coordinate P 3) q =
      -Smooth.betaValue P q.1 • dbar (coordinate P 0) q -
        Smooth.muValue P q.1 • dbar (coordinate P 1) q := by
  have h0 := coordinate_differentiableAt P 0 q hq
  have h1 := coordinate_differentiableAt P 1 q hq
  have hb := beta_differentiableAt P q hq
  have hm := mu_differentiableAt P q hq
  have hz : DifferentiableAt ℂ (fun w : ℂ × ComplexPlane₂ => w.2 1) q := by
    fun_prop
  have ha : DifferentiableAt ℝ
      (fun w => Smooth.betaValue P w.1 * coordinate P 0 w) q :=
    (hb.restrictScalars ℝ).mul h0
  have hc : DifferentiableAt ℝ
      (fun w => Smooth.muValue P w.1 * coordinate P 1 w) q :=
    (hm.restrictScalars ℝ).mul h1
  have hs : DifferentiableAt ℝ
      (fun w => Smooth.betaValue P w.1 * coordinate P 0 w +
        Smooth.muValue P w.1 * coordinate P 1 w) q := ha.add hc
  have hadd : dbar (fun w => Smooth.betaValue P w.1 * coordinate P 0 w +
      Smooth.muValue P w.1 * coordinate P 1 w) q =
      dbar (fun w => Smooth.betaValue P w.1 * coordinate P 0 w) q +
        dbar (fun w => Smooth.muValue P w.1 * coordinate P 1 w) q :=
    dbar_add ha hc
  have hsub : dbar (fun w : ℂ × ComplexPlane₂ => w.2 1 -
      (Smooth.betaValue P w.1 * coordinate P 0 w +
        Smooth.muValue P w.1 * coordinate P 1 w)) q =
      dbar (fun w : ℂ × ComplexPlane₂ => w.2 1) q -
        dbar (fun w => Smooth.betaValue P w.1 * coordinate P 0 w +
          Smooth.muValue P w.1 * coordinate P 1 w) q := by
    unfold dbar antiPart
    rw [fderiv_fun_sub (hz.restrictScalars ℝ) hs, map_sub]
  rw [dbar_congr (coordinate_three_eventuallyEq P q hq), hsub,
    dbar_zero_of_differentiableAt hz,
    hadd, dbar_holomorphic_mul hb h0, dbar_holomorphic_mul hm h1]
  simp only [neg_smul]
  abel

/-- Literal full directional identity at an actual base point. -/
theorem dbar_coordinate_two_apply (b : U) (z : ComplexPlane₂)
    (v : ℂ × ComplexPlane₂) :
    dbar (coordinate P 2) ((b : ℂ), z) v =
      -(6 * (P.point b).val.μ) * dbar (coordinate P 0) ((b : ℂ), z) v -
        (P.point b).val.τ * dbar (coordinate P 1) ((b : ℂ), z) v := by
  rw [dbar_coordinate_two P ((b : ℂ), z) b.property]
  simp only [sub_apply, smul_apply,
    smul_eq_mul, Smooth.muValue_apply, Smooth.tauValue_apply]

/-- Literal full directional identity for the fourth actual coordinate. -/
theorem dbar_coordinate_three_apply (b : U) (z : ComplexPlane₂)
    (v : ℂ × ComplexPlane₂) :
    dbar (coordinate P 3) ((b : ℂ), z) v =
      -(P.point b).val.β * dbar (coordinate P 0) ((b : ℂ), z) v -
        (P.point b).val.μ * dbar (coordinate P 1) ((b : ℂ), z) v := by
  rw [dbar_coordinate_three P ((b : ℂ), z) b.property]
  simp only [sub_apply, smul_apply,
    smul_eq_mul, Smooth.betaValue_apply, Smooth.muValue_apply]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms
