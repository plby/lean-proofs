import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsDifferential
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsFrame
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCauchyMixed

/-!
# Genuine smoothness and closedness of the full period-coordinate covectors

Smoothness is on the original full open covering domain. Closedness is the
actual equality of the two antiholomorphic directional derivatives in every
pair of directions; it follows from the real Schwarz theorem for the actual
smooth inverse-coordinate functions.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms

open HolomorphicDolbeaultThree

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- Literal covector values of the full frame. -/
theorem frameLinear_val (q c : Model) :
    (frameLinear P q c).val = c.1 • baseCovector.val +
      c.2 0 • dbar (coordinate P 0) q + c.2 1 • dbar (coordinate P 1) q := rfl

/-- Every constant linear combination of the actual frame covectors varies
jointly smoothly in the original base and fibre variables. -/
theorem frameLinear_contDiffOn (c : Model) :
    ContDiffOn ℝ ∞ (fun q => (frameLinear P q c).val)
      (Smooth.baseProductDomain U ComplexPlane₂) := by
  change ContDiffOn ℝ ∞ (fun q => c.1 • baseCovector.val +
    c.2 0 • dbar (coordinate P 0) q + c.2 1 • dbar (coordinate P 1) q) _
  exact (contDiffOn_const.add
    (ContDiffOn.const_smul (c.2 0) (coordinate_dbar_contDiffOn P 0))).add
      (ContDiffOn.const_smul (c.2 1) (coordinate_dbar_contDiffOn P 1))

/-- Each original full coordinate covector satisfies the genuine closed-form
equation in all pairs of native complex directions, including the base. -/
theorem coordinate_dbar_closed (j : Fin 4) (q : Model)
    (hq : q ∈ Smooth.baseProductDomain U ComplexPlane₂) (v w : Model) :
    dbar (fun y => dbar (coordinate P j) y w) q v =
      dbar (fun y => dbar (coordinate P j) y v) q w := by
  have h := (coordinate_contDiffOn P j).contDiffAt
    ((Smooth.baseProductDomain_isOpen U ComplexPlane₂).mem_nhds hq)
  have h2 : ContDiffAt ℝ 2 (coordinate P j) q :=
    h.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact dbar_dbar_of_contDiffAt h2 v w

/-- The original base covector also satisfies the actual full closed-form
equation; its coefficients are constant in these original charts. -/
theorem baseCovector_closed (q v w : Model) :
    dbar (fun _ : Model => baseCovector.val w) q v =
      dbar (fun _ : Model => baseCovector.val v) q w := by
  simp only [dbar_const, zero_apply]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms
