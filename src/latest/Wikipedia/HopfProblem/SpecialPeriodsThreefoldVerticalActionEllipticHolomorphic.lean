import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriod

/-!
# The elliptic vertical flow in the original quotient atlas

Joint holomorphicity descends through the actual quotient covering times
the parameter line.  In particular the finite-orbit atlas of the filling
is unchanged.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic

open Wikipedia.HopfProblem.Elliptic

local notation "IF" => modelWithCornersSelf ℂ FamilyModel
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual affine finite quotient is locally biholomorphic for its
original covering atlas. -/
theorem quotient_isLocalDiffeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace v hv
    IsLocalDiffeomorph IF IF ω (D.quotient v hv) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  exact CoveringQuotient.project_isLocalDiffeomorph
    (D.quotientCoveringMap v hv) (D.action_holomorphic v hv.1)

/-- Joint holomorphicity of the actual descended translation. -/
theorem jointFlow_holomorphic (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.chartedSpace v hv
    ContMDiff ((IF).prod I₁) IF ω
      (fun x : D.Space v hv × ℂ => flow D v hv x.2 x.1) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace v hv
  have hq := CanonicalProduct.isLocalDiffeomorph_prodLine
    (quotient_isLocalDiffeomorph D v hv)
  have hs : Function.Surjective
      (fun x : D.TotalSpace × ℂ => (D.quotient v hv x.1, x.2)) := by
    rintro ⟨y, s⟩
    obtain ⟨x, rfl⟩ := D.quotient_surjective v hv y
    exact ⟨(x, s), rfl⟩
  apply contMDiff_of_comp_localDiffeomorph ((IF).prod I₁) ((IF).prod I₁) IF hq hs
  change ContMDiff ((IF).prod I₁) IF ω
    (fun x : D.TotalSpace × ℂ => flow D v hv x.2 (D.quotient v hv x.1))
  simp_rw [flow_quotient]
  exact (D.quotient_holomorphic v hv).comp (Period.jointFlow_holomorphic D.periods)

theorem flow_holomorphic (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ) :
    letI := D.chartedSpace v hv
    ContMDiff IF IF ω (flow D v hv s) := by
  let := D.chartedSpace v hv
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.action v hv.1
  apply CoveringQuotient.contMDiff_of_comp (D.quotientCoveringMap v hv) IF ω
  change ContMDiff IF IF ω
    (fun x : D.TotalSpace => D.quotient v hv (Period.flow D.periods s x))
  exact (D.quotient_holomorphic v hv).comp (Period.flow_holomorphic D.periods s)

/-- Each vertical translation is an actual biholomorphism; its inverse
is translation by the opposite complex parameter. -/
def flowBiholomorph (v : Lattice) (hv : AdmissibleTwist j v) (s : ℂ) :
    letI := D.chartedSpace v hv
    Diffeomorph IF IF (D.Space v hv) (D.Space v hv) ω := by
  letI := D.chartedSpace v hv
  exact {
    toFun := flow D v hv s
    invFun := flow D v hv (-s)
    left_inv := flow_neg_flow D v hv s
    right_inv := flow_flow_neg D v hv s
    contMDiff_toFun := flow_holomorphic D v hv s
    contMDiff_invFun := flow_holomorphic D v hv (-s) }

@[simp] theorem flowBiholomorph_apply (v : Lattice) (hv : AdmissibleTwist j v)
    (s : ℂ) (x : D.Space v hv) :
    letI := D.chartedSpace v hv
    flowBiholomorph D v hv s x = flow D v hv s x := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic
