import Wikipedia.HopfProblem.EllipticEquivariantLocalModel
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackLocal

/-!
# Native charts of the finite elliptic quotient

The actual finite quotient is a local biholomorphism for its original
complex atlas.  In each selected quotient chart, its coordinate map from
the selected upstairs chart is literally the identity.  Consequently the
actual coordinate differential, determinant, and volume pullback are the
identity, one, and the original volume form, respectively.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts

open TrianglePeriodFamily.Canonical SpecialPeriods

local notation "I" => modelWithCornersSelf ℂ Model

variable {j : Kind} (D : Equivariant.Data j) (v : Lattice) (hv : AdmissibleTwist j v)

local instance familyChartedSpace : ChartedSpace Model D.TotalSpace :=
  D.periods.totalChartedSpace

local instance familyManifold : IsManifold I ω D.TotalSpace :=
  D.periods.totalSpace_isManifold

local instance quotientChartedSpace : ChartedSpace Model (D.Space v hv) :=
  D.chartedSpace v hv

local instance quotientManifold : IsManifold I ω (D.Space v hv) := D.isManifold v hv

/-- The original covering lift with its already proved analytic inverse. -/
def localInversePartialDiffeomorph (a : D.TotalSpace) :
    PartialDiffeomorph I I (D.Space v hv) D.TotalSpace ω where
  __ := D.localInverse v hv a
  contMDiffOn_toFun := D.localInverse_holomorphic v hv a
  contMDiffOn_invFun := by
    change ContMDiffOn I I ω
      ((D.localInverse v hv a).symm : D.TotalSpace → D.Space v hv)
      (D.localInverse v hv a).target
    rw [D.localInverse_symm]
    exact (D.quotient_holomorphic v hv).contMDiffOn

/-- Local biholomorphy is proved for the actual finite quotient map. -/
theorem quotient_isLocalDiffeomorph : IsLocalDiffeomorph I I ω (D.quotient v hv) := by
  intro a
  let := D.action v hv.1
  have ha : a ∈ (localInversePartialDiffeomorph D v hv a).target :=
    (D.quotientCoveringMap v hv).isCoveringMap.isLocalHomeomorph.self_mem_localInverseAt_target
  have he := (localInversePartialDiffeomorph D v hv a).symm.isLocalDiffeomorphAt I I ω ha
  change IsLocalDiffeomorphAt I I ω
    ((D.localInverse v hv a).symm : D.TotalSpace → D.Space v hv) a at he
  rw [D.localInverse_symm] at he
  exact he

/-- The upstairs point used by the original preferred quotient chart. -/
def representative (y : D.Space v hv) : D.TotalSpace := by
  letI := D.action v hv.1
  exact CoveringQuotient.representative (D.quotientCoveringMap v hv) y

@[simp] theorem quotient_representative (y : D.Space v hv) :
    D.quotient v hv (representative D v hv y) = y := by
  let := D.action v hv.1
  exact CoveringQuotient.project_representative (D.quotientCoveringMap v hv) y

/-- The native local lift used by a specified downstairs preferred chart. -/
def lift (y x : D.Space v hv) : D.TotalSpace :=
  D.localInverse v hv (representative D v hv y) x

/-- This equality records the original quotient chart, without replacing
the selected atlas by a transported one. -/
theorem chart_eq (y : D.Space v hv) :
    chartAt Model y = (D.localInverse v hv (representative D v hv y)).trans
      (chartAt Model (representative D v hv y)) := rfl

theorem chart_source (y x : D.Space v hv) :
    x ∈ (chartAt Model y).source ↔
      x ∈ (D.localInverse v hv (representative D v hv y)).source ∧
        lift D v hv y x ∈ (chartAt Model (representative D v hv y)).source := Iff.rfl

theorem quotient_lift (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) :
    D.quotient v hv (lift D v hv y x) = x :=
  D.quotient_localInverse v hv _ ((chart_source D v hv y x).mp hx).1

theorem lift_mem_familyChart (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    lift D v hv y x ∈ (chartAt Model (representative D v hv y)).source :=
  ((chart_source D v hv y x).mp hx).2

@[simp] theorem chart_lift (y x : D.Space v hv) :
    chartAt Model (representative D v hv y) (lift D v hv y x) =
      chartAt Model y x := rfl

/-- The inverse of the actual quotient chart is the quotient of the
inverse upstairs chart. -/
theorem chart_symm (y : D.Space v hv) :
    ((chartAt Model y).symm : Model → D.Space v hv) =
      D.quotient v hv ∘ (chartAt Model (representative D v hv y)).symm := by
  let := D.action v hv.1
  exact CoveringQuotient.chart_symm (D.quotientCoveringMap v hv) y

/-- The quotient in the two matched native charts is exactly the identity
on the whole native quotient-chart target. -/
theorem coordinate_eq (y : D.Space v hv) (u : Model)
    (hu : u ∈ (chartAt Model y).target) :
    (chartAt Model y ∘ D.quotient v hv ∘
      (chartAt Model (representative D v hv y)).symm) u = u := by
  change chartAt Model y ((D.quotient v hv ∘
    (chartAt Model (representative D v hv y)).symm) u) = u
  rw [← chart_symm D v hv y]
  exact (chartAt Model y).right_inv hu

theorem coordinate_eventuallyEq (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    (chartAt Model y ∘ D.quotient v hv ∘
      (chartAt Model (representative D v hv y)).symm) =ᶠ[𝓝 (chartAt Model y x)]
        (fun u : Model => u) := by
  filter_upwards [(chartAt Model y).open_target.mem_nhds
    ((chartAt Model y).map_source hx)] with u hu
  exact coordinate_eq D v hv y u hu

/-- The actual Fréchet derivative of the matched coordinate map is the
identity at every point of the full chart source. -/
theorem coordinate_fderiv (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    fderiv ℂ (chartAt Model y ∘ D.quotient v hv ∘
      (chartAt Model (representative D v hv y)).symm) (chartAt Model y x) =
        ContinuousLinearMap.id ℂ Model := by
  rw [(coordinate_eventuallyEq D v hv y x hx).fderiv_eq]
  exact fderiv_id

/-- The determinant used by canonical pullback is the determinant of the
actual coordinate derivative, not an assigned character. -/
theorem chartDerivative_eq_id (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    Pullback.chartDerivative (D.quotient v hv)
      (achart Model (representative D v hv y)) (achart Model y) (lift D v hv y x) =
        ContinuousLinearMap.id ℂ Model := by
  change fderiv ℂ (chartAt Model y ∘ D.quotient v hv ∘
    (chartAt Model (representative D v hv y)).symm)
      (chartAt Model (representative D v hv y) (lift D v hv y x)) = _
  rw [chart_lift]
  exact coordinate_fderiv D v hv y x hx

theorem chartDeterminant_eq_one (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    Pullback.chartDeterminant (D.quotient v hv)
      (achart Model (representative D v hv y)) (achart Model y) (lift D v hv y x) = 1 := by
  rw [Pullback.chartDeterminant, chartDerivative_eq_id D v hv y x hx]
  exact LinearMap.det_id

theorem volume_pullback (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    volume.compContinuousLinearMap
      (Pullback.chartDerivative (D.quotient v hv)
        (achart Model (representative D v hv y)) (achart Model y) (lift D v hv y x)) =
      volume := by
  rw [chartDerivative_eq_id D v hv y x hx]
  rfl

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts
