import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticParametrization

/-!
# The actual elliptic projection equations in the global threefold

The original full-filling charts compose with the inverse of the genuine
global parametrization to give analytic partial charts for the existing
glued atlas. In these charts the global sphere projection has the literal
equation `u.1 ^ j.order`. Its actual transverse projection has order three
or four at every point of the central fibre.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open EllipticFilling

local notation "FM" => ℂ × ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ FM

attribute [local instance] specialEllipticPieceChartedSpace
  specialFullFillingChartedSpace Threefold.chartedSpace

/-- An original full-filling chart, retaining its actual analytic forward
and inverse maps as a partial diffeomorphism. -/
def nativeFillingChart (j : Elliptic.Kind) (y : SpecialFullFilling j) :
    PartialDiffeomorph IF IF (SpecialFullFilling j) FM ω := by
  letI : IsManifold IF ω (SpecialFullFilling j) :=
    (specialFullFilling_construction j).2.2.1
  exact
    { toPartialEquiv := (chartAt FM y).toPartialEquiv
      open_source := (chartAt FM y).open_source
      open_target := (chartAt FM y).open_target
      contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y)
      contMDiffOn_invFun :=
        contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas y) }

@[simp] theorem nativeFillingChart_apply (j : Elliptic.Kind)
    (y x : SpecialFullFilling j) : nativeFillingChart j y x = chartAt FM y x := rfl

@[simp] theorem nativeFillingChart_symm_apply (j : Elliptic.Kind)
    (y : SpecialFullFilling j) (u : FM) :
    (nativeFillingChart j y).symm u = (chartAt FM y).symm u := rfl

@[simp] theorem nativeFillingChart_source (j : Elliptic.Kind) (y : SpecialFullFilling j) :
    (nativeFillingChart j y).source = (chartAt FM y).source := rfl

@[simp] theorem nativeFillingChart_target (j : Elliptic.Kind) (y : SpecialFullFilling j) :
    (nativeFillingChart j y).target = (chartAt FM y).target := rfl

/-- An analytic chart for the unchanged global atlas, obtained from an
actual full-filling chart and the inverse of its genuine parametrization. -/
def projectionChart (j : Elliptic.Kind) (y : SpecialFullFilling j) :
    PartialDiffeomorph IF IF Threefold.Space FM ω :=
  (fullParametrization j).symm.trans (nativeFillingChart j y)

theorem projectionChart_mem_source (j : Elliptic.Kind) (y : SpecialFullFilling j)
    (hy : y ∈ (fullParametrization j).source) :
    fullParametrization j y ∈ (projectionChart j y).source := by
  refine ⟨(fullParametrization j).map_source' hy, ?_⟩
  change (fullParametrization j).symm (fullParametrization j y) ∈ (chartAt FM y).source
  have he : (fullParametrization j).symm (fullParametrization j y) = y :=
    (fullParametrization j).left_inv' hy
  rw [he]
  exact mem_chart_source FM y

theorem projectionChart_apply (j : Elliptic.Kind) (y : SpecialFullFilling j)
    (hy : y ∈ (fullParametrization j).source) :
    projectionChart j y (fullParametrization j y) = chartAt FM y y := by
  change chartAt FM y ((fullParametrization j).symm (fullParametrization j y)) = _
  have he : (fullParametrization j).symm (fullParametrization j y) = y :=
    (fullParametrization j).left_inv' hy
  rw [he]

theorem projectionChart_source_subset (j : Elliptic.Kind) (y : SpecialFullFilling j) :
    (projectionChart j y).source ⊆
      (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) := by
  intro x hx
  rw [← fullParametrization_target]
  exact hx.1

/-- The literal projection formula on the entire target of every actual
global elliptic chart. -/
theorem sphereChart_projectionSphere_projectionChart_symm (j : Elliptic.Kind)
    (y : SpecialFullFilling j) (u : FM) (hu : u ∈ (projectionChart j y).target) :
    sphereChart j (Threefold.projectionSphere ((projectionChart j y).symm u)) =
      u.1 ^ j.order := by
  change sphereChart j (Threefold.projectionSphere
    (fullParametrization j ((chartAt FM y).symm u))) = _
  exact (sphereChart_projectionSphere_fullParametrization j _ hu.2).trans
    (specialFullFilling_projection_chart j y u hu.1)

/-- The reduced central support is the actual first-coordinate hyperplane
in these global projection charts. -/
theorem projectionChart_coordinate_zero_iff (j : Elliptic.Kind)
    (y : SpecialFullFilling j) (u : FM) (hu : u ∈ (projectionChart j y).target) :
    sphereChart j (Threefold.projectionSphere ((projectionChart j y).symm u)) = 0 ↔
      u.1 = 0 := by
  rw [sphereChart_projectionSphere_projectionChart_symm j y u hu]
  exact pow_eq_zero_iff j.order_pos.ne'

/-- Every point of the actual global elliptic patch has an analytic chart
for the existing global atlas with the original literal power equation. -/
theorem exists_projectionChart (j : Elliptic.Kind) (x : Threefold.Space)
    (hx : x ∈ (Threefold.liftedPatch (some (some j)) : Set Threefold.Space)) :
    ∃ e : PartialDiffeomorph IF IF Threefold.Space FM ω,
      x ∈ e.source ∧
      e.source ⊆ (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) ∧
      ∀ u ∈ e.target,
        sphereChart j (Threefold.projectionSphere (e.symm u)) = u.1 ^ j.order := by
  have hxt : x ∈ (fullParametrization j).target := by
    simpa only [fullParametrization_target] using hx
  let y := (fullParametrization j).symm x
  have hys : y ∈ (fullParametrization j).source :=
    (fullParametrization j).symm.map_source' hxt
  have hpy : fullParametrization j y = x := (fullParametrization j).right_inv' hxt
  refine ⟨projectionChart j y, ?_, projectionChart_source_subset j y,
    sphereChart_projectionSphere_projectionChart_symm j y⟩
  rw [← hpy]
  exact projectionChart_mem_source j y hys

/-- At a zero of the actual elliptic base coordinate, that same genuine
chart places the central point on its first-coordinate hyperplane. -/
theorem exists_central_projectionChart (j : Elliptic.Kind) (x : Threefold.Space)
    (hx : x ∈ (Threefold.liftedPatch (some (some j)) : Set Threefold.Space))
    (hzero : sphereChart j (Threefold.projectionSphere x) = 0) :
    ∃ e : PartialDiffeomorph IF IF Threefold.Space FM ω,
      x ∈ e.source ∧ (e x).1 = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some (some j)) : Set Threefold.Space) ∧
      ∀ u ∈ e.target,
        sphereChart j (Threefold.projectionSphere (e.symm u)) = u.1 ^ j.order := by
  obtain ⟨e, hxs, hes, hp⟩ := exists_projectionChart j x hx
  refine ⟨e, hxs, ?_, hes, hp⟩
  apply (pow_eq_zero_iff j.order_pos.ne').mp
  rw [← hp (e x) (e.map_source' hxs)]
  have he : e.symm (e x) = x := e.left_inv' hxs
  rw [he]
  exact hzero

/-- The actual global sphere projection on a transverse line in the
global chart, measured in the original elliptic sphere coordinate. -/
def globalTransverseProjection (j : Elliptic.Kind) (y : SpecialFullFilling j)
    (z : ℂ) : ℂ :=
  sphereChart j (Threefold.projectionSphere
    ((projectionChart j y).symm (z, (chartAt FM y y).2)))

/-- Near the chart's center, this actual global transverse map agrees
with the original full-filling transverse projection. -/
theorem globalTransverseProjection_eventuallyEq (j : Elliptic.Kind)
    (y : SpecialFullFilling j) (hy : y ∈ (fullParametrization j).source) :
    globalTransverseProjection j y =ᶠ[𝓝 (chartAt FM y y).1]
      specialTransverseProjection j y := by
  have ht : chartAt FM y y ∈ (projectionChart j y).target := by
    rw [← projectionChart_apply j y hy]
    exact (projectionChart j y).map_source' (projectionChart_mem_source j y hy)
  have hn := (projectionChart j y).open_target.mem_nhds ht
  have hc : ContinuousAt (fun z : ℂ => (z, (chartAt FM y y).2))
      (chartAt FM y y).1 := continuousAt_id.prodMk continuousAt_const
  have he : ∀ᶠ z in 𝓝 (chartAt FM y y).1,
      (z, (chartAt FM y y).2) ∈ (projectionChart j y).target := hc hn
  filter_upwards [he] with z hz
  change sphereChart j (Threefold.projectionSphere
      (fullParametrization j ((chartAt FM y).symm (z, (chartAt FM y y).2)))) =
    (specialFullFillingProjection j ((chartAt FM y).symm (z, (chartAt FM y y).2)) : ℂ)
  exact sphereChart_projectionSphere_fullParametrization j _ hz.2

/-- The actual global projection has exact transverse multiplicity three
or four at every point of the central filling fibre. -/
theorem globalTransverseProjection_central_order (j : Elliptic.Kind)
    (y : SpecialFullFilling j)
    (hy : specialFullFillingProjection j y = Elliptic.discZero) :
    analyticOrderAt (globalTransverseProjection j y) 0 = (j.order : ℕ∞) := by
  have hc : (chartAt FM y y).1 = 0 :=
    (specialFullFilling_central_chart j y y (mem_chart_source FM y)).mp hy
  have he := globalTransverseProjection_eventuallyEq j y
    (mem_fullParametrization_source_of_central j hy)
  rw [hc] at he
  rw [analyticOrderAt_congr he]
  exact specialFullFilling_central_order j y hy

theorem globalTransverseProjection_order_three (y : SpecialFullFilling .three)
    (hy : specialFullFillingProjection .three y = Elliptic.discZero) :
    analyticOrderAt (globalTransverseProjection .three y) 0 = 3 := by
  simpa [Elliptic.Kind.order] using globalTransverseProjection_central_order .three y hy

theorem globalTransverseProjection_order_four (y : SpecialFullFilling .four)
    (hy : specialFullFillingProjection .four y = Elliptic.discZero) :
    analyticOrderAt (globalTransverseProjection .four y) 0 = 4 := by
  simpa [Elliptic.Kind.order] using globalTransverseProjection_central_order .four y hy

/-- At any noncentral point of the actual global elliptic patch, the
projection minus its value has transverse order one. -/
theorem globalTransverseProjection_noncentral_order (j : Elliptic.Kind)
    (y : SpecialFullFilling j) (hys : y ∈ (fullParametrization j).source)
    (hy : specialFullFillingProjection j y ≠ Elliptic.discZero) :
    analyticOrderAt (fun z : ℂ => globalTransverseProjection j y z -
      sphereChart j (Threefold.projectionSphere (fullParametrization j y)))
      (chartAt FM y y).1 = 1 := by
  have he : (fun z : ℂ => globalTransverseProjection j y z -
      sphereChart j (Threefold.projectionSphere (fullParametrization j y)))
      =ᶠ[𝓝 (chartAt FM y y).1]
      (fun z : ℂ => specialTransverseProjection j y z -
        (specialFullFillingProjection j y : ℂ)) := by
    filter_upwards [globalTransverseProjection_eventuallyEq j y hys] with z hz
    rw [hz, sphereChart_projectionSphere_fullParametrization j y hys]
  rw [analyticOrderAt_congr he]
  exact specialFullFilling_noncentral_order j y hy

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
