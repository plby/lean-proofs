import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspLogCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsRegularCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspOverlap

/-!
# The unchanged cusp logarithmic cover in regular period coordinates

The actual logarithmic cover enters the actual regular upper-half-plane cover
by multiplication of the base coordinate by the triangle cusp width. Its two
complex fibre coordinates are unchanged. All maps retain their native atlases.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open CuspFamily CuspUniformization

local notation "EL" => ℂ × ComplexPlane₂
local notation "IL" => modelWithCornersSelf ℂ EL
local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂

attribute [local instance] RegularCover.coverChartedSpace

/-- The chosen actual filling radius lies in the precisely invariant cusp horodisc. -/
theorem radius_cap : CuspGeometry.data.radius ≤ Triangle.cuspRadius Triangle.width :=
  specialBaseCover_cusp_radius_bounds.2.2.le

/-- Forget only the two fibre coordinates of the actual logarithmic cover. -/
def toLogBase (x : LogDomain) : LogBase CuspGeometry.data.radius :=
  ⟨x.val.1, x.property⟩

@[simp] theorem toLogBase_coe (x : LogDomain) : (toLogBase x : ℂ) = x.val.1 := rfl

theorem toLogBase_holomorphic : ContMDiff IL I₁ ω toLogBase := by
  have hf : ContMDiff IL I₁ ω (fun x : LogDomain => x.val.1) :=
    (contDiff_fst : ContDiff ℂ ω (Prod.fst : EL → ℂ)).contMDiff.comp
      contMDiff_subtype_val
  intro x
  have he : ContMDiffAt IL I₁ ω (Subtype.val ∘ toLogBase) x ↔
      ContMDiffAt IL I₁ ω toLogBase x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hf x)

/-- The actual regular covering point with the same complex fibre vector. -/
def toRegularCover (x : LogDomain) : RegularCover.Cover :=
  (logBaseToRegular CuspGeometry.data.radius radius_cap (toLogBase x), x.val.2)

@[simp] theorem toRegularCover_base_coe (x : LogDomain) :
    (((toRegularCover x).1 : ℍ) : ℂ) = (Triangle.width : ℂ) * x.val.1 :=
  logBaseToRegular_coe CuspGeometry.data.radius radius_cap (toLogBase x)

@[simp] theorem toRegularCover_fibre (x : LogDomain) : (toRegularCover x).2 = x.val.2 :=
  rfl

theorem toRegularCover_holomorphic : ContMDiff IL IL ω toRegularCover := by
  have hb : ContMDiff IL I₁ ω
      (fun x : LogDomain => logBaseToRegular CuspGeometry.data.radius radius_cap
        (toLogBase x)) :=
    (logBaseToRegular_holomorphic CuspGeometry.data.radius radius_cap).comp
      toLogBase_holomorphic
  have hv : ContMDiff IL I₂ ω (fun x : LogDomain => x.val.2) :=
    (contDiff_snd : ContDiff ℂ ω (Prod.snd : EL → ComplexPlane₂)).contMDiff.comp
      contMDiff_subtype_val
  rw [modelWithCornersSelf_prod] at hb hv ⊢
  exact hb.prodMk hv

/-- The logarithmic cover keeps its original open-subset coordinate. -/
theorem logDomain_chart_apply (x y : LogDomain) : chartAt EL x y = y.val := rfl

/-- In the actual source and target charts the comparison is the base-width scaling. -/
theorem toRegularCover_chart_apply (x y : LogDomain) :
    chartAt EL (toRegularCover x) (toRegularCover y) =
      ((Triangle.width : ℂ) * y.val.1, y.val.2) := by
  rw [RegularCover.cover_chart_apply, toRegularCover_base_coe, toRegularCover_fibre]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
