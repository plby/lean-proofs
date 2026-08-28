import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionTriangleBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriod

/-!
# Joint holomorphicity of the actual descended triangle-family action

The original quotient covering, multiplied by the parameter line,
detects holomorphicity for the existing varying-period quotient atlas.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Triangle

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)
  (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

local notation "IF" => modelWithCornersSelf ℂ (V × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The original triangle quotient carries a jointly holomorphic
vertical action of the additive complex line. -/
theorem jointFlow_holomorphic :
    letI := D.chartedSpace hq
    ContMDiff ((IF).prod I₁) IF ω
      (fun x : D.Space × ℂ => flow D x.2 x.1) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace hq
  have hl := CanonicalProduct.isLocalDiffeomorph_prodLine
    (D.quotient_isLocalDiffeomorph hq)
  have hs : Function.Surjective
      (fun x : D.TotalSpace × ℂ => (D.quotient x.1, x.2)) := by
    rintro ⟨y, s⟩
    obtain ⟨x, rfl⟩ := D.quotient_surjective y
    exact ⟨(x, s), rfl⟩
  apply contMDiff_of_comp_localDiffeomorph ((IF).prod I₁) ((IF).prod I₁) IF hl hs
  change ContMDiff ((IF).prod I₁) IF ω
    (fun x : D.TotalSpace × ℂ => flow D x.2 (D.quotient x.1))
  simp_rw [flow_quotient]
  exact (D.quotient_holomorphic hq).comp (Period.jointFlow_holomorphic D.periods)

theorem flow_holomorphic (s : ℂ) :
    letI := D.chartedSpace hq
    ContMDiff IF IF ω (flow D s) := by
  let := D.chartedSpace hq
  have hi : ContMDiff IF ((IF).prod I₁) ω (fun x : D.Space => (x, s)) :=
    contMDiff_id.prodMk contMDiff_const
  have hh := (jointFlow_holomorphic D hq).comp hi
  simpa only [Function.comp_def] using hh

/-- The actual inverse is the opposite translation, with the same
already constructed quotient complex structure. -/
def flowBiholomorph (s : ℂ) :
    letI := D.chartedSpace hq
    Diffeomorph IF IF D.Space D.Space ω := by
  letI := D.chartedSpace hq
  exact {
    toFun := flow D s
    invFun := flow D (-s)
    left_inv := fun x => by rw [← flow_add, neg_add_cancel, flow_zero]
    right_inv := fun x => by rw [← flow_add, add_neg_cancel, flow_zero]
    contMDiff_toFun := flow_holomorphic D hq s
    contMDiff_invFun := flow_holomorphic D hq (-s) }

@[simp] theorem flowBiholomorph_apply (s : ℂ) (x : D.Space) :
    letI := D.chartedSpace hq
    flowBiholomorph D hq s x = flow D s x := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Triangle
