import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriodBasic
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapPeriodPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalProductLocal
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# Joint holomorphicity of vertical translations in varying period tori

Holomorphicity is proved in the original complex vector-cover coordinates,
then descended through that cover times the identity of the parameter
line.  The real-coordinate formula for the quotient is not used as a
replacement complex atlas.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Period

theorem vector_holomorphic : ContDiff ℂ ω vector := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_id

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IF" => modelWithCornersSelf ℂ (V × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

local instance vectorChartedSpace : ChartedSpace (V × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd V ComplexPlane₂) (B × ComplexPlane₂))

/-- The joint vector-coordinate formula is genuinely holomorphic. -/
theorem jointVectorFlow_holomorphic :
    ContMDiff ((IF).prod I₁) IF ω
      (fun x : (B × ComplexPlane₂) × ℂ => vectorFlow x.2 x.1) := by
  rw [modelWithCornersSelf_prod]
  exact (contMDiff_fst.comp contMDiff_fst).prodMk
    ((contMDiff_snd.comp contMDiff_fst).add
      (vector_holomorphic.contMDiff.comp contMDiff_snd))

variable (P : HolomorphicPeriodMap V B)
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Joint holomorphicity in the actual total-space atlas and the original
complex translation parameter. -/
theorem jointFlow_holomorphic :
    letI := P.totalChartedSpace
    ContMDiff ((IF).prod I₁) IF ω
      (fun x : P.TotalSpace × ℂ => flow P x.2 x.1) := by
  let := P.totalChartedSpace
  have hq := CanonicalProduct.isLocalDiffeomorph_prodLine
    P.quotientMap_isLocalDiffeomorph
  have hs : Function.Surjective
      (fun x : (B × ComplexPlane₂) × ℂ => (P.quotientMap x.1, x.2)) := by
    rintro ⟨y, s⟩
    obtain ⟨x, rfl⟩ := P.quotientMap_surjective y
    exact ⟨(x, s), rfl⟩
  apply contMDiff_of_comp_localDiffeomorph ((IF).prod I₁) ((IF).prod I₁) IF hq hs
  change ContMDiff ((IF).prod I₁) IF ω
    (fun x : (B × ComplexPlane₂) × ℂ => flow P x.2 (P.quotientMap x.1))
  simp_rw [flow_quotientMap]
  exact P.quotientMap_holomorphic.comp jointVectorFlow_holomorphic

theorem flow_holomorphic (s : ℂ) :
    letI := P.totalChartedSpace
    ContMDiff IF IF ω (flow P s) := by
  let := P.totalChartedSpace
  exact (jointFlow_holomorphic P).comp (contMDiff_id.prodMk contMDiff_const)

/-- Each actual vertical translation has the holomorphic inverse given
by the opposite parameter. -/
def flowBiholomorph (s : ℂ) :
    letI := P.totalChartedSpace
    Diffeomorph IF IF P.TotalSpace P.TotalSpace ω := by
  letI := P.totalChartedSpace
  exact {
    toFun := flow P s
    invFun := flow P (-s)
    left_inv := fun x => by rw [← flow_add, neg_add_cancel, flow_zero]
    right_inv := fun x => by rw [← flow_add, add_neg_cancel, flow_zero]
    contMDiff_toFun := flow_holomorphic P s
    contMDiff_invFun := flow_holomorphic P (-s) }

@[simp] theorem flowBiholomorph_apply (s : ℂ) (x : P.TotalSpace) :
    letI := P.totalChartedSpace
    flowBiholomorph P s x = flow P s x := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Period
