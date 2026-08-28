import Wikipedia.HopfProblem.TrianglePeriodFamilyQuotient
import Wikipedia.HopfProblem.PeriodFamilyFibreImmersion
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# The actual tori and zero section in the descended triangle family

Each quotient fibre is identified with the original complex period torus,
not merely with an abstract compact space.  Its inclusion is holomorphic
and an immersion for the constructed quotient atlas.  The integral
monodromy fixes zero, so the actual holomorphic zero section descends.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Data

open SpecialPeriods

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
    (D : TrianglePeriodFamily.Data V B)

/-- The original complex period torus maps to the actual descended family. -/
def fibreInclusion (b : B) : (D.periods.point b).Torus → D.Space :=
  D.quotient ∘ D.periods.fibreInclusion b

@[simp] theorem projection_fibreInclusion (b : B) (z : (D.periods.point b).Torus) :
    D.projection (D.fibreInclusion b z) = D.baseQuotient b := rfl

theorem fibreInclusion_continuous (b : B) : Continuous (D.fibreInclusion b) :=
  D.quotient_continuous.comp
    (continuous_const.prodMk (D.periods.torusHomeomorph b).symm.continuous)

variable (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)

/-- The full quotient fibre over a chosen base lift is the actual complex
period torus at that lift, with its original quotient topology. -/
def fibreHomeomorph (b : B) :
    (D.periods.point b).Torus ≃ₜ (D.projection ⁻¹' {D.baseQuotient b}) := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  exact (D.periods.torusHomeomorph b).symm.trans
    (DiagonalQuotient.fibreHomeomorphOver (F := RealTorus₄) hq b).symm

@[simp] theorem fibreHomeomorph_coe (b : B) (z : (D.periods.point b).Torus) :
    (D.fibreHomeomorph hq b z : D.Space) = D.fibreInclusion b z := by
  let := triangleTorusAction
  let := triangleTorusAction_continuous
  change ((DiagonalQuotient.fibreHomeomorphOver (F := RealTorus₄) hq b).symm
    ((D.periods.torusHomeomorph b).symm z)).val = _
  exact DiagonalQuotient.fibreHomeomorphOver_symm_coe hq b
    ((D.periods.torusHomeomorph b).symm z)

include hq in
theorem fibreInclusion_injective (b : B) : Function.Injective (D.fibreInclusion b) := by
  intro x y hxy
  apply (D.fibreHomeomorph hq b).injective
  apply Subtype.ext
  simpa only [D.fibreHomeomorph_coe] using hxy

include hq in
theorem fibreInclusion_range (b : B) :
    range (D.fibreInclusion b) = D.projection ⁻¹' {D.baseQuotient b} := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact D.projection_fibreInclusion b z
  · intro hy
    refine ⟨(D.fibreHomeomorph hq b).symm ⟨y, hy⟩, ?_⟩
    have he := congrArg Subtype.val ((D.fibreHomeomorph hq b).apply_symm_apply ⟨y, hy⟩)
    simpa only [D.fibreHomeomorph_coe] using he

include hq in
theorem fibreInclusion_isEmbedding (b : B) : IsEmbedding (D.fibreInclusion b) := by
  have h := IsEmbedding.subtypeVal.comp (D.fibreHomeomorph hq b).isEmbedding
  convert h using 1
  funext z
  exact (D.fibreHomeomorph_coe hq b z).symm

include hq in
theorem fibreInclusion_isClosedEmbedding [T2Space D.Space] (b : B) :
    IsClosedEmbedding (D.fibreInclusion b) :=
  (D.fibreInclusion_continuous b).isClosedEmbedding (D.fibreInclusion_injective hq b)

section Analytic

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

theorem fibreInclusion_holomorphic (b : B) :
    letI := D.chartedSpace hq
    ContMDiff (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (D.fibreInclusion b) := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace hq
  exact (D.quotient_holomorphic hq).comp (D.periods.fibreInclusion_holomorphic b)

/-- The actual complex torus inclusion has the expected normal-form
immersion, with the base model as its complement. -/
theorem fibreInclusion_isImmersionOfComplement (b : B) :
    letI := D.chartedSpace hq
    Manifold.IsImmersionOfComplement V (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (D.fibreInclusion b) := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.immersion_project (D.quotientCoveringMap hq)
    D.totalAction_holomorphic (D.periods.fibreInclusion_holomorphic b).continuous
    (D.periods.fibreInclusion_isImmersionOfComplement b)

theorem fibreInclusion_isSmoothEmbedding (b : B) :
    letI := D.chartedSpace hq
    Manifold.IsSmoothEmbedding (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω (D.fibreInclusion b) := by
  let := D.chartedSpace hq
  exact ⟨(D.fibreInclusion_isImmersionOfComplement hq b).isImmersion,
    D.fibreInclusion_isEmbedding hq b⟩

end Analytic

/-- The genuine zero section, descended using the proved linear monodromy. -/
def zeroSection : D.BaseSpace → D.Space := by
  let := D.totalAction
  refine Quotient.lift (fun b : B => D.quotient (D.periods.zeroSection b)) ?_
  rintro b b' ⟨g, hg⟩
  rw [← hg, ← D.totalAction_zeroSection, D.quotient_smul]

@[simp] theorem zeroSection_baseQuotient (b : B) :
    D.zeroSection (D.baseQuotient b) = D.quotient (D.periods.zeroSection b) := rfl

@[simp] theorem projection_zeroSection (b : D.BaseSpace) :
    D.projection (D.zeroSection b) = b := by
  induction b using Quotient.inductionOn with
  | h b => rfl

theorem zeroSection_injective : Function.Injective D.zeroSection :=
  Function.LeftInverse.injective D.projection_zeroSection

theorem zeroSection_continuous : Continuous D.zeroSection := by
  exact isQuotientMap_quotient_mk'.continuous_iff.mpr
    (D.quotient_continuous.comp (continuous_id.prodMk continuous_const))

theorem zeroSection_isEmbedding : IsEmbedding D.zeroSection :=
  Function.LeftInverse.isEmbedding D.projection_zeroSection
    D.projection_continuous D.zeroSection_continuous

theorem zeroSection_isClosedEmbedding [T2Space D.Space] : IsClosedEmbedding D.zeroSection := by
  refine ⟨D.zeroSection_isEmbedding, ?_⟩
  have he : range D.zeroSection = {x | D.zeroSection (D.projection x) = x} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      change D.zeroSection (D.projection (D.zeroSection b)) = D.zeroSection b
      rw [D.projection_zeroSection]
    · intro hx
      exact ⟨D.projection x, hx⟩
  rw [he]
  exact isClosed_eq (D.zeroSection_continuous.comp D.projection_continuous) continuous_id

theorem zeroSection_holomorphic [IsManifold (modelWithCornersSelf ℂ V) ω B] :
    letI := D.baseChartedSpace hq
    letI := D.chartedSpace hq
    ContMDiff (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω D.zeroSection := by
  let := D.periods.totalChartedSpace
  let := D.baseChartedSpace hq
  let := D.chartedSpace hq
  apply CoveringQuotient.contMDiff_of_comp hq
    (modelWithCornersSelf ℂ (V × ComplexPlane₂)) ω
  exact (D.quotient_holomorphic hq).comp D.periods.zeroSection_holomorphic

end Wikipedia.HopfProblem.TrianglePeriodFamily.Data
