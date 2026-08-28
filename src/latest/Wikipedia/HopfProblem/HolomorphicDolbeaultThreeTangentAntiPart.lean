import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeTangentCoordinates
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Antiholomorphic projection of native cotangent sections

The projection acts on the original dependent real cotangent fibres.  The
bundle and its charts are those in `FormsBundle`; the model covectors below
are only the underlying coordinates of each specified native fibre.  The
native coordinate identity on each original chart proves that this
pointwise projection preserves actual smooth bundle sections.
-/

noncomputable section

open TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Tangent

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Pointwise antiholomorphic projection in the original dependent
cotangent fibres, without replacing the native Hom bundle. -/
def antiPartSection {U : Opens M} (a : ∀ x : U, Forms.Covector E M (x : M)) :
    ∀ x : U, Forms.Covector E M (x : M) :=
  fun x => Forms.covectorFromModel E M (x : M)
    (antiPart (Forms.covectorAsModel E M (a x)))

@[simp] theorem antiPartSection_apply {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x : U) :
    antiPartSection E M a x = Forms.covectorFromModel E M (x : M)
      (antiPart (Forms.covectorAsModel E M (a x))) := rfl

/-- In its own native fibre the projection is exactly the original
continuous real-linear operator `antiPartLinear`. -/
@[simp] theorem antiPartSection_asModel {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x : U) :
    Forms.covectorAsModel E M (antiPartSection E M a x) =
      antiPart (Forms.covectorAsModel E M (a x)) := rfl

/-- Every projected native fibre covector is anti-complex-linear for the
original complex structure. -/
theorem antiPartSection_mem {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x : U) :
    Forms.covectorAsModel E M (antiPartSection E M a x) ∈ antiCovectors (E := E) :=
  antiPart_mem (Forms.covectorAsModel E M (a x))

theorem antiPartSection_I {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x : U) (v : E) :
    Forms.covectorAsModel E M (antiPartSection E M a x) (Complex.I • v) =
      -Complex.I * Forms.covectorAsModel E M (antiPartSection E M a x) v :=
  antiPart_I (Forms.covectorAsModel E M (a x)) v

/-- The pointwise native projection is idempotent. -/
@[simp] theorem antiPartSection_idempotent {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M)) :
    antiPartSection E M (antiPartSection E M a) = antiPartSection E M a := by
  funext x
  exact congrArg (Forms.covectorFromModel E M (x : M))
    (antiPart_idempotent (Forms.covectorAsModel E M (a x)))

/-- Native anti-complex-linear covectors are fixed by this projection. -/
theorem antiPartSection_eq_self {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M))
    (ha : ∀ x : U, Forms.covectorAsModel E M (a x) ∈ antiCovectors (E := E)) :
    antiPartSection E M a = a := by
  funext x
  exact congrArg (Forms.covectorFromModel E M (x : M)) (antiPart_eq_self (ha x))

variable [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Pointwise antiholomorphic projection preserves actual native
cotangent-section smoothness at every point of the original open set. -/
theorem antiPartSection_smoothAt {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x : U)
    (ha : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M a) x) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M (antiPartSection E M a)) x := by
  apply (Forms.smoothSectionAt_iff E M _ x).2
  have hmodel : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℂ) ∞
      (fun y : U => antiPart (Forms.inCoordinates E M a (x : M) y)) x :=
    (antiPartLinear (E := E)).contDiff.comp_contMDiffAt
      ((Forms.smoothSectionAt_iff E M a x).1 ha)
  apply hmodel.congr_of_eventuallyEq
  have hchart : ∀ᶠ y : U in 𝓝 x, (y : M) ∈ (chartAt E (x : M)).source :=
    (show ContinuousAt (fun y : U => (y : M)) x from
      continuous_subtype_val.continuousAt).eventually
        ((chartAt E (x : M)).open_source.mem_nhds (mem_chart_source E (x : M)))
  filter_upwards [hchart] with y hy
  exact inCoordinates_antiPart E M a (x : M) y hy

/-- A genuinely smooth native cotangent section projects to a genuinely
smooth native antiholomorphic cotangent section on the same open set. -/
theorem antiPartSection_smooth {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M))
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M a)) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M (antiPartSection E M a)) :=
  fun x => antiPartSection_smoothAt E M a x (ha x)

/-- The actual projected native form, carrying its proved smoothness and
pointwise anti-linearity; no differential equation is imposed. -/
def antiPartForm {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M))
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M a)) : Forms.FormSection E M U :=
  Forms.sectionMk E M U (antiPartSection E M a) (antiPartSection_smooth E M a ha)
    (antiPartSection_mem E M a)

@[simp] theorem antiPartForm_apply {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M))
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M a)) (x : U) :
    antiPartForm E M a ha x = antiPartSection E M a x := rfl

/-- Already antiholomorphic native form sections are fixed by the
projection, including their genuine smooth section data. -/
@[simp] theorem antiPartForm_eq_self {U : Opens M} (s : Forms.FormSection E M U) :
    antiPartForm E M s.val (Forms.FormSection.smooth E M s) = s := by
  apply Forms.FormSection.ext E M
  intro x
  exact congrFun (antiPartSection_eq_self E M s.val (Forms.FormSection.anti E M s)) x

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Tangent
