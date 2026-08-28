import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedCoordinates
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeTangentTransitions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth coefficients of native forms in the actual manifold charts

The ambient extension agrees with the original section on its open domain.
Its native Hom-bundle coordinates are smooth wherever the original chart is
defined.  Composing with the original inverse chart gives real smooth
coefficient functions on the actual coordinate domain.  On a complex manifold
the same coefficients retain the original antiholomorphic linearity.
-/

noncomputable section

open Bundle Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The ambient representative is a native smooth bundle section at every
point of the original open domain. -/
theorem extendForm_contMDiffAt {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M))
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M a)) (x : M) (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (fun y : M => (⟨y, extendForm E M U a y⟩ : Forms.CotangentBundle E M)) x := by
  apply (contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp
  apply (ha ⟨x, hx⟩).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro y
  change (⟨(y : M), extendForm E M U a (y : M)⟩ : Forms.CotangentBundle E M) =
    ⟨(y : M), a y⟩
  rw [extendForm_apply E M U a (y : M) y.property]

/-- A native smooth section has real smooth coefficients in any of the
original preferred charts on the actual coordinate domain. -/
theorem coordinateForm_contDiffAt_of_smooth {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M))
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M a)) (x₀ : M) (z : E)
    (hz : z ∈ coordinateDomain E M U x₀) :
    ContDiffAt ℝ ∞ (coordinateForm E M U a x₀) z := by
  let t : M → Forms.CotangentBundle E M :=
    fun y => ⟨y, extendForm E M U a y⟩
  let e := trivializationAt (E →L[ℝ] ℂ) (Forms.Covector E M) x₀
  have ht : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      t ((chartAt E x₀).symm z) :=
    extendForm_contMDiffAt E M a ha _ hz.2
  have he : t ((chartAt E x₀).symm z) ∈ e.source := by
    rw [e.mem_source]
    change (chartAt E x₀).symm z ∈
      (trivializationAt (E →L[ℝ] ℂ) (Forms.Covector E M) x₀).baseSet
    simpa [Forms.Covector, hom_trivializationAt_baseSet] using
      (chartAt E x₀).map_target hz.1
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℂ) ∞
      (fun y => (e (t y)).2) ((chartAt E x₀).symm z) :=
    ((e.contMDiffAt_iff he).mp ht).2
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (chartAt E x₀).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x₀) hz.1
  exact (hc.comp z hi).contDiffAt

variable [NormedSpace ℂ E]

/-- The coefficients of an original smooth antiholomorphic form are real
smooth at every point of their actual chart domain. -/
theorem coordinateForm_contDiffAt {U : Opens M} (s : Forms.FormSection E M U)
    (x₀ : M) (z : E) (hz : z ∈ coordinateDomain E M U x₀) :
    ContDiffAt ℝ ∞ (coordinateForm E M U s.val x₀) z :=
  coordinateForm_contDiffAt_of_smooth E M s.val (Forms.FormSection.smooth E M s) x₀ z hz

/-- Real smoothness holds on the whole actual coordinate domain. -/
theorem coordinateForm_contDiffOn {U : Opens M} (s : Forms.FormSection E M U)
    (x₀ : M) :
    ContDiffOn ℝ ∞ (coordinateForm E M U s.val x₀) (coordinateDomain E M U x₀) :=
  fun z hz => (coordinateForm_contDiffAt E M s x₀ z hz).contDiffWithinAt

/-- Evaluation on an original fixed model vector is a real smooth scalar
coefficient function on the actual chart domain. -/
theorem coordinateForm_apply_contDiffAt {U : Opens M} (s : Forms.FormSection E M U)
    (x₀ : M) (z : E) (hz : z ∈ coordinateDomain E M U x₀) (v : E) :
    ContDiffAt ℝ ∞ (fun y => coordinateForm E M U s.val x₀ y v) z :=
  (coordinateForm_contDiffAt E M s x₀ z hz).clm_apply contDiffAt_const

/-- The actual covector coefficient has an ordinary real Fréchet derivative
at every point of its original coordinate domain. -/
theorem coordinateForm_differentiableAt {U : Opens M} (s : Forms.FormSection E M U)
    (x₀ : M) (z : E) (hz : z ∈ coordinateDomain E M U x₀) :
    DifferentiableAt ℝ (coordinateForm E M U s.val x₀) z :=
  (coordinateForm_contDiffAt E M s x₀ z hz).differentiableAt (by simp)

/-- In particular every literal scalar coefficient has its ordinary real
Fréchet derivative on the actual chart domain. -/
theorem coordinateForm_apply_differentiableAt {U : Opens M}
    (s : Forms.FormSection E M U) (x₀ : M) (z : E)
    (hz : z ∈ coordinateDomain E M U x₀) (v : E) :
    DifferentiableAt ℝ (fun y => coordinateForm E M U s.val x₀ y v) z :=
  (coordinateForm_apply_contDiffAt E M s x₀ z hz v).differentiableAt (by simp)

variable [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ω M]

/-- Original holomorphic chart transitions preserve the actual
antiholomorphic linearity of the covectors. -/
theorem coordinateForm_anti_I {U : Opens M} (s : Forms.FormSection E M U)
    (x₀ : M) (z : E) (hz : z ∈ coordinateDomain E M U x₀) (v : E) :
    coordinateForm E M U s.val x₀ z (Complex.I • v) =
      -Complex.I * coordinateForm E M U s.val x₀ z v := by
  change z ∈ (chartAt E x₀).target ∧ (chartAt E x₀).symm z ∈ U at hz
  let p : U := ⟨(chartAt E x₀).symm z, hz.2⟩
  let T : E →L[ℝ] E :=
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ ((chartAt E x₀).symm z)
  have hT : T (Complex.I • v) = Complex.I • T v :=
    Tangent.symmL_trivializationAt_complex_smul E M x₀ ((chartAt E x₀).symm z)
      ((chartAt E x₀).map_target hz.1) Complex.I v
  calc
    coordinateForm E M U s.val x₀ z (Complex.I • v) =
        Forms.covectorAsModel E M (s p) (T (Complex.I • v)) :=
      coordinateForm_apply E M U s.val x₀ z (Complex.I • v) hz
    _ = Forms.covectorAsModel E M (s p) (Complex.I • T v) :=
      congrArg (Forms.covectorAsModel E M (s p)) hT
    _ = -Complex.I * Forms.covectorAsModel E M (s p) (T v) :=
      Forms.FormSection.anti_I E M s p (T v)
    _ = -Complex.I * coordinateForm E M U s.val x₀ z v :=
      congrArg (-Complex.I * ·) (coordinateForm_apply E M U s.val x₀ z v hz).symm

/-- The actual native coordinate covector lies in the original
antiholomorphic covector subspace. -/
theorem coordinateForm_anti {U : Opens M} (s : Forms.FormSection E M U)
    (x₀ : M) (z : E) (hz : z ∈ coordinateDomain E M U x₀) :
    coordinateForm E M U s.val x₀ z ∈ antiCovectors (E := E) :=
  fun v => coordinateForm_anti_I E M s x₀ z hz v

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms
