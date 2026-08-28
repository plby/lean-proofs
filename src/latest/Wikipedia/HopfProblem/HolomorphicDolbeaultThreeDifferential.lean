import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferentialCoordinates
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeTangent
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeForms

/-!
# The original native antiholomorphic differential as a sheaf morphism

The value is the antiholomorphic part of the actual manifold derivative.
It is smooth in the original cotangent bundle, complex-linear in the
function, and commutes with literal restriction to every original open.
-/

noncomputable section

open Bundle Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual native `(0,1)` form obtained from a smooth function. -/
def formOfSmooth (U : Opens M) (s : Functions.SmoothSection E M U) :
    Forms.FormSection E M U :=
  Tangent.antiPartForm E M (realSection E M U s) (realSection_smooth E M U s)

@[simp] theorem formOfSmooth_asModel (U : Opens M) (s : Functions.SmoothSection E M U)
    (x : U) :
    Forms.covectorAsModel E M (formOfSmooth E M U s x) =
      antiPart (Forms.covectorAsModel E M (realSection E M U s x)) := rfl

/-- In its original preferred chart this is the literal full Fréchet
antiholomorphic differential, with the usual positive convention. -/
theorem formOfSmooth_eq_chart_dbar (U : Opens M) (s : Functions.SmoothSection E M U)
    (x : U) :
    Forms.covectorAsModel E M (formOfSmooth E M U s x) =
      dbar (chartFunction E M U s (x : M)) (chartAt E (x : M) (x : M)) := by
  change antiPart (Forms.covectorAsModel E M (realSection E M U s x)) = _
  rw [realSection_eq_chart_fderiv]
  rfl

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ω M] in
theorem chartFunction_contDiffAt_self (U : Opens M) (s : Functions.SmoothSection E M U)
    (x : U) :
    ContDiffAt ℝ ∞ (chartFunction E M U s (x : M)) (chartAt E (x : M) (x : M)) := by
  apply chartFunction_contDiffAt E M U s
    (x : M) (chartAt E (x : M) (x : M))
    ((chartAt E (x : M)).map_source (mem_chart_source E (x : M)))
  simpa only [(chartAt E (x : M)).left_inv (mem_chart_source E (x : M))] using x.property

theorem formOfSmooth_add (U : Opens M) (s t : Functions.SmoothSection E M U) :
    formOfSmooth E M U (s + t) = formOfSmooth E M U s + formOfSmooth E M U t := by
  apply Forms.FormSection.ext E M
  intro x
  change Forms.covectorAsModel E M (formOfSmooth E M U (s + t) x) =
    Forms.covectorAsModel E M (formOfSmooth E M U s x) +
      Forms.covectorAsModel E M (formOfSmooth E M U t x)
  rw [formOfSmooth_eq_chart_dbar, formOfSmooth_eq_chart_dbar,
    formOfSmooth_eq_chart_dbar]
  have he : chartFunction E M U (s + t) (x : M) =
      chartFunction E M U s (x : M) + chartFunction E M U t (x : M) := by
    funext z
    simp only [chartFunction, Functions.extend_add, Function.comp_apply, Pi.add_apply]
  rw [he]
  exact dbar_add ((chartFunction_contDiffAt_self E M U s x).differentiableAt (by simp))
    ((chartFunction_contDiffAt_self E M U t x).differentiableAt (by simp))

theorem formOfSmooth_smul (U : Opens M) (c : ℂ) (s : Functions.SmoothSection E M U) :
    formOfSmooth E M U (c • s) = c • formOfSmooth E M U s := by
  apply Forms.FormSection.ext E M
  intro x
  change Forms.covectorAsModel E M (formOfSmooth E M U (c • s) x) =
    c • Forms.covectorAsModel E M (formOfSmooth E M U s x)
  rw [formOfSmooth_eq_chart_dbar, formOfSmooth_eq_chart_dbar]
  have he : chartFunction E M U (c • s) (x : M) =
      fun z => c * chartFunction E M U s (x : M) z := by
    funext z
    simp only [chartFunction, Functions.extend_smul, Function.comp_apply]
  rw [he]
  exact dbar_const_mul c ((chartFunction_contDiffAt_self E M U s x).differentiableAt
    (by simp))

/-- The native differential with its original pointwise complex linearity. -/
def differentialSection (U : Opens M) :
    Functions.SmoothSection E M U →ₗ[ℂ] Forms.FormSection E M U where
  toFun := formOfSmooth E M U
  map_add' := formOfSmooth_add E M U
  map_smul' := formOfSmooth_smul E M U

@[simp] theorem differentialSection_asModel (U : Opens M)
    (s : Functions.SmoothSection E M U) (x : U) :
    Forms.covectorAsModel E M (differentialSection E M U s x) =
      antiPart (Forms.covectorAsModel E M (realSection E M U s x)) := rfl

theorem differentialSection_restrict {U V : Opens M} (h : U ≤ V)
    (s : Functions.SmoothSection E M V) :
    differentialSection E M U (Functions.restriction E M h s) =
      Forms.restriction E M h (differentialSection E M V s) := by
  apply Forms.FormSection.ext E M
  intro x
  change antiPart (Forms.covectorAsModel E M
      (realSection E M U (Functions.restriction E M h s) x)) =
    antiPart (Forms.covectorAsModel E M (realSection E M V s ⟨x, h x.property⟩))
  rw [realSection_restrict]

/-- The actual native antiholomorphic differential on sheaves. -/
def differential : Functions.smoothSheaf E M ⟶ Forms.sheaf E M where
  hom :=
    { app U := AddCommGrpCat.ofHom (differentialSection E M U.unop).toAddMonoidHom
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        exact AddMonoidHom.ext (differentialSection_restrict E M (leOfHom h.unop)) }

/-- In every original chart, not just the selected chart centre, the
native form equals the literal chartwise full antiholomorphic derivative. -/
theorem differentialSection_inCoordinates (U : Opens M)
    (s : Functions.SmoothSection E M U) (x₀ : M) (x : U)
    (hx : (x : M) ∈ (chartAt E x₀).source) :
    Forms.inCoordinates E M (differentialSection E M U s).val x₀ x =
      dbar (chartFunction E M U s x₀) (chartAt E x₀ (x : M)) := by
  change Forms.inCoordinates E M (Tangent.antiPartSection E M
    (realSection E M U s)) x₀ x = _
  calc
    _ = antiPart (Forms.inCoordinates E M (realSection E M U s) x₀ x) :=
      Tangent.inCoordinates_antiPart E M (realSection E M U s) x₀ x hx
    _ = _ := by
      rw [realSection_coordinates_eq_fderiv E M U s x₀ x hx]
      rfl

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential
