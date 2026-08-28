import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeDifferentialClosed
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeKernel
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosed

/-!
# The original differential into the actual closed-form sheaf

The target consists of all genuine smooth anti-linear native forms
satisfying their actual chartwise differential equation.  The map is
the original native differential, with only its proved closedness added.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original complex-linear differential into actual closed forms. -/
def closedSectionLinearMap (U : Opens M) :
    Functions.SmoothSection E M U →ₗ[ℂ] ClosedForms.ClosedFormSection E M U where
  toFun := closedSection E M U
  map_add' s t := by
    apply (ClosedForms.toFormLinearMap_injective E M U)
    exact map_add (differentialSection E M U) s t
  map_smul' c s := by
    apply (ClosedForms.toFormLinearMap_injective E M U)
    exact map_smul (differentialSection E M U) c s

@[simp] theorem closedSectionLinearMap_apply (U : Opens M)
    (s : Functions.SmoothSection E M U) :
    closedSectionLinearMap E M U s = closedSection E M U s := rfl

/-- The actual sheaf morphism `A⁰ → Z¹`, with original restrictions. -/
def closedDifferential : Functions.smoothSheaf E M ⟶ ClosedForms.sheaf E M where
  hom :=
    { app U := AddCommGrpCat.ofHom (closedSectionLinearMap E M U.unop).toAddMonoidHom
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        exact AddMonoidHom.ext (closedSection_restrict E M (leOfHom h.unop)) }

/-- Forgetting the closedness proof gives precisely the original native
differential, without an isomorphic replacement or a sign change. -/
@[reassoc] theorem closedDifferential_inclusion :
    closedDifferential E M ≫ ClosedForms.inclusion E M = differential E M := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  exact AddMonoidHom.ext fun _ => rfl

theorem inclusion_closedDifferential :
    Functions.inclusion E M ≫ closedDifferential E M = 0 := by
  apply (cancel_mono (ClosedForms.inclusion E M)).mp
  rw [Category.assoc, closedDifferential_inclusion, inclusion_differential, zero_comp]

/-- The genuine initial native Dolbeault short complex. -/
def initialComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of M)) :=
  ShortComplex.mk (Functions.inclusion E M) (closedDifferential E M)
    (inclusion_closedDifferential E M)

@[simp] theorem initialComplex_f : (initialComplex E M).f = Functions.inclusion E M := rfl
@[simp] theorem initialComplex_g : (initialComplex E M).g = closedDifferential E M := rfl

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential
