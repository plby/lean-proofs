import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic

/-!
# The actual inclusion of holomorphic into smooth functions

For manifolds charted on the complex plane, an actual analytic map is
smooth in the underlying real charts. The resulting inclusion on every
open submanifold is a literal complex-linear map of actual functions and
commutes with restriction. It gives the first arrow of the actual
one-dimensional Dolbeault sequence.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
  [IsManifold 𝓘(ℂ) ω M] [IsManifold 𝓘(ℝ, ℂ) ∞ M]

/-- Analytic maps in the complex charts are genuinely smooth in the
same charts considered over the real field. -/
theorem real_smooth_of_holomorphic {f : M → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f := by
  rw [contMDiff_iff] at hf ⊢
  refine ⟨hf.1, fun x y => ?_⟩
  exact ((hf.2 x y).of_le (by simp)).restrict_scalars ℝ

variable (M)

/-- The genuine complex-linear inclusion on each actual open set. -/
def inclusionSection (U : Opens M) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ) M U →ₗ[ℂ]
      SmoothFunctions.Section 𝓘(ℝ, ℂ) M U where
  toFun f := ⟨f, real_smooth_of_holomorphic f.contMDiff⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem inclusionSection_apply (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) M U) (x : U) :
    inclusionSection M U f x = f x := rfl

theorem inclusionSection_injective (U : Opens M) :
    Function.Injective (inclusionSection M U) := by
  intro f g h
  apply ContMDiffMap.ext
  intro x
  exact congrArg (fun k : SmoothFunctions.Section 𝓘(ℝ, ℂ) M U => k x) h

/-- The actual holomorphic-to-smooth morphism of additive sheaves. -/
def inclusion : HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ) M ⟶
    SmoothFunctions.additiveSheaf 𝓘(ℝ, ℂ) M where
  hom :=
    { app U := AddCommGrpCat.ofHom (inclusionSection M U.unop).toAddMonoidHom
      naturality _ _ _ := rfl }

/-- The actual inclusion is a monomorphism of sheaves. -/
instance inclusion_mono : Mono (inclusion M) := by
  have h (U : (Opens (TopCat.of M))ᵒᵖ) : Mono ((inclusion M).hom.app U) :=
    ConcreteCategory.mono_of_injective _ (inclusionSection_injective M U.unop)
  have : Mono (inclusion M).hom := NatTrans.mono_of_mono_app _
  exact (TopCat.Sheaf.forget AddCommGrpCat (TopCat.of M)).mono_of_mono_map this

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DolbeaultLocal
