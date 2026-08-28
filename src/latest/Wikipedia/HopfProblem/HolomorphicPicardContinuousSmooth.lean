import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothBasic
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual map from holomorphic to smooth functions

Restriction of scalars changes only the differentiability field in the
original charts.  The sheaf map constructed here is the identity on the
underlying complex-valued functions on each original open set.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicard.ContinuousSmooth

open HolomorphicSheafCohomology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]

/-- A holomorphic function is smooth in exactly the same original charts,
with the derivative's scalar field restricted from complex to real. -/
theorem contMDiff_real_of_complex {f : M → ℂ}
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ω f) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f := by
  intro x
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp (hf x)
  apply contMDiffAt_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [mfld_simps] using (hd.restrict_scalars ℝ).of_le (show ∞ ≤ ω by simp)

/-- The actual same function, now bundled with real smoothness. -/
def smoothSection (U : Opens M) (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) :
    SmoothFunctions.Section 𝓘(ℝ, E) M U :=
  ⟨f, contMDiff_real_of_complex U f.contMDiff⟩

@[simp] theorem smoothSection_apply (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U) (x : U) :
    smoothSection M U f x = f x := rfl

/-- Pointwise addition is preserved by this literal inclusion of sections. -/
def sectionAddHom (U : Opens M) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U →+
      SmoothFunctions.Section 𝓘(ℝ, E) M U where
  toFun := smoothSection M U
  map_zero' := by apply ContMDiffMap.ext; intro x; rfl
  map_add' _ _ := by apply ContMDiffMap.ext; intro x; rfl

/-- The genuine sheaf morphism, with literal restriction compatibility. -/
def sheafMap : HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, E) M ⟶
    SmoothFunctions.additiveSheaf 𝓘(ℝ, E) M where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom (sectionAddHom M U.unop)
      naturality := by
        intro U V h
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro f
        apply ContMDiffMap.ext
        intro x
        rfl }

/-- Evaluation of the original sheaf map does not change the function. -/
@[simp] theorem sheafMap_apply (U : (Opens (TopCat.of M))ᵒᵖ)
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ, E) M U.unop)
    (x : U.unop) :
    (sheafMap M).hom.app U f x = f x := rfl

end Wikipedia.HopfProblem.HolomorphicPicard.ContinuousSmooth
