import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBundle
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth pointwise operations on native complex-valued cotangent sections

All operations here are operations on the original dependent covectors.  The
native Hom-bundle coordinates commute with complex scalar multiplication because
the target bundle is the trivial complex line; the tangent trivialization is
only precomposed with the covector.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The target trivialization is the identity, so native cotangent coordinates
are literal precomposition by the tangent trivialization's inverse linear map. -/
theorem inCoordinates_comp {U : Opens M}
    (a : ∀ x : U, Covector E M (x : M)) (x₀ : M) (x : U) :
    inCoordinates E M a x₀ x =
      (a x).comp ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x) := by
  ext v
  exact inCoordinates_apply E M a x₀ x v

@[simp] theorem inCoordinates_zero (U : Opens M) (x₀ : M) (x : U) :
    inCoordinates E M (fun x : U => (0 : Covector E M (x : M))) x₀ x = 0 := by
  rw [inCoordinates_comp]
  ext v
  rfl

@[simp] theorem inCoordinates_add {U : Opens M}
    (a b : ∀ x : U, Covector E M (x : M)) (x₀ : M) (x : U) :
    inCoordinates E M (fun x => a x + b x) x₀ x =
      inCoordinates E M a x₀ x + inCoordinates E M b x₀ x := by
  simp only [inCoordinates_comp]
  ext v
  rfl

@[simp] theorem inCoordinates_neg {U : Opens M}
    (a : ∀ x : U, Covector E M (x : M)) (x₀ : M) (x : U) :
    inCoordinates E M (fun x => -a x) x₀ x = -inCoordinates E M a x₀ x := by
  simp only [inCoordinates_comp]
  ext v
  rfl

@[simp] theorem inCoordinates_function_smul {U : Opens M} (g : U → ℂ)
    (a : ∀ x : U, Covector E M (x : M)) (x₀ : M) (x : U) :
    inCoordinates E M (fun x => g x • a x) x₀ x =
      g x • inCoordinates E M a x₀ x := by
  simp only [inCoordinates_comp]
  ext v
  rfl

@[simp] theorem inCoordinates_smul {U : Opens M} (c : ℂ)
    (a : ∀ x : U, Covector E M (x : M)) (x₀ : M) (x : U) :
    inCoordinates E M (fun x => c • a x) x₀ x =
      c • inCoordinates E M a x₀ x :=
  inCoordinates_function_smul E M (fun _ => c) a x₀ x

/-- The original zero covector section is smooth. -/
theorem smoothSection_zero (U : Opens M) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M (fun x : U => (0 : Covector E M (x : M)))) := by
  intro x
  apply (smoothSectionAt_iff E M _ x).2
  exact (contMDiffAt_const : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℂ) ∞
      (fun _ : U => (0 : E →L[ℝ] ℂ)) x).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => inCoordinates_zero E M U x y)

/-- Pointwise addition preserves smoothness in the native Hom bundle. -/
theorem smoothSection_add {U : Opens M}
    (a b : ∀ x : U, Covector E M (x : M))
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M a))
    (hb : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M b)) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M (fun x => a x + b x)) := by
  intro x
  apply (smoothSectionAt_iff E M _ x).2
  exact (((smoothSectionAt_iff E M a x).1 (ha x)).add
      ((smoothSectionAt_iff E M b x).1 (hb x))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => inCoordinates_add E M a b x y)

/-- Pointwise negation preserves smoothness in the native Hom bundle. -/
theorem smoothSection_neg {U : Opens M}
    (a : ∀ x : U, Covector E M (x : M))
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M a)) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M (fun x => -a x)) := by
  intro x
  apply (smoothSectionAt_iff E M _ x).2
  exact ((smoothSectionAt_iff E M a x).1 (ha x)).neg.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => inCoordinates_neg E M a x y)

/-- Multiplication by a smooth complex-valued function preserves smoothness
of the original dependent covectors. -/
theorem smoothSection_function_smul {U : Opens M} (g : U → ℂ)
    (a : ∀ x : U, Covector E M (x : M))
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ g)
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M a)) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M (fun x => g x • a x)) := by
  intro x
  apply (smoothSectionAt_iff E M _ x).2
  have hmul : ContDiff ℝ ∞ (fun p : ℂ × (E →L[ℝ] ℂ) => p.1 • p.2) :=
    contDiff_smul
  exact (hmul.comp_contMDiffAt ((hg x).prodMk_space
      ((smoothSectionAt_iff E M a x).1 (ha x)))).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => inCoordinates_function_smul E M g a x y)

/-- Multiplication by a constant complex scalar preserves native smoothness. -/
theorem smoothSection_smul {U : Opens M} (c : ℂ)
    (a : ∀ x : U, Covector E M (x : M))
    (ha : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M a)) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (sectionMap E M (fun x => c • a x)) :=
  smoothSection_function_smul E M (fun _ => c) a contMDiff_const ha

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms
