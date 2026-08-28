import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCohomology
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeScalars
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCohomologyAbstractScalars
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Native complex-linear degree-one Dolbeault comparison

The quotient has its actual pointwise complex module structure modulo
the range of the actual complex-linear differential.  The target has
the scalar action induced on genuine `Sheaf.H` by multiplication of the
original holomorphic functions.  The comparison is the original positive
connecting morphism; neither scalar action is transported through it.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Cohomology

open NativeDifferential CuspNormalization.SheafCohomology
open HolomorphicSheafCohomology

variable (M : Type) [TopologicalSpace M] [ChartedSpace Model M]
  [IsManifold 𝓘(ℂ, Model) ω M] [IsManifold 𝓘(ℝ, Model) ∞ M]

/-- The original holomorphic-sheaf-induced complex action on actual `H¹`. -/
@[instance_reducible] def h1Module : Module ℂ (H1 M) :=
  holomorphicCohomologyModule 𝓘(ℂ, Model) M 1

attribute [local instance] h1Module

local instance closedSectionsModule :
    Module ℂ (CohomologyAbstract.Sections (initialComplex Model M).X₃) :=
  ClosedForms.sheaf_obj_module Model M (op ⊤)

omit [IsManifold 𝓘(ℂ, Model) ω M] [IsManifold 𝓘(ℝ, Model) ∞ M] in
/-- Scalar multiplication is the genuine cohomology map of multiplication
of the original holomorphic functions. -/
theorem h1Module_smul (c : ℂ) (a : H1 M) :
    c • a = CategoryTheory.Sheaf.H.map (holomorphicScalarEnd 𝓘(ℂ, Model) M c) 1 a := rfl

/-- The actual positive connecting morphism, with both native scalar actions. -/
def classLinearMap : GlobalClosed M →ₗ[ℂ] H1 M :=
  CohomologyAbstract.classLinearMap
    (S := initialComplex Model M)
    (holomorphicScalarEnd 𝓘(ℂ, Model) M)
    (SmoothFunctions.scalarEnd 𝓘(ℝ, Model) M)
    (ClosedForms.scalarEnd Model M)
    (inclusion_scalar Model M) (closedDifferential_scalar Model M)
    (fun c s => ClosedForms.scalarEnd_eq_smul Model M c ⊤ s)
    (initialComplex_shortExact M)

@[simp] theorem classLinearMap_apply (s : GlobalClosed M) :
    classLinearMap M s = classMap M s := rfl

/-- The genuine globally exact native forms, as the actual image subspace. -/
def exactForms : Submodule ℂ (GlobalClosed M) :=
  (closedSectionLinearMap Model M ⊤).range

theorem mem_exactForms (s : GlobalClosed M) :
    s ∈ exactForms M ↔ ∃ f : GlobalSmooth M, closedSection Model M ⊤ f = s := Iff.rfl

/-- The kernel of the native class map is exactly the original image
subspace, not a chosen presentation of the cohomology group. -/
theorem classLinearMap_ker : (classLinearMap M).ker = exactForms M := by
  ext s
  exact classMap_eq_zero_iff M s

/-- Closed global native forms modulo actual globally exact native forms,
with the original pointwise complex module quotient. -/
abbrev DolbeaultH1 := GlobalClosed M ⧸ exactForms M

variable [T2Space M] [SigmaCompactSpace M]

theorem classLinearMap_surjective : Function.Surjective (classLinearMap M) :=
  classMap_surjective M

/-- The genuine native complex-linear Dolbeault comparison in degree one. -/
def linearEquiv : DolbeaultH1 M ≃ₗ[ℂ] H1 M :=
  (Submodule.quotEquivOfEq (exactForms M) (classLinearMap M).ker
    (classLinearMap_ker M).symm).trans
      ((classLinearMap M).quotKerEquivOfSurjective (classLinearMap_surjective M))

/-- On actual forms the comparison is precisely the original positive
Ext connecting class, with no sign or scalar normalization. -/
@[simp] theorem linearEquiv_mk (s : GlobalClosed M) :
    linearEquiv M (Submodule.Quotient.mk s) = classMap M s := by
  simp only [linearEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk, classLinearMap_apply]

theorem linearEquiv_symm_classMap (s : GlobalClosed M) :
    (linearEquiv M).symm (classMap M s) = Submodule.Quotient.mk s := by
  apply (linearEquiv M).injective
  rw [LinearEquiv.apply_symm_apply, linearEquiv_mk]

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Cohomology
