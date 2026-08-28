import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsLinear
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Native sections under an actual fibrewise bundle biholomorphism

An actual biholomorphism of original bundle total spaces which acts
by continuous-linear equivalences on the original fibres induces a
linear equivalence of holomorphic sections on every base open. The
scalar ring is the actual ring of holomorphic functions on that open.
Both directions use the original total-space holomorphic maps and
commute with literal section restriction.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections.Comparison

variable {M : Type} {ι κ : Type*} [TopologicalSpace M]
  (C : VectorBundleCore ℂ M ℂ ι) (D : VectorBundleCore ℂ M ℂ κ)
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (e : Diffeomorph (I.prod I₁) (I.prod I₁) C.TotalSpace D.TotalSpace ω)
  (φ : ∀ x : M, C.Fiber x ≃L[ℂ] D.Fiber x)
  (he : ∀ (x : M) (v : C.Fiber x), e ⟨x, v⟩ = ⟨x, φ x v⟩)

include he in
/-- The actual inverse total-space map acts by the inverse fibre map. -/
theorem inverse_fiberwise (x : M) (v : D.Fiber x) :
    e.symm ⟨x, v⟩ = ⟨x, (φ x).symm v⟩ := by
  apply e.injective
  change e (e.symm ⟨x, v⟩) = e ⟨x, (φ x).symm v⟩
  rw [e.apply_symm_apply, he, (φ x).apply_symm_apply]

/-- Apply the actual original bundle map to a section on a base open. -/
def mapSection (U : Opens M) (s : Section C I U) : Section D I U where
  toFun x := φ (x : M) (s x)
  contMDiff_toFun := by
    simpa only [Function.comp_def, he] using e.contMDiff.comp s.contMDiff_toFun

/-- Apply the actual inverse original bundle map on the same base open. -/
def invMapSection (U : Opens M) (s : Section D I U) : Section C I U where
  toFun x := (φ (x : M)).symm (s x)
  contMDiff_toFun := by
    simpa only [Function.comp_def, inverse_fiberwise C D I e φ he] using
      e.symm.contMDiff.comp s.contMDiff_toFun

@[simp] theorem mapSection_apply (U : Opens M) (s : Section C I U) (x : U) :
    mapSection C D I e φ he U s x = φ (x : M) (s x) := rfl

@[simp] theorem invMapSection_apply (U : Opens M) (s : Section D I U) (x : U) :
    invMapSection C D I e φ he U s x = (φ (x : M)).symm (s x) := rfl

/-- The induced section map is composition in the original total spaces. -/
theorem mapSection_totalSpace (U : Opens M) (s : Section C I U) (x : U) :
    Section.totalSpace D I (mapSection C D I e φ he U s) x =
      e (Section.totalSpace C I s x) :=
  (he (x : M) (s x)).symm

theorem invMapSection_totalSpace (U : Opens M) (s : Section D I U) (x : U) :
    Section.totalSpace C I (invMapSection C D I e φ he U s) x =
      e.symm (Section.totalSpace D I s x) :=
  (inverse_fiberwise C D I e φ he (x : M) (s x)).symm

/-- The full section spaces are equivalent by the actual fibre maps. -/
def sectionEquiv (U : Opens M) : Section C I U ≃ Section D I U where
  toFun := mapSection C D I e φ he U
  invFun := invMapSection C D I e φ he U
  left_inv s := by
    apply Section.ext C I
    intro x
    exact (φ (x : M)).symm_apply_apply (s x)
  right_inv s := by
    apply Section.ext D I
    intro x
    exact (φ (x : M)).apply_symm_apply (s x)

@[simp] theorem sectionEquiv_apply (U : Opens M) (s : Section C I U) (x : U) :
    sectionEquiv C D I e φ he U s x = φ (x : M) (s x) := rfl

@[simp] theorem sectionEquiv_symm_apply (U : Opens M) (s : Section D I U) (x : U) :
    (sectionEquiv C D I e φ he U).symm s x = (φ (x : M)).symm (s x) := rfl

variable [C.IsContMDiff I ω] [D.IsContMDiff I ω]

/-- The comparison is linear over actual holomorphic functions on each
open, with the literal pointwise actions on the original fibres. -/
def sectionLinearEquiv (U : Opens M) :
    Section C I U ≃ₗ[HolomorphicFunctionSheaf.Section I M U] Section D I U where
  __ := sectionEquiv C D I e φ he U
  map_add' s t := by
    apply Section.ext D I
    intro x
    exact (φ (x : M)).map_add (s x) (t x)
  map_smul' f s := by
    apply Section.ext D I
    intro x
    exact (φ (x : M)).map_smul (f x) (s x)

@[simp] theorem sectionLinearEquiv_apply (U : Opens M) (s : Section C I U) (x : U) :
    sectionLinearEquiv C D I e φ he U s x = φ (x : M) (s x) := rfl

@[simp] theorem sectionLinearEquiv_symm_apply (U : Opens M) (s : Section D I U) (x : U) :
    (sectionLinearEquiv C D I e φ he U).symm s x = (φ (x : M)).symm (s x) := rfl

theorem sectionLinearEquiv_totalSpace (U : Opens M) (s : Section C I U) (x : U) :
    Section.totalSpace D I (sectionLinearEquiv C D I e φ he U s) x =
      e (Section.totalSpace C I s x) :=
  mapSection_totalSpace C D I e φ he U s x

theorem sectionLinearEquiv_symm_totalSpace (U : Opens M) (s : Section D I U) (x : U) :
    Section.totalSpace C I ((sectionLinearEquiv C D I e φ he U).symm s) x =
      e.symm (Section.totalSpace D I s x) :=
  invMapSection_totalSpace C D I e φ he U s x

/-- The native section comparison commutes with literal restriction. -/
theorem sectionLinearEquiv_restrict {U V : Opens M} (h : U ≤ V) (s : Section C I V) :
    sectionLinearEquiv C D I e φ he U (Section.restrict C I h s) =
      Section.restrict D I h (sectionLinearEquiv C D I e φ he V s) := by
  apply Section.ext D I
  intro x
  rfl

theorem sectionLinearEquiv_symm_restrict {U V : Opens M} (h : U ≤ V) (s : Section D I V) :
    (sectionLinearEquiv C D I e φ he U).symm (Section.restrict D I h s) =
      Section.restrict C I h ((sectionLinearEquiv C D I e φ he V).symm s) := by
  apply Section.ext C I
  intro x
  rfl

/-- Forgetting variable scalars gives the same native comparison over complex constants. -/
def sectionComplexLinearEquiv (U : Opens M) : Section C I U ≃ₗ[ℂ] Section D I U :=
  (sectionLinearEquiv C D I e φ he U).restrictScalars ℂ

@[simp] theorem sectionComplexLinearEquiv_apply (U : Opens M) (s : Section C I U) (x : U) :
    sectionComplexLinearEquiv C D I e φ he U s x = φ (x : M) (s x) := rfl

@[simp] theorem sectionComplexLinearEquiv_symm_apply
    (U : Opens M) (s : Section D I U) (x : U) :
    (sectionComplexLinearEquiv C D I e φ he U).symm s x = (φ (x : M)).symm (s x) := rfl

end Wikipedia.HopfProblem.NativeBundleSections.Comparison
