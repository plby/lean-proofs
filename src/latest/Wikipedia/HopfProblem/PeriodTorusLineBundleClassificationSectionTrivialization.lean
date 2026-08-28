import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIdentification
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationSectionTransport
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreTrivialization
import Wikipedia.HopfProblem.PeriodTori

/-!
# An actual native product trivialization from a nowhere-zero section

The given holomorphic section is transported by the existing native
identification to the scalar-core bundle. Its proved section-to-product map
then gives an actual fibre-linear analytic diffeomorphism for the original
native total space, carrying the original section to the constant vector `1`.
No classification or preexisting global trivialization is assumed.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusLineBundleClassificationNative

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

private def transportedNonzeroSection (s : ContMDiffSection IC ℂ ω V) :
    ContMDiffSection IC ℂ ω (data V).core.Fiber :=
  (identification V IC).symm.sectionEquiv s

private theorem transportedNonzeroSection_ne_zero (s : ContMDiffSection IC ℂ ω V)
    (hne : ∀ x, s x ≠ 0) (x : p.Torus) : transportedNonzeroSection p V s x ≠ 0 :=
  ((identification V IC).symm.sectionEquiv_value_ne_zero_iff s x).mpr (hne x)

private def coreNonzeroSectionTrivialization (s : ContMDiffSection IC ℂ ω V)
    (hne : ∀ x, s x ≠ 0) : (data V).AnalyticTrivialization IC :=
  (data V).analyticTrivializationOfSection (transportedNonzeroSection p V s) IC
    (transportedNonzeroSection p V s).contMDiff
    (transportedNonzeroSection_ne_zero p V s hne)

/-- A nowhere-zero native holomorphic section determines an actual analytic
product diffeomorphism of the original native total space. -/
def nonzeroSectionProductDiffeomorph (s : ContMDiffSection IC ℂ ω V)
    (hne : ∀ x, s x ≠ 0) :
    Diffeomorph ((IC).prod I₁) ((IC).prod I₁) (TotalSpace ℂ V) (p.Torus × ℂ) ω :=
  (identification V IC).diffeomorph.symm.trans
    (coreNonzeroSectionTrivialization p V s hne).diffeomorph

theorem nonzeroSectionProductDiffeomorph_preserves_base
    (s : ContMDiffSection IC ℂ ω V) (hne : ∀ x, s x ≠ 0) (v : TotalSpace ℂ V) :
    (nonzeroSectionProductDiffeomorph p V s hne v).1 = v.proj :=
  (coreNonzeroSectionTrivialization p V s hne).preserves_base (fromNative V v)

theorem nonzeroSectionProductDiffeomorph_map_add
    (s : ContMDiffSection IC ℂ ω V) (hne : ∀ x, s x ≠ 0)
    (x : p.Torus) (v w : V x) :
    (nonzeroSectionProductDiffeomorph p V s hne ⟨x, v + w⟩).2 =
      (nonzeroSectionProductDiffeomorph p V s hne ⟨x, v⟩).2 +
        (nonzeroSectionProductDiffeomorph p V s hne ⟨x, w⟩).2 := by
  change ((coreNonzeroSectionTrivialization p V s hne).diffeomorph
    ⟨x, (fiberIdentification V x).symm (v + w)⟩).2 = _
  rw [map_add]
  exact (coreNonzeroSectionTrivialization p V s hne).map_add x _ _

theorem nonzeroSectionProductDiffeomorph_map_smul
    (s : ContMDiffSection IC ℂ ω V) (hne : ∀ x, s x ≠ 0)
    (x : p.Torus) (c : ℂ) (v : V x) :
    (nonzeroSectionProductDiffeomorph p V s hne ⟨x, c • v⟩).2 =
      c • (nonzeroSectionProductDiffeomorph p V s hne ⟨x, v⟩).2 := by
  change ((coreNonzeroSectionTrivialization p V s hne).diffeomorph
    ⟨x, (fiberIdentification V x).symm (c • v)⟩).2 = _
  rw [map_smul]
  exact (coreNonzeroSectionTrivialization p V s hne).map_smul x c _

/-- The actual original section is normalized to the constant fibre vector
`1`, with the base point unchanged. -/
theorem nonzeroSectionProductDiffeomorph_section
    (s : ContMDiffSection IC ℂ ω V) (hne : ∀ x, s x ≠ 0) (x : p.Torus) :
    nonzeroSectionProductDiffeomorph p V s hne ⟨x, s x⟩ = (x, 1) :=
  (data V).sectionTrivialization_section (transportedNonzeroSection p V s) IC
    (transportedNonzeroSection p V s).contMDiff
    (transportedNonzeroSection_ne_zero p V s hne) x

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
