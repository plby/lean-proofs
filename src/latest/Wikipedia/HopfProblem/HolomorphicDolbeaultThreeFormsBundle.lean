import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Analysis.Complex.Basic

/-!
# Smooth open sections of the native real cotangent Hom bundle

The fibres are actual real continuous-linear maps from the original
tangent spaces to `ℂ`.  Their total space has Mathlib's native Hom-bundle
topology and charted-space structure.  Smoothness on an open set is
smoothness of the actual dependent section map into this total space.
-/

noncomputable section

open Bundle TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual real cotangent fibre with complex values. -/
abbrev Covector (x : M) := TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℂ

/-- The original native real cotangent Hom-bundle total space. -/
abbrev CotangentBundle := Bundle.TotalSpace (E →L[ℝ] ℂ) (Covector E M)

/-- Native tangent and Hom-bundle instances give actual smoothness. -/
theorem cotangentBundle_smooth :
    ContMDiffVectorBundle ∞ (E →L[ℝ] ℂ) (Covector E M) 𝓘(ℝ, E) :=
  inferInstance

/-- The native fibre covector written using the model underlying that
particular tangent space.  This does not change any bundle topology. -/
def covectorAsModel {x : M} (L : Covector E M x) : E →L[ℝ] ℂ := L

/-- Regard a model covector as a vector in one specified native fibre. -/
def covectorFromModel (x : M) (L : E →L[ℝ] ℂ) : Covector E M x := L

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem covectorAsModel_fromModel (x : M) (L : E →L[ℝ] ℂ) :
    covectorAsModel E M (covectorFromModel E M x L) = L := rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem covectorFromModel_asModel {x : M} (L : Covector E M x) :
    covectorFromModel E M x (covectorAsModel E M L) = L := rfl

/-- A dependent open section determines its original total-space map. -/
def sectionMap {U : Opens M} (a : ∀ x : U, Covector E M (x : M)) :
    U → CotangentBundle E M :=
  fun x => ⟨(x : M), a x⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem sectionMap_proj {U : Opens M}
    (a : ∀ x : U, Covector E M (x : M)) (x : U) :
    (sectionMap E M a x).proj = (x : M) := rfl

/-- Literal native covector coordinates in the tangent trivialization
centred at the specified original base point. -/
def inCoordinates {U : Opens M} (a : ∀ x : U, Covector E M (x : M))
    (x₀ : M) (x : U) : E →L[ℝ] ℂ :=
  (trivializationAt (E →L[ℝ] ℂ) (Covector E M) x₀ (sectionMap E M a x)).2

/-- These coordinates are exactly Mathlib's Hom-bundle coordinates. -/
theorem inCoordinates_eq {U : Opens M} (a : ∀ x : U, Covector E M (x : M))
    (x₀ : M) (x : U) :
    inCoordinates E M a x₀ x =
      ContinuousLinearMap.inCoordinates E (TangentSpace 𝓘(ℝ, E) : M → Type)
        ℂ (fun _ : M => ℂ) x₀ x x₀ x (a x) := rfl

/-- Coordinate evaluation uses the inverse of the actual tangent
trivialization, not a fixed trivialization of the manifold's tangent bundle. -/
theorem inCoordinates_apply {U : Opens M} (a : ∀ x : U, Covector E M (x : M))
    (x₀ : M) (x : U) (v : E) :
    inCoordinates E M a x₀ x v =
      a x ((trivializationAt E (TangentSpace 𝓘(ℝ, E) : M → Type) x₀).symmL ℝ x v) := by
  simp [inCoordinates_eq, ContinuousLinearMap.inCoordinates]

/-- At its own native chart centre the coordinate covector is exactly
the original fibre covector, using the native tangent-coordinate identity. -/
theorem inCoordinates_self {U : Opens M} (a : ∀ x : U, Covector E M (x : M)) (x : U) :
    inCoordinates E M a (x : M) x = covectorAsModel E M (a x) := by
  ext v
  rw [inCoordinates_apply]
  congr 1
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source E (x : M))]
  exact (tangentBundleCore 𝓘(ℝ, E) M).coordChange_self
    (achart E (x : M)) x (mem_chart_source E (x : M)) v

/-- Smoothness of the native total-space map is equivalent to smoothness
of its native coordinates at the chosen chart centre. -/
theorem smoothSectionAt_iff {U : Opens M}
    (a : ∀ x : U, Covector E M (x : M)) (x : U) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
        (sectionMap E M a) x ↔
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] ℂ) ∞
        (inCoordinates E M a (x : M)) x := by
  rw [Bundle.contMDiffAt_totalSpace]
  exact and_iff_right (contMDiff_subtype_val x)

/-- Smoothness of original dependent cotangent sections is a genuine
local predicate, with literal restrictions on the original open sets. -/
def smoothLocalPredicate :
    TopCat.LocalPredicate (fun x : TopCat.of M => Covector E M x) where
  pred {U} a := ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
    (sectionMap E M a)
  res {U V} i a ha := ha.comp (contMDiff_inclusion i.le)
  locality {U} a ha := by
    let P := (contDiffWithinAt_localInvariantProp
      (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞).localPredicate
        M (CotangentBundle E M)
    apply P.locality (sectionMap E M a)
    intro x
    obtain ⟨V, hV, i, h⟩ := ha x
    exact ⟨V, hV, i, h⟩

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms
