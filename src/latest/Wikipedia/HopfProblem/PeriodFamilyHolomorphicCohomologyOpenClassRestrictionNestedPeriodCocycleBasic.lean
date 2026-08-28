import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRestrictionNaturality
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleCech
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafOverBase

/-!
# Literal period-cocycle pullback between nested base opens

The coefficients are defined only on the larger base open. Both total
spaces retain their original varying-period quotient atlases, and the
inclusion preserves the real torus coordinate. The coefficient sheaf map
is the actual all-open pullback along that holomorphic inclusion.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.NestedPeriodCocycle

open PeriodFamilyHigherDirectImage HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  {U W : Opens B}

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The genuine inclusion of the two original restricted total spaces. -/
def familyMap (P : HolomorphicPeriodMap V B) (h : U ≤ W) :
    TopCat.of (Restriction.restrictedPeriods P U).TotalSpace ⟶
      TopCat.of (Restriction.restrictedPeriods P W).TotalSpace :=
  TopCat.ofHom ⟨Restriction.restrictionInclusion P h,
    ((Opens.isOpenEmbedding_of_le h).continuous.comp continuous_fst).prodMk continuous_snd⟩

@[simp] theorem familyMap_apply (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (x : (Restriction.restrictedPeriods P U).TotalSpace) :
    familyMap P h x = (Opens.inclusion h x.1, x.2) := rfl

/-- The corresponding inclusion of the original covering spaces. -/
def upstairsInclusion (h : U ≤ W) : U × ComplexPlane₂ → W × ComplexPlane₂ :=
  fun x => (Opens.inclusion h x.1, x.2)

theorem upstairsInclusion_continuous (h : U ≤ W) : Continuous (upstairsInclusion h) :=
  ((Opens.isOpenEmbedding_of_le h).continuous.comp continuous_fst).prodMk continuous_snd

/-- The original quotient square commutes without changing covering coordinates. -/
@[simp] theorem familyMap_quotientMap (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (x : U × ComplexPlane₂) :
    familyMap P h ((Restriction.restrictedPeriods P U).quotientMap x) =
      (Restriction.restrictedPeriods P W).quotientMap (upstairsInclusion h x) := rfl

@[simp] theorem familyMap_projection (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (x : (Restriction.restrictedPeriods P U).TotalSpace) :
    (Restriction.restrictedPeriods P W).projection (familyMap P h x) =
      Opens.inclusion h ((Restriction.restrictedPeriods P U).projection x) := rfl

/-- Literal restriction of four holomorphic functions defined only on the larger open. -/
def restrictedCoefficients (h : U ≤ W) (a : Cocycle.Coefficients V W) :
    Cocycle.Coefficients V U := fun j =>
  ⟨fun b => a j (Opens.inclusion h b), (a j).contMDiff.comp (contMDiff_inclusion h)⟩

@[simp] theorem restrictedCoefficients_apply (h : U ≤ W)
    (a : Cocycle.Coefficients V W) (j : Fin 4) (b : U) :
    restrictedCoefficients h a j b = a j (Opens.inclusion h b) := rfl

/-- The two original primitives agree in the unchanged covering coordinates. -/
theorem primitive_restrictedCoefficients (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) (x : U × ComplexPlane₂) :
    Cocycle.primitive (Restriction.restrictedPeriods P U) (restrictedCoefficients h a) x =
      Cocycle.primitive (Restriction.restrictedPeriods P W) a (upstairsInclusion h x) := rfl

/-- The literal inverse image of the independently chosen larger-family cover. -/
abbrev pullbackCover (P : HolomorphicPeriodMap V B) (h : U ≤ W) :
    W × ComplexPlane₂ → Opens (Restriction.restrictedPeriods P U).TotalSpace :=
  CechFibre.pullbackCover (familyMap P h)
    (Cocycle.coverOpen (Restriction.restrictedPeriods P W))

theorem pullbackCover_covers (P : HolomorphicPeriodMap V B) (h : U ≤ W) :
    ∀ x : (Restriction.restrictedPeriods P U).TotalSpace,
      ∃ i : W × ComplexPlane₂, x ∈ pullbackCover P h i :=
  CechFibre.pullbackCover_covers (familyMap P h)
    (Cocycle.coverOpen_covers (Restriction.restrictedPeriods P W))

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Holomorphy is in the two original total-space quotient atlases. -/
theorem familyMap_holomorphic (P : HolomorphicPeriodMap V B) (h : U ≤ W) :
    letI := (Restriction.restrictedPeriods P U).totalChartedSpace
    letI := (Restriction.restrictedPeriods P W).totalChartedSpace
    ContMDiff IT IT ω (familyMap P h) :=
  Restriction.restrictionInclusion_holomorphic P h

/-- The actual nested inclusion bundled as a holomorphic map. -/
def familyHolomorphicMap (P : HolomorphicPeriodMap V B) (h : U ≤ W) :
    letI := (Restriction.restrictedPeriods P U).totalChartedSpace
    letI := (Restriction.restrictedPeriods P W).totalChartedSpace
    ContMDiffMap IT IT (Restriction.restrictedPeriods P U).TotalSpace
      (Restriction.restrictedPeriods P W).TotalSpace ω := by
  letI := (Restriction.restrictedPeriods P U).totalChartedSpace
  letI := (Restriction.restrictedPeriods P W).totalChartedSpace
  exact ⟨familyMap P h, familyMap_holomorphic P h⟩

/-- The genuine all-open pullback of holomorphic coefficient sections. -/
def coefficientPullback (P : HolomorphicPeriodMap V B) (h : U ≤ W) :
    Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P W) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat (familyMap P h)).obj
        (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P U)) := by
  letI := (Restriction.restrictedPeriods P U).totalChartedSpace
  letI := (Restriction.restrictedPeriods P W).totalChartedSpace
  exact CuspNormalization.SheafOverBase.additivePullback IT IT
    (𝟙 (TopCat.of (Restriction.restrictedPeriods P W).TotalSpace))
    (familyMap P h) (familyHolomorphicMap P h) (fun _ => rfl)

/-- Actual Čech pullback on the literal inverse-image cover. -/
def pullbackCocycle (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) :
    CechOneCocycle (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P U))
      (pullbackCover P h) :=
  CechFibre.pullbackCocycle (familyMap P h) (coefficientPullback P h)
    (Cocycle.cocycle (Restriction.restrictedPeriods P W) a)

/-- Pulled-back values are the original primitive differences at the included point. -/
theorem pullbackCocycle_value_apply (P : HolomorphicPeriodMap V B) (h : U ≤ W)
    (a : Cocycle.Coefficients V W) (i j : W × ComplexPlane₂)
    (x : ↥(pullbackCover P h i ⊓ pullbackCover P h j)) :
    Subtype.val ((pullbackCocycle P h a).value i j :
      Cocycle.NativeSection (Restriction.restrictedPeriods P U)
        (pullbackCover P h i ⊓ pullbackCover P h j)) x =
      Cocycle.primitive (Restriction.restrictedPeriods P W) a
        (Cocycle.lift (Restriction.restrictedPeriods P W) i (familyMap P h x)) -
      Cocycle.primitive (Restriction.restrictedPeriods P W) a
        (Cocycle.lift (Restriction.restrictedPeriods P W) j (familyMap P h x)) := rfl

end OpenClassRestriction.NestedPeriodCocycle
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
