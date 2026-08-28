import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRestriction
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleCech
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafOverBase

/-!
# Literal maps from the original restricted period family

For an actual base open, the total-family map forgets only the base
subtype tag and preserves the real torus coordinate. Its holomorphicity
uses the original restriction biholomorphism and both original quotient
atlases. Coefficients and covering coordinates restrict literally.
The actual holomorphic section pullback produces the original pulled-back
period cocycle, without identifying its cover with a newly chosen cover.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open PeriodFamilyHigherDirectImage HolomorphicFunctionSheaf.SphereH1

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The actual map to the original total family forgets only the base tag. -/
def familyMap (P : HolomorphicPeriodMap V B) (A : Opens B) :
    TopCat.of (Restriction.restrictedPeriods P A).TotalSpace ⟶ TopCat.of P.TotalSpace :=
  TopCat.ofHom ⟨fun x => ((x.1 : B), x.2),
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩

@[simp] theorem familyMap_apply (P : HolomorphicPeriodMap V B) (A : Opens B)
    (x : (Restriction.restrictedPeriods P A).TotalSpace) :
    familyMap P A x = ((x.1 : B), x.2) := rfl

/-- The covering-space map forgets the same tag, leaving the complex vector unchanged. -/
def upstairsForget (A : Opens B) : A × ComplexPlane₂ → B × ComplexPlane₂ :=
  fun x => ((x.1 : B), x.2)

theorem upstairsForget_continuous (A : Opens B) : Continuous (upstairsForget A) :=
  (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd

/-- The original quotient-cover square commutes literally. -/
@[simp] theorem familyMap_quotientMap (P : HolomorphicPeriodMap V B) (A : Opens B)
    (x : A × ComplexPlane₂) :
    familyMap P A ((Restriction.restrictedPeriods P A).quotientMap x) =
      P.quotientMap (upstairsForget A x) := rfl

@[simp] theorem familyMap_projection (P : HolomorphicPeriodMap V B) (A : Opens B)
    (x : (Restriction.restrictedPeriods P A).TotalSpace) :
    P.projection (familyMap P A x) =
      ((Restriction.restrictedPeriods P A).projection x : B) := rfl

/-- Restriction of the original four holomorphic coefficient functions. -/
def restrictCoefficients (A : Opens B) (a : Cocycle.Coefficients V B) :
    Cocycle.Coefficients V A := fun j =>
  ⟨fun b => a j b, (a j).contMDiff.comp contMDiff_subtype_val⟩

@[simp] theorem restrictCoefficients_apply (A : Opens B) (a : Cocycle.Coefficients V B)
    (j : Fin 4) (b : A) : restrictCoefficients A a j b = a j b := rfl

/-- The restricted primitive is the original function in the same covering coordinates. -/
theorem primitive_restrictCoefficients (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) (x : A × ComplexPlane₂) :
    Cocycle.primitive (Restriction.restrictedPeriods P A) (restrictCoefficients A a) x =
      Cocycle.primitive P a (upstairsForget A x) := rfl

/-- The cover is the literal inverse image of the original family cover. -/
abbrev familyPullbackCover (P : HolomorphicPeriodMap V B) (A : Opens B) :
    B × ComplexPlane₂ → Opens (Restriction.restrictedPeriods P A).TotalSpace :=
  CechFibre.pullbackCover (familyMap P A) (Cocycle.coverOpen P)

theorem familyPullbackCover_covers (P : HolomorphicPeriodMap V B) (A : Opens B) :
    ∀ x : (Restriction.restrictedPeriods P A).TotalSpace,
      ∃ i : B × ComplexPlane₂, x ∈ familyPullbackCover P A i :=
  CechFibre.pullbackCover_covers (familyMap P A) (Cocycle.coverOpen_covers P)

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual total-family inclusion is holomorphic in the unchanged quotient atlases. -/
theorem familyMap_holomorphic (P : HolomorphicPeriodMap V B) (A : Opens B) :
    letI := (Restriction.restrictedPeriods P A).totalChartedSpace
    letI := P.totalChartedSpace
    ContMDiff IT IT ω (familyMap P A) := by
  let := (Restriction.restrictedPeriods P A).totalChartedSpace
  let := P.totalChartedSpace
  exact (contMDiff_subtype_val (I := IT) (U := Zero.basePreimage P A)).comp
    (Restriction.restrictionBiholomorph P A).contMDiff

/-- The actual holomorphic map bundled with the original two atlases. -/
def familyHolomorphicMap (P : HolomorphicPeriodMap V B) (A : Opens B) :
    letI := (Restriction.restrictedPeriods P A).totalChartedSpace
    letI := P.totalChartedSpace
    ContMDiffMap IT IT (Restriction.restrictedPeriods P A).TotalSpace P.TotalSpace ω := by
  letI := (Restriction.restrictedPeriods P A).totalChartedSpace
  letI := P.totalChartedSpace
  exact ⟨familyMap P A, familyMap_holomorphic P A⟩

/-- The genuine all-open coefficient pullback to the original restricted family. -/
def familyCoefficientPullback (P : HolomorphicPeriodMap V B) (A : Opens B) :
    Zero.totalAdditiveSheaf P ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat (familyMap P A)).obj
        (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P A)) := by
  letI := (Restriction.restrictedPeriods P A).totalChartedSpace
  letI := P.totalChartedSpace
  exact CuspNormalization.SheafOverBase.additivePullback IT IT
    (𝟙 (TopCat.of P.TotalSpace)) (familyMap P A) (familyHolomorphicMap P A) (fun _ => rfl)

/-- Literal pullback gives the original period cocycle on that original inverse-image cover. -/
def familyPullbackCocycle (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) :
    CechOneCocycle (Zero.totalAdditiveSheaf (Restriction.restrictedPeriods P A))
      (familyPullbackCover P A) :=
  CechFibre.pullbackCocycle (familyMap P A) (familyCoefficientPullback P A)
    (Cocycle.cocycle P a)

/-- The pulled-back values are the original primitive differences at the same family point. -/
theorem familyPullbackCocycle_value_apply (P : HolomorphicPeriodMap V B) (A : Opens B)
    (a : Cocycle.Coefficients V B) (i j : B × ComplexPlane₂)
    (x : ↥(familyPullbackCover P A i ⊓ familyPullbackCover P A j)) :
    Subtype.val ((familyPullbackCocycle P A a).value i j :
      Cocycle.NativeSection (Restriction.restrictedPeriods P A)
        (familyPullbackCover P A i ⊓ familyPullbackCover P A j)) x =
      Cocycle.primitive P a (Cocycle.lift P i (familyMap P A x)) -
        Cocycle.primitive P a (Cocycle.lift P j (familyMap P A x)) := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
