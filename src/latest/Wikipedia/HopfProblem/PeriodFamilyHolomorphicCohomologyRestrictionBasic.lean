import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageZeroBasic

/-!
# The original period family restricted to an open base

The restricted period data are the original three holomorphic functions
composed with the literal open-subtype inclusion.  The underlying topological
identification with the full base preimage only regroups subtype pairs.  Its
holomorphicity for the two actual quotient atlases is proved separately.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

/-- The actual period map restricted through the original open inclusion. -/
def restrictedPeriods (P : HolomorphicPeriodMap V B) (U : Opens B) :
    HolomorphicPeriodMap V U where
  point b := P.point b
  holomorphic_tau := P.holomorphic_tau.comp contMDiff_subtype_val
  holomorphic_mu := P.holomorphic_mu.comp contMDiff_subtype_val
  holomorphic_beta := P.holomorphic_beta.comp contMDiff_subtype_val

@[simp] theorem restrictedPeriods_point (P : HolomorphicPeriodMap V B) (U : Opens B)
    (b : U) : (restrictedPeriods P U).point b = P.point b := rfl

@[simp] theorem restrictedPeriods_periodEquiv (P : HolomorphicPeriodMap V B) (U : Opens B)
    (b : U) : (restrictedPeriods P U).periodEquiv b = P.periodEquiv b := rfl

/-- The literal map from the restricted family to the original full preimage. -/
def toPreimage (P : HolomorphicPeriodMap V B) (U : Opens B) :
    (restrictedPeriods P U).TotalSpace → Zero.basePreimage P U :=
  fun x => ⟨((x.1 : B), x.2), x.1.property⟩

/-- The literal inverse pair-regrouping map. -/
def fromPreimage (P : HolomorphicPeriodMap V B) (U : Opens B) :
    Zero.basePreimage P U → (restrictedPeriods P U).TotalSpace :=
  fun x => (⟨x.val.1, x.property⟩, x.val.2)

@[simp] theorem toPreimage_val (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : (restrictedPeriods P U).TotalSpace) :
    (toPreimage P U x : P.TotalSpace) = ((x.1 : B), x.2) := rfl

@[simp] theorem fromPreimage_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : Zero.basePreimage P U) :
    fromPreimage P U x = (⟨x.val.1, x.property⟩, x.val.2) := rfl

@[simp] theorem fromPreimage_toPreimage (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : (restrictedPeriods P U).TotalSpace) : fromPreimage P U (toPreimage P U x) = x := rfl

@[simp] theorem toPreimage_fromPreimage (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : Zero.basePreimage P U) : toPreimage P U (fromPreimage P U x) = x := rfl

/-- This is a homeomorphism of the original quotient topological spaces. -/
def restrictionHomeomorph (P : HolomorphicPeriodMap V B) (U : Opens B) :
    (restrictedPeriods P U).TotalSpace ≃ₜ Zero.basePreimage P U where
  toFun := toPreimage P U
  invFun := fromPreimage P U
  left_inv := fromPreimage_toPreimage P U
  right_inv := toPreimage_fromPreimage P U
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)

@[simp] theorem restrictionHomeomorph_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : (restrictedPeriods P U).TotalSpace) :
    restrictionHomeomorph P U x = toPreimage P U x := rfl

@[simp] theorem restrictionHomeomorph_symm_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : Zero.basePreimage P U) :
    (restrictionHomeomorph P U).symm x = fromPreimage P U x := rfl

/-- The covering square commutes for the original complex-vector covering maps. -/
@[simp] theorem toPreimage_quotientMap (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : U × ComplexPlane₂) :
    toPreimage P U ((restrictedPeriods P U).quotientMap x) =
      (⟨P.quotientMap ((x.1 : B), x.2), x.1.property⟩ : Zero.basePreimage P U) := rfl

/-- The projection square commutes literally, as a map into the base open. -/
@[simp] theorem baseProjection_toPreimage (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : (restrictedPeriods P U).TotalSpace) :
    Zero.baseProjection P U (toPreimage P U x) = (restrictedPeriods P U).projection x := rfl

@[simp] theorem projection_fromPreimage (P : HolomorphicPeriodMap V B) (U : Opens B)
    (x : Zero.basePreimage P U) :
    (restrictedPeriods P U).projection (fromPreimage P U x) = Zero.baseProjection P U x := rfl

/-- The original zero sections agree under the literal restriction map. -/
@[simp] theorem toPreimage_zeroSection (P : HolomorphicPeriodMap V B) (U : Opens B) (b : U) :
    toPreimage P U ((restrictedPeriods P U).zeroSection b) = Zero.zeroSectionOn P U b := rfl

/-- The genuine complex period-torus inclusions are unchanged by restriction. -/
@[simp] theorem toPreimage_fibreInclusion (P : HolomorphicPeriodMap V B) (U : Opens B)
    (b : U) (z : (P.point b).Torus) :
    toPreimage P U ((restrictedPeriods P U).fibreInclusion b z) = Zero.fibreOn P U b z := rfl

@[simp] theorem fromPreimage_fibreOn (P : HolomorphicPeriodMap V B) (U : Opens B)
    (b : U) (z : (P.point b).Torus) :
    fromPreimage P U (Zero.fibreOn P U b z) = (restrictedPeriods P U).fibreInclusion b z := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Restriction
