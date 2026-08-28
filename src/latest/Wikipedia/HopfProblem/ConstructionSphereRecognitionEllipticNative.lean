import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticAction
import Wikipedia.HopfProblem.EllipticEquivariantFillings
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticAction

/-!
# The original elliptic filling and its literal finite-action model

The original clockwise base rotation is exactly rotation by `-1/m` in
the native additive circle.  Consequently the identity on the original
disc times the real period torus conjugates the two finite actions.  On
the fibre, the original period-coordinate homeomorphism identifies the
real affine quotient with the actual central elliptic surface.

Both quotient comparisons retain their literal representatives in both
directions.  These are topological comparisons, not replacements of the
native smooth or complex atlas.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticNative

open Elliptic SpecialPeriods EllipticModel
open Elliptic.HigherHomology.MappingTorusQuotient
open ThreefoldOverlapMappingTorus.Elliptic (affine_pow_order)

/-- The original family generator uses the negative primitive sector angle. -/
theorem rotate_neg_sector (j : Kind) (s : Disc) :
    rotate (-sector j.order) s = familyRotation j s := by
  apply Subtype.ext
  rw [sector, ← AddCircle.coe_neg, rotate_real, LogGauge.familyRotation_val_exponential]
  have h : (((-(1 / (j.order : ℝ))) : ℝ) : ℂ) = -(1 / (j.order : ℂ)) := by
    push_cast
    rfl
  rw [h]

/-- Equality with the literal native affine generator, before taking any quotient. -/
theorem capPermutation_native (j : Kind) (v : Lattice) (x : Disc × RealTorus₄) :
    capPermutation j.order (flatTorusAffine j v) x = familyPermutation j v x := by
  rw [capPermutation_apply, familyPermutation_apply, rotate_neg_sector]

variable {j : Kind} (D : Equivariant.Data j)

/-- The identity on the actual covering family identifies the original filling
with the explicit clockwise-disc finite-action quotient. -/
def capHomeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    D.Space v hv ≃ₜ
      CapQuotient j.order (flatTorusAffine j v) (affine_pow_order j v hv.1) :=
  cyclicQuotientCongr (D.permutation v) (D.permutation_pow_order v hv.1)
    (capPermutation j.order (flatTorusAffine j v))
    (capPermutation_pow_order j.order (flatTorusAffine j v) (affine_pow_order j v hv.1))
    (Homeomorph.refl (Disc × RealTorus₄))
    (fun x => (capPermutation_native j v x).symm)

/-- No coordinate or representative is changed by the native cap comparison. -/
@[simp] theorem capHomeomorph_quotient (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.TotalSpace) :
    capHomeomorph D v hv (D.quotient v hv x) =
      capProject j.order (flatTorusAffine j v) (affine_pow_order j v hv.1) x := rfl

/-- The inverse returns precisely the original filling quotient representative. -/
@[simp] theorem capHomeomorph_symm_capProject (v : Lattice) (hv : AdmissibleTwist j v)
    (x : Disc × RealTorus₄) :
    (capHomeomorph D v hv).symm
      (capProject j.order (flatTorusAffine j v) (affine_pow_order j v hv.1) x) =
        D.quotient v hv x := rfl

/-- The original period-coordinate change descends to the actual elliptic surface. -/
def fibreSurfaceHomeomorph (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) :
    FibreQuotient j.order (flatTorusAffine j v) (affine_pow_order j v hv.1) ≃ₜ
      Surface j p v hv :=
  cyclicQuotientCongr (flatTorusAffine j v).toEquiv
    (fibrePermutation_pow_order j.order (flatTorusAffine j v) (affine_pow_order j v hv.1))
    (affinePermutation j p v) (affinePermutation_pow_order j p v hv.1)
    (flatTorusPeriodHomeomorph p.val) (flatTorusAffine_periodHomeomorph j p v)

/-- The fibre quotient is mapped by the literal original period map and surface projection. -/
@[simp] theorem fibreSurfaceHomeomorph_project (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (x : RealTorus₄) :
    fibreSurfaceHomeomorph j p v hv
      (fibreProject j.order (flatTorusAffine j v) (affine_pow_order j v hv.1) x) =
        surfaceProjection j p v hv (flatTorusPeriodHomeomorph p.val x) := rfl

/-- Original real period representatives retain all four coordinates. -/
@[simp] theorem fibreSurfaceHomeomorph_project_mkQ (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (x : RealPlane₄) :
    fibreSurfaceHomeomorph j p v hv
      (fibreProject j.order (flatTorusAffine j v) (affine_pow_order j v hv.1)
        (standardLattice.mkQ x)) =
      surfaceProjection j p v hv (flatProjection p.val x) := by
  rw [fibreSurfaceHomeomorph_project, flatTorusPeriodHomeomorph_mkQ]

/-- The inverse has the exact inverse period-coordinate formula. -/
@[simp] theorem fibreSurfaceHomeomorph_symm_surfaceProjection (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (x : p.val.Torus) :
    (fibreSurfaceHomeomorph j p v hv).symm (surfaceProjection j p v hv x) =
      fibreProject j.order (flatTorusAffine j v) (affine_pow_order j v hv.1)
        ((flatTorusPeriodHomeomorph p.val).symm x) := rfl

/-- The inverse on native flat representatives returns the original real torus class. -/
@[simp] theorem fibreSurfaceHomeomorph_symm_flatProjection (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (x : RealPlane₄) :
    (fibreSurfaceHomeomorph j p v hv).symm
      (surfaceProjection j p v hv (flatProjection p.val x)) =
        fibreProject j.order (flatTorusAffine j v) (affine_pow_order j v hv.1)
          (standardLattice.mkQ x) := by
  rw [fibreSurfaceHomeomorph_symm_surfaceProjection,
    flatTorusPeriodHomeomorph_symm_flatProjection]

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticNative
