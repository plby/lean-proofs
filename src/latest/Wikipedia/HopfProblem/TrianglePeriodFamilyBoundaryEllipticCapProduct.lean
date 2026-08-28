import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductCore
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductConjugacy
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusSurface
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticCap

/-!
# The actual elliptic cap boundary is its central surface times a circle

The primitive twist coordinates conjugate the original affine monodromy to
the finite circle twist.  The explicit product homeomorphism for that twist
then identifies the original boundary mapping torus with the original
central surface times an additive circle.  Its first coordinate is exactly
the original boundary inclusion followed by the actual radial retraction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open Elliptic Elliptic.HigherHomology Elliptic.HigherHomology.MappingTorusQuotient
open SpecialPeriods SpecialPeriods.EllipticFilling

local notation "E" => ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary

/-- The original affine elliptic boundary in the verified primitive twist coordinates. -/
def splitBoundaryHomeomorph (j : Kind) :
    E j ≃ₜ MappingTorus.Torus (twist j.order (fibreTorusHomeomorph j)) :=
  mappingTorusConjugacy (flatTorusAffine j j.twist)
    (twist j.order (fibreTorusHomeomorph j)) (splitFlatTorusHomeomorph j)
    (splitFlatTorusHomeomorph_flatTorusAffine j)

@[simp] theorem splitBoundaryHomeomorph_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    splitBoundaryHomeomorph j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      MappingTorus.mk (twist j.order (fibreTorusHomeomorph j))
        (t, splitFlatTorusHomeomorph j x) := rfl

/-- The genuine product homeomorphism, retaining the original central surface. -/
def boundaryProductHomeomorph (j : Kind) :
    E j ≃ₜ ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j ×
      MappingTorus.Circle :=
  (splitBoundaryHomeomorph j).trans
    ((twistProductHomeomorph j.order (fibreTorusHomeomorph j)
      (fibreTorusHomeomorph_pow_order j)).trans
        (((surfaceSplitQuotientHomeomorph j (specialLocalData j).centralPeriod).symm).prodCongr
          (Homeomorph.refl MappingTorus.Circle)))

/-- The period splitting and the flat splitting retain precisely the original
real-period torus identification. -/
theorem splitPeriodTorusHomeomorph_symm_splitFlat (j : Kind) (p : PeriodDomain)
    (x : RealTorus₄) :
    (splitPeriodTorusHomeomorph j p).symm (splitFlatTorusHomeomorph j x) =
      flatTorusPeriodHomeomorph p x := by
  apply (splitPeriodTorusHomeomorph j p).injective
  rw [Homeomorph.apply_symm_apply]
  change splitFlatTorusHomeomorph j x =
    splitFlatTorusHomeomorph j
      ((flatTorusPeriodHomeomorph p).symm (flatTorusPeriodHomeomorph p x))
  rw [Homeomorph.symm_apply_apply]

/-- On every actual cylinder representative the first coordinate is the
original cap retraction; the second is the invariant primitive twist coordinate. -/
theorem boundaryProductHomeomorph_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    boundaryProductHomeomorph j (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j
        (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)),
        (splitFlatTorusHomeomorph j x).1 +
          ((t / j.order : ℝ) : MappingTorus.Circle)) := by
  rw [boundaryProductHomeomorph, Homeomorph.trans_apply, splitBoundaryHomeomorph_mk,
    Homeomorph.trans_apply]
  change ((surfaceSplitQuotientHomeomorph j (specialLocalData j).centralPeriod).symm
      (project j.order (fibreTorusHomeomorph j) (fibreTorusHomeomorph_pow_order j)
        (splitFlatTorusHomeomorph j x)),
      (splitFlatTorusHomeomorph j x).1 + ((t / j.order : ℝ) : MappingTorus.Circle)) = _
  rw [surfaceSplitQuotientHomeomorph_symm_project,
    splitPeriodTorusHomeomorph_symm_splitFlat,
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk]

/-- The product projection is the literal cap map on every point, not only
on fibre classes or on an abstractly identified homology group. -/
theorem boundaryProductHomeomorph_fst (j : Kind) (q : E j) :
    (boundaryProductHomeomorph j q).1 =
      ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j q := by
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective (flatTorusAffine j j.twist) q
  exact congrArg Prod.fst (boundaryProductHomeomorph_mk j t x)

/-- Equality of actual continuous maps preserving the original cap projection. -/
theorem boundaryProductHomeomorph_fst_comp (j : Kind) :
    (ContinuousMap.fst : C(ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j ×
      MappingTorus.Circle, ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j)).comp
        (boundaryProductHomeomorph j : C(_, _)) =
      ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j := by
  ext q
  exact boundaryProductHomeomorph_fst j q

/-- The actual boundary circle coordinate, including the sign of the
primitive main twist in the order-four case. -/
def boundaryCircleCoordinate (j : Kind) : C(E j, MappingTorus.Circle) :=
  (ContinuousMap.snd : C(ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j ×
    MappingTorus.Circle, MappingTorus.Circle)).comp (boundaryProductHomeomorph j : C(_, _))

theorem boundaryCircleCoordinate_realCoordinates (j : Kind) (t : ℝ)
    (x : RealCoordinates) :
    boundaryCircleCoordinate j
      (MappingTorus.mk (flatTorusAffine j j.twist) (t, standardLattice.mkQ x)) =
        ((((j.twist 0 : ℝ) * x 0 + t / j.order : ℝ)) : MappingTorus.Circle) := by
  change (boundaryProductHomeomorph j
    (MappingTorus.mk (flatTorusAffine j j.twist) (t, standardLattice.mkQ x))).2 = _
  rw [boundaryProductHomeomorph_mk, splitFlatTorusHomeomorph_mkQ]
  exact (AddCircle.coe_add _ _ _).symm

/-- Fixing the new circle coordinate to zero gives a genuine continuous
section of the original boundary-to-central-surface map. -/
def capSection (j : Kind) :
    C(ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j, E j) :=
  ((boundaryProductHomeomorph j).symm : C(_, _)).comp
    ⟨fun x => (x, (0 : MappingTorus.Circle)), continuous_id.prodMk continuous_const⟩

@[simp] theorem specialBoundaryToCentral_capSection (j : Kind)
    (x : ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) :
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j (capSection j x) = x := by
  rw [← boundaryProductHomeomorph_fst]
  change (boundaryProductHomeomorph j ((boundaryProductHomeomorph j).symm (x, 0))).1 = x
  rw [Homeomorph.apply_symm_apply]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
