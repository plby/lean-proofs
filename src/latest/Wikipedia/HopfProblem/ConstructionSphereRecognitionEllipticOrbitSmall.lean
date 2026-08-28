import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitSurface
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitSmallAction

/-!
# The actual small-cap circle quotient

The previously proved native small-cap product restricts only the root
radius.  Applying the genuine central-surface orbit map gives an open
quotient whose fibres are exactly the original small-cap circle orbits.
This identifies the actual orbit space with the original root ball times
the surviving finite affine quotient.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling
open EllipticModel EllipticOrbitFlat EllipticSmallProduct EllipticGamma

local notation "Circle" => AddCircle (1 : ℝ)

/-- The original small product followed only by the actual surface orbit map. -/
def smallOrbitMap (j : Kind) :
    C(Threefold.SpecialEllipticPiece j, RootBall j × FibreModel j) :=
  (ContinuousMap.prodMap (ContinuousMap.id (RootBall j))
    (surfaceModelMap (specialLocalData j))).comp
      (smallProductHomeomorph j : C(_, _))

@[simp] theorem smallOrbitMap_apply (j : Kind) (x : Threefold.SpecialEllipticPiece j) :
    smallOrbitMap j x =
      ((smallProductHomeomorph j x).1,
        surfaceModelMap (specialLocalData j) (smallProductHomeomorph j x).2) := rfl

theorem smallOrbitMap_isOpenQuotientMap (j : Kind) :
    IsOpenQuotientMap (smallOrbitMap j) :=
  (IsOpenQuotientMap.id.prodMap (surfaceModelMap_isOpenQuotientMap
    (specialLocalData j))).comp (smallProductHomeomorph j).isOpenQuotientMap

/-- The exact original small root and four-period representative formula. -/
@[simp] theorem smallOrbitMap_quotient (j : Kind) (s : RootBall j) (x : RealTorus₄) :
    smallOrbitMap j (smallQuotient j s x) =
      (rootBallRotate j (normalizedGamma j x) s, fibreModelProjection j (dropDelta x)) := by
  rw [smallOrbitMap_apply, smallProductHomeomorph_quotient]
  change (rootBallRotate j (normalizedGamma j x) s,
    surfaceModelMap (specialLocalData j) (surfaceCover (specialLocalData j) x)) = _
  rw [surfaceModelMap_surfaceCover]

/-- The original inclusion into the full cap preserves both quotient coordinates. -/
theorem smallOrbitMap_full (j : Kind) (x : Threefold.SpecialEllipticPiece j) :
    (((smallOrbitMap j x).1 : Disc), (smallOrbitMap j x).2) =
      fullOrbitMap (specialLocalData j) (x.val : SpecialFullFilling j) :=
  (fullOrbitMap_originalProduct (specialLocalData j) (x.val : SpecialFullFilling j)).symm

theorem smallOrbitMap_eq_iff_full (j : Kind) (x y : Threefold.SpecialEllipticPiece j) :
    smallOrbitMap j x = smallOrbitMap j y ↔
      fullOrbitMap (specialLocalData j) (x.val : SpecialFullFilling j) =
        fullOrbitMap (specialLocalData j) (y.val : SpecialFullFilling j) := by
  have hp : Function.Injective (fun p : RootBall j × FibreModel j => (p.1.val, p.2)) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg (fun z : Disc × FibreModel j => z.1) h))
      (congrArg (fun z : Disc × FibreModel j => z.2) h)
  have hx := smallOrbitMap_full j x
  have hy := smallOrbitMap_full j y
  constructor
  · intro h
    exact hx.symm.trans ((congrArg (fun p : RootBall j × FibreModel j => (p.1.val, p.2)) h).trans hy)
  · intro h
    exact hp (hx.trans (h.trans hy.symm))

/-- The small-piece orbit relation is precisely the fibres of its original product quotient. -/
theorem smallOrbitMap_eq_iff (j : Kind) (x y : Threefold.SpecialEllipticPiece j) :
    smallOrbitMap j x = smallOrbitMap j y ↔ ∃ d : Circle, smallCircleFlow j d y = x := by
  rw [smallOrbitMap_eq_iff_full, fullOrbitMap_eq_iff]
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨d, Subtype.ext hd⟩
  · rintro ⟨d, hd⟩
    exact ⟨d, congrArg Subtype.val hd⟩

/-- The actual small-cap circle orbit space, with its original quotient topology. -/
def smallOrbitHomeomorph (j : Kind) : SmallOrbit j ≃ₜ RootBall j × FibreModel j :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph
    (smallOrbitProjection j) (smallOrbitMap j)
    (smallOrbitProjection_isOpenQuotientMap j).isQuotientMap
    (smallOrbitMap_isOpenQuotientMap j).isQuotientMap
    (fun x y => (smallOrbitProjection_eq_iff j x y).trans (smallOrbitMap_eq_iff j x y).symm)

@[simp] theorem smallOrbitHomeomorph_projection (j : Kind)
    (x : Threefold.SpecialEllipticPiece j) :
    smallOrbitHomeomorph j (smallOrbitProjection j x) = smallOrbitMap j x :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph_apply _ _ _ _ _ x

@[simp] theorem smallOrbitHomeomorph_quotient (j : Kind) (s : RootBall j) (x : RealTorus₄) :
    smallOrbitHomeomorph j (smallOrbitProjection j (smallQuotient j s x)) =
      (rootBallRotate j (normalizedGamma j x) s, fibreModelProjection j (dropDelta x)) := by
  rw [smallOrbitHomeomorph_projection, smallOrbitMap_quotient]

/-- Its inverse returns the literal native small-cap representative with the opposite phase. -/
theorem smallOrbitHomeomorph_symm_project (j : Kind) (s : RootBall j) (x : RealTorus₄) :
    (smallOrbitHomeomorph j).symm (s, fibreModelProjection j (dropDelta x)) =
      smallOrbitProjection j (smallQuotient j (rootBallRotate j (-normalizedGamma j x) s) x) := by
  apply (smallOrbitHomeomorph j).injective
  rw [Homeomorph.apply_symm_apply, smallOrbitHomeomorph_quotient]
  apply Prod.ext
  · apply Subtype.ext
    exact (rotate_rotate_neg (normalizedGamma j x) s.val).symm
  · rfl

/-- The actual inclusion of small into full circle orbit spaces. -/
def smallToFullOrbit (j : Kind) : SmallOrbit j → FullOrbit (specialLocalData j) :=
  Quotient.lift (fun x : Threefold.SpecialEllipticPiece j =>
    fullOrbitProjection (specialLocalData j) (x.val : SpecialFullFilling j)) (by
      rintro x y ⟨d, hd⟩
      apply (fullOrbitProjection_eq_iff (specialLocalData j) _ _).mpr
      exact ⟨d, congrArg Subtype.val hd⟩)

@[simp] theorem smallToFullOrbit_projection (j : Kind) (x : Threefold.SpecialEllipticPiece j) :
    smallToFullOrbit j (smallOrbitProjection j x) =
      fullOrbitProjection (specialLocalData j) (x.val : SpecialFullFilling j) := rfl

/-- The whole small/full comparison is exactly the ordinary root-ball inclusion. -/
theorem smallToFullOrbit_coordinates (j : Kind) (x : SmallOrbit j) :
    fullOrbitHomeomorph (specialLocalData j) (smallToFullOrbit j x) =
      (((smallOrbitHomeomorph j x).1 : Disc), (smallOrbitHomeomorph j x).2) := by
  obtain ⟨y, rfl⟩ := smallOrbitProjection_surjective j x
  rw [smallToFullOrbit_projection, smallOrbitHomeomorph_projection]
  exact (smallOrbitMap_full j y).symm

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

