import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticFullProduct

/-!
# Product coordinates on the original small elliptic pieces

The full product homeomorphism preserves the actual root radius.  Restricting
it therefore identifies the original small piece, with its original radius
predicate, with the corresponding root ball times the actual central surface.
Both directions retain the native filling quotient representatives.

This is a restriction of a proved topological homeomorphism.  No smooth
product structure, different gluing map, or ball recognition is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmallProduct

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling
open ThreefoldOverlapMappingTorus.Elliptic
open EllipticModel EllipticGamma EllipticFullProduct

/-- The actual root-radius subdomain of the original open unit disc. -/
abbrev RootBall (j : Kind) :=
  {s : Disc // ‖(s : ℂ)‖ ^ j.order < Threefold.specialBaseCover.radius (some j)}

/-- The original projection norm is exactly the order-th power of the product root radius. -/
theorem fullProduct_norm_pow (j : Kind) (y : SpecialFullFilling j) :
    ‖((specialFillingProductHomeomorph j y).1 : ℂ)‖ ^ j.order =
      ‖(specialFullFillingProjection j y : ℂ)‖ := by
  obtain ⟨⟨s, x⟩, rfl⟩ :=
    (specialLocalData j).quotient_surjective j.twist (mainTwist_admissible j) y
  change ‖((fillingProductHomeomorph (specialLocalData j)
    ((specialLocalData j).quotient j.twist (mainTwist_admissible j) (s, x))).1 : ℂ)‖ ^
      j.order = ‖(discPower j.order j.order_pos s : ℂ)‖
  rw [fillingProductHomeomorph_quotient_norm, discPower_coe, norm_pow]

/-- Restriction of the original full product to the original small-piece predicate. -/
def smallSubtypeHomeomorph (j : Kind) :
    Threefold.SpecialEllipticPiece j ≃ₜ
      {p : Disc × BoundaryCentralSurface j //
        ‖(p.1 : ℂ)‖ ^ j.order < Threefold.specialBaseCover.radius (some j)} :=
  (specialFillingProductHomeomorph j).subtype (by
    intro y
    change ‖(specialFullFillingProjection j y : ℂ)‖ <
        Threefold.specialBaseCover.radius (some j) ↔
      ‖((specialFillingProductHomeomorph j y).1 : ℂ)‖ ^ j.order <
        Threefold.specialBaseCover.radius (some j)
    rw [fullProduct_norm_pow])

/-- Move the radius predicate onto precisely the first product factor. -/
def rootBallProductHomeomorph (j : Kind) :
    {p : Disc × BoundaryCentralSurface j //
      ‖(p.1 : ℂ)‖ ^ j.order < Threefold.specialBaseCover.radius (some j)} ≃ₜ
      RootBall j × BoundaryCentralSurface j where
  toFun p := (⟨p.val.1, p.property⟩, p.val.2)
  invFun p := ⟨(p.1.val, p.2), p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk
    continuous_subtype_val.snd
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk
    continuous_snd).subtype_mk _

/-- The actual small elliptic gluing piece is its original root ball times its central surface. -/
def smallProductHomeomorph (j : Kind) :
    Threefold.SpecialEllipticPiece j ≃ₜ RootBall j × BoundaryCentralSurface j :=
  (smallSubtypeHomeomorph j).trans (rootBallProductHomeomorph j)

/-- The first coordinate is the unchanged disc coordinate of the full product. -/
@[simp] theorem smallProductHomeomorph_fst_val (j : Kind)
    (y : Threefold.SpecialEllipticPiece j) :
    ((smallProductHomeomorph j y).1 : Disc) = (specialFillingProductHomeomorph j y.val).1 := rfl

/-- Restricting the domain does not change the surface coordinate. -/
@[simp] theorem smallProductHomeomorph_snd (j : Kind)
    (y : Threefold.SpecialEllipticPiece j) :
    (smallProductHomeomorph j y).2 = (specialFillingProductHomeomorph j y.val).2 := rfl

/-- The small product's second coordinate is the original full-filling radial retraction. -/
theorem smallProductHomeomorph_snd_retraction (j : Kind)
    (y : Threefold.SpecialEllipticPiece j) :
    (smallProductHomeomorph j y).2 =
      (specialLocalData j).fillingSurfaceRetraction j.twist (mainTwist_admissible j) y.val :=
  fillingProductHomeomorph_snd (specialLocalData j) y.val

/-- The inverse is literally the full-product inverse with its original radius proof. -/
@[simp] theorem smallProductHomeomorph_symm_val (j : Kind)
    (p : RootBall j × BoundaryCentralSurface j) :
    ((smallProductHomeomorph j).symm p : SpecialFullFilling j) =
      (specialFillingProductHomeomorph j).symm (p.1.val, p.2) := rfl

/-- The native disc rotation preserves the exact root ball, without changing its radius. -/
def rootBallRotate (j : Kind) (c : EllipticModel.Circle) (s : RootBall j) : RootBall j :=
  ⟨rotate c s.val, by rw [rotate_norm]; exact s.property⟩

@[simp] theorem rootBallRotate_val (j : Kind) (c : EllipticModel.Circle) (s : RootBall j) :
    (rootBallRotate j c s : Disc) = rotate c s.val := rfl

/-- A point of the original small piece, specified by its original root and real-torus point. -/
def smallQuotient (j : Kind) (s : RootBall j) (x : RealTorus₄) :
    Threefold.SpecialEllipticPiece j :=
  ⟨(specialLocalData j).quotient j.twist (mainTwist_admissible j) (s.val, x), by
    change ‖(discPower j.order j.order_pos s.val : ℂ)‖ <
      Threefold.specialBaseCover.radius (some j)
    rw [discPower_coe, norm_pow]
    exact s.property⟩

@[simp] theorem smallQuotient_val (j : Kind) (s : RootBall j) (x : RealTorus₄) :
    (smallQuotient j s x : SpecialFullFilling j) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j) (s.val, x) := rfl

/-- The full forward formula on original small-piece representatives. -/
theorem smallProductHomeomorph_quotient (j : Kind) (s : RootBall j) (x : RealTorus₄) :
    smallProductHomeomorph j (smallQuotient j s x) =
      (rootBallRotate j (normalizedGamma j x) s,
        surfaceProjection j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)
          (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val x)) := by
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst
      (fillingProductHomeomorph_quotient (specialLocalData j) s.val x)
  · rw [smallProductHomeomorph_snd]
    exact congrArg Prod.snd
      (fillingProductHomeomorph_quotient (specialLocalData j) s.val x)

/-- The inverse returns the original small-piece representative with the opposite phase. -/
theorem smallProductHomeomorph_symm_surfaceProjection (j : Kind)
    (s : RootBall j) (x : RealTorus₄) :
    (smallProductHomeomorph j).symm
      (s, surfaceProjection j (specialLocalData j).centralPeriod j.twist (mainTwist_admissible j)
        (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val x)) =
      smallQuotient j (rootBallRotate j (-normalizedGamma j x) s) x := by
  apply Subtype.ext
  rw [smallProductHomeomorph_symm_val, smallQuotient_val]
  exact fillingProductHomeomorph_symm_surfaceProjection (specialLocalData j) s.val x

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticSmallProduct
