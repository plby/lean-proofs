import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitAction
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticSmallProduct
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticSpecial

/-!
# The original circle action on the actual small elliptic piece

The action is the restriction of fourth-column translation on the full
original cap.  The defining small-radius predicate is preserved by the
unchanged base parameter.  The circle quotient retains the native subtype
topology and the real-time formula of the original vertical flow.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

open Elliptic SpecialPeriods SpecialPeriods.EllipticFilling
open SpecialPeriods.Threefold

local notation "Circle" => AddCircle (1 : ℝ)

/-- The original small piece is invariant under the actual full-cap circle. -/
def smallCircleFlow (j : Kind) (d : Circle) (x : SpecialEllipticPiece j) :
    SpecialEllipticPiece j :=
  ⟨fullCircleFlow (specialLocalData j) d x.val, by
    change ‖((specialLocalData j).projection j.twist (mainTwist_admissible j)
      (fullCircleFlow (specialLocalData j) d x.val) : ℂ)‖ < specialBaseCover.radius (some j)
    have he := fullCircleFlow_projection (specialLocalData j) d
      (show (specialLocalData j).Space j.twist (mainTwist_admissible j) from x.val)
    exact (congrArg (fun z : Disc => ‖(z : ℂ)‖) he).trans_lt x.property⟩

@[simp] theorem smallCircleFlow_val (j : Kind) (d : Circle) (x : SpecialEllipticPiece j) :
    (smallCircleFlow j d x : SpecialFullFilling j) =
      fullCircleFlow (specialLocalData j) d x.val := rfl

/-- The descended circle parameter retains the exact native real time. -/
theorem smallCircleFlow_real (j : Kind) (t : ℝ) (x : SpecialEllipticPiece j) :
    smallCircleFlow j (t : Circle) x = VerticalAction.Elliptic.specialFlow j (t : ℂ) x :=
  Subtype.ext (fullCircleFlow_real (specialLocalData j) t x.val)

@[simp] theorem smallCircleFlow_zero (j : Kind) (x : SpecialEllipticPiece j) :
    smallCircleFlow j 0 x = x :=
  Subtype.ext (fullCircleFlow_zero (specialLocalData j) x.val)

theorem smallCircleFlow_add (j : Kind) (d e : Circle) (x : SpecialEllipticPiece j) :
    smallCircleFlow j (d + e) x = smallCircleFlow j d (smallCircleFlow j e x) :=
  Subtype.ext (fullCircleFlow_add (specialLocalData j) d e x.val)

/-- The actual compactified-base projection is fixed by the small-piece circle. -/
@[simp] theorem smallCircleFlow_projectionToBase (j : Kind) (d : Circle)
    (x : SpecialEllipticPiece j) :
    specialEllipticPieceProjectionToBase j (smallCircleFlow j d x) =
      specialEllipticPieceProjectionToBase j x := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective d
  rw [smallCircleFlow_real]
  exact VerticalAction.Elliptic.specialFlow_projectionToBase j (t : ℂ) x

theorem smallCircleFlow_joint_continuous (j : Kind) :
    Continuous (fun p : Circle × SpecialEllipticPiece j => smallCircleFlow j p.1 p.2) := by
  have hv : Continuous (fun x : SpecialEllipticPiece j => (x.val : SpecialFullFilling j)) :=
    continuous_subtype_val
  have h : Continuous (fun p : Circle × SpecialEllipticPiece j =>
      fullCircleFlow (specialLocalData j) p.1 (p.2.val : SpecialFullFilling j)) :=
    (fullCircleFlow_joint_continuous (specialLocalData j)).comp
      (continuous_fst.prodMk (hv.comp continuous_snd))
  exact h.subtype_mk _

@[instance_reducible] def smallCircleAction (j : Kind) :
    AddAction Circle (SpecialEllipticPiece j) where
  vadd d x := smallCircleFlow j d x
  zero_vadd := smallCircleFlow_zero j
  add_vadd := smallCircleFlow_add j

theorem smallCircleAction_continuous (j : Kind) :
    letI := smallCircleAction j
    ContinuousVAdd Circle (SpecialEllipticPiece j) := by
  let := smallCircleAction j
  exact ⟨smallCircleFlow_joint_continuous j⟩

/-- The actual orbit relation on the original small gluing piece. -/
def smallOrbitSetoid (j : Kind) : Setoid (SpecialEllipticPiece j) :=
  letI := smallCircleAction j
  AddAction.orbitRel Circle (SpecialEllipticPiece j)

abbrev SmallOrbit (j : Kind) := Quotient (smallOrbitSetoid j)

def smallOrbitProjection (j : Kind) : SpecialEllipticPiece j → SmallOrbit j :=
  Quotient.mk (smallOrbitSetoid j)

theorem smallOrbitProjection_surjective (j : Kind) :
    Function.Surjective (smallOrbitProjection j) := Quotient.mk_surjective

theorem smallOrbitProjection_isOpenQuotientMap (j : Kind) :
    IsOpenQuotientMap (smallOrbitProjection j) := by
  let := smallCircleAction j
  let := smallCircleAction_continuous j
  exact AddAction.isOpenQuotientMap_quotientMk

theorem smallOrbitProjection_eq_iff (j : Kind) (x y : SpecialEllipticPiece j) :
    smallOrbitProjection j x = smallOrbitProjection j y ↔
      ∃ d : Circle, smallCircleFlow j d y = x := Quotient.eq''

@[simp] theorem smallOrbitProjection_circleFlow (j : Kind) (d : Circle)
    (x : SpecialEllipticPiece j) :
    smallOrbitProjection j (smallCircleFlow j d x) = smallOrbitProjection j x :=
  (smallOrbitProjection_eq_iff j _ _).mpr ⟨d, rfl⟩

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit
