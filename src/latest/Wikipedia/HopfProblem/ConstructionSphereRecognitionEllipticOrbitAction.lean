import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticFullProduct
import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCircle

/-!
# The original delta-circle action on the full elliptic cap

The circle acts on the unchanged covering family by adding the fourth real
period column. Its descent is through the original finite affine action.
Real circle representatives agree exactly with the original complex vertical
flow; in particular neither a sign nor a finite covering degree is inserted.
The orbit space below has its actual quotient topology.
-/

noncomputable section

open Topology

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit

open Elliptic SpecialPeriods
open SpecialPeriods.Threefold.Homology.DeltaSweep
open SpecialPeriods.Threefold.VerticalAction

local notation "Circle" => AddCircle (1 : ℝ)

variable {j : Kind} (D : Equivariant.Data j)

/-- Literal fourth-column translation on the original covering family. -/
def upstairsCircleFlow (d : Circle) (x : D.TotalSpace) : D.TotalSpace :=
  (x.1, x.2 + deltaCircle d)

@[simp] theorem upstairsCircleFlow_apply (d : Circle) (s : Disc) (x : RealTorus₄) :
    upstairsCircleFlow D d (s, x) = (s, x + deltaCircle d) := rfl

/-- The actual varying period basis identifies real vertical time with this
literal translation, including over the central point. -/
theorem upstairsCircleFlow_real (t : ℝ) (x : D.TotalSpace) :
    upstairsCircleFlow D (t : Circle) x = Period.flow D.periods (t : ℂ) x := by
  change (x.1, x.2 + deltaCircle (t : Circle)) =
    (x.1, x.2 + standardLattice.mkQ
      ((D.periods.periodEquiv x.1).symm (Period.vector (t : ℂ))))
  rw [EllipticGamma.inverse_vector_real, deltaCircle_real_apply]

/-- The full original affine deck action commutes with the delta circle. -/
theorem upstairsCircleFlow_action (d : Circle) (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action j.twist (mainTwist_admissible j).1
    upstairsCircleFlow D d (g • x) = g • upstairsCircleFlow D d x := by
  let := D.action j.twist (mainTwist_admissible j).1
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective d
  rw [upstairsCircleFlow_real, upstairsCircleFlow_real]
  exact SpecialPeriods.Threefold.VerticalAction.Elliptic.periodFlow_action D
    j.twist (mainTwist_admissible j).1 (t : ℂ) g x

/-- Descent through the original finite quotient, not a new model of the cap. -/
def fullCircleFlow (d : Circle) :
    D.Space j.twist (mainTwist_admissible j) →
      D.Space j.twist (mainTwist_admissible j) := by
  let := D.action j.twist (mainTwist_admissible j).1
  exact FiniteQuotient.descend
    (fun x => D.quotient j.twist (mainTwist_admissible j) (upstairsCircleFlow D d x))
    (by
      intro g x
      rw [upstairsCircleFlow_action, D.quotient_smul])

@[simp] theorem fullCircleFlow_quotient (d : Circle) (x : D.TotalSpace) :
    fullCircleFlow D d (D.quotient j.twist (mainTwist_admissible j) x) =
      D.quotient j.twist (mainTwist_admissible j) (upstairsCircleFlow D d x) := rfl

/-- The real-parameter formula uses precisely the already constructed flow. -/
theorem fullCircleFlow_real (t : ℝ) (x : D.Space j.twist (mainTwist_admissible j)) :
    fullCircleFlow D (t : Circle) x =
      SpecialPeriods.Threefold.VerticalAction.Elliptic.flow D j.twist
        (mainTwist_admissible j) (t : ℂ) x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) x
  rw [fullCircleFlow_quotient, upstairsCircleFlow_real,
    SpecialPeriods.Threefold.VerticalAction.Elliptic.flow_quotient]

@[simp] theorem fullCircleFlow_zero (x : D.Space j.twist (mainTwist_admissible j)) :
    fullCircleFlow D 0 x = x := by
  obtain ⟨⟨s, y⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) x
  simp only [fullCircleFlow_quotient, upstairsCircleFlow_apply, deltaCircle_zero, add_zero]

theorem fullCircleFlow_add (d e : Circle)
    (x : D.Space j.twist (mainTwist_admissible j)) :
    fullCircleFlow D (d + e) x = fullCircleFlow D d (fullCircleFlow D e x) := by
  obtain ⟨⟨s, y⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) x
  simp only [fullCircleFlow_quotient, upstairsCircleFlow_apply, deltaCircle_add]
  congr 1
  apply congrArg (fun z : RealTorus₄ => (s, z))
  abel

/-- The original base parameter is fixed, not merely its absolute value. -/
@[simp] theorem fullCircleFlow_projection (d : Circle)
    (x : D.Space j.twist (mainTwist_admissible j)) :
    D.projection j.twist (mainTwist_admissible j) (fullCircleFlow D d x) =
      D.projection j.twist (mainTwist_admissible j) x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) x
  rw [fullCircleFlow_quotient, D.projection_quotient, D.projection_quotient]
  rfl

/-- Joint continuity is checked through the actual open finite quotient. -/
theorem fullCircleFlow_joint_continuous :
    Continuous (fun p : Circle × D.Space j.twist (mainTwist_admissible j) =>
      fullCircleFlow D p.1 p.2) := by
  apply (IsOpenQuotientMap.id.prodMap
    (D.quotient_isOpenQuotientMap j.twist (mainTwist_admissible j))).continuous_comp_iff.mp
  change Continuous (fun p : Circle × D.TotalSpace =>
    D.quotient j.twist (mainTwist_admissible j)
      (p.2.1, p.2.2 + deltaCircle p.1))
  exact (D.quotient_continuous j.twist (mainTwist_admissible j)).comp
    ((continuous_fst.comp continuous_snd).prodMk
      ((continuous_snd.comp continuous_snd).add (deltaCircle.continuous.comp continuous_fst)))

@[instance_reducible] def fullCircleAction :
    AddAction Circle (D.Space j.twist (mainTwist_admissible j)) where
  vadd d x := fullCircleFlow D d x
  zero_vadd := fullCircleFlow_zero D
  add_vadd := fullCircleFlow_add D

theorem fullCircleAction_continuous :
    letI := fullCircleAction D
    ContinuousVAdd Circle (D.Space j.twist (mainTwist_admissible j)) := by
  let := fullCircleAction D
  exact ⟨fullCircleFlow_joint_continuous D⟩

/-- The actual orbit relation of the original vertical circle. -/
def fullOrbitSetoid : Setoid (D.Space j.twist (mainTwist_admissible j)) :=
  letI := fullCircleAction D
  AddAction.orbitRel Circle (D.Space j.twist (mainTwist_admissible j))

/-- This is the genuine circle orbit quotient, with its quotient topology. -/
abbrev FullOrbit := Quotient (fullOrbitSetoid D)

def fullOrbitProjection : D.Space j.twist (mainTwist_admissible j) → FullOrbit D :=
  Quotient.mk (fullOrbitSetoid D)

theorem fullOrbitProjection_surjective : Function.Surjective (fullOrbitProjection D) :=
  Quotient.mk_surjective

theorem fullOrbitProjection_isOpenQuotientMap :
    IsOpenQuotientMap (fullOrbitProjection D) := by
  let := fullCircleAction D
  let := fullCircleAction_continuous D
  exact AddAction.isOpenQuotientMap_quotientMk

/-- Equality in the new quotient is exactly one original circle orbit. -/
theorem fullOrbitProjection_eq_iff (x y : D.Space j.twist (mainTwist_admissible j)) :
    fullOrbitProjection D x = fullOrbitProjection D y ↔
      ∃ d : Circle, fullCircleFlow D d y = x := Quotient.eq''

@[simp] theorem fullOrbitProjection_circleFlow (d : Circle)
    (x : D.Space j.twist (mainTwist_admissible j)) :
    fullOrbitProjection D (fullCircleFlow D d x) = fullOrbitProjection D x :=
  (fullOrbitProjection_eq_iff D _ _).mpr ⟨d, rfl⟩

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbit
