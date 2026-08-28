import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Path

/-!
# Closed paths on the actual quotient circle

A closed path descends through the quotient of the unit interval that
identifies its endpoints.  The actual `AddCircle.homeoIccQuot` identifies
that quotient with the unit-period additive circle.  Pullback along the
real quotient map gives a continuous periodic extension, with literal
unit-interval values and integer-periodicity identities.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryLoopSquares

/-- The actual unit-period additive circle. -/
abbrev LoopCircle := AddCircle (1 : ℝ)

/-- The closed interval appearing literally in the endpoint-identification relation. -/
abbrev LoopInterval := Set.Icc (0 : ℝ) (0 + 1)

/-- The actual quotient of the closed interval by its two endpoints. -/
abbrev LoopQuotient := Quot (AddCircle.EndpointIdent (1 : ℝ) 0)

/-- The identity on real coordinates identifies the two interval presentations. -/
def loopIntervalHomeomorph : unitInterval ≃ₜ LoopInterval where
  toFun t := ⟨t.val, by simpa only [LoopInterval, unitInterval, zero_add] using t.property⟩
  invFun t := ⟨t.val, by simpa only [LoopInterval, unitInterval, zero_add] using t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk
    (fun t => by simpa only [LoopInterval, unitInterval, zero_add] using t.property)
  continuous_invFun := continuous_subtype_val.subtype_mk
    (fun t => by simpa only [LoopInterval, unitInterval, zero_add] using t.property)

@[simp] theorem loopIntervalHomeomorph_coe (t : unitInterval) :
    (loopIntervalHomeomorph t : ℝ) = (t : ℝ) := rfl

@[simp] theorem loopIntervalHomeomorph_symm_coe (t : LoopInterval) :
    ((loopIntervalHomeomorph.symm t : unitInterval) : ℝ) = (t : ℝ) := rfl

/-- The canonical interval quotient map is literally the quotient constructor. -/
def loopQuotientMap (t : unitInterval) : LoopQuotient :=
  Quot.mk _ ⟨t.val, by simpa only [LoopInterval, unitInterval, zero_add] using t.property⟩

theorem loopQuotientMap_isQuotientMap : IsQuotientMap loopQuotientMap :=
  isQuotientMap_quot_mk.comp loopIntervalHomeomorph.isQuotientMap

/-- The circle-to-interval-quotient homeomorphism sends an interval point to its literal class. -/
theorem loopCircleQuotient_unit (t : unitInterval) :
    AddCircle.homeoIccQuot (1 : ℝ) 0 ((t : ℝ) : LoopCircle) = loopQuotientMap t := by
  apply (AddCircle.homeoIccQuot (1 : ℝ) 0).symm.injective
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- Every point of the actual circle has a representative in the closed unit interval. -/
theorem loopUnitCircle_surjective :
    Function.Surjective (fun t : unitInterval => ((t : ℝ) : LoopCircle)) := by
  intro z
  obtain ⟨t, ht⟩ := loopQuotientMap_isQuotientMap.surjective
    (AddCircle.homeoIccQuot (1 : ℝ) 0 z)
  refine ⟨t, (AddCircle.homeoIccQuot (1 : ℝ) 0).injective ?_⟩
  rw [loopCircleQuotient_unit, ht]

/-- Every integral real number is zero in the unit-period additive circle. -/
@[simp] theorem loopCircle_int (k : ℤ) : ((k : ℝ) : LoopCircle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨k, by simp [zsmul_eq_mul]⟩

/-- Adding an integer does not change the actual quotient point. -/
theorem loopCircle_add_int (t : ℝ) (k : ℤ) :
    ((t + (k : ℝ) : ℝ) : LoopCircle) = (t : LoopCircle) := by
  rw [AddCircle.coe_add, loopCircle_int, add_zero]

theorem loopCircle_add_one (t : ℝ) :
    ((t + 1 : ℝ) : LoopCircle) = (t : LoopCircle) :=
  AddCircle.coe_add_period (1 : ℝ) t

variable {X : Type*} [TopologicalSpace X] {a : X}

/-- A closed path descends continuously to the actual endpoint quotient. -/
def loopOnQuotient (p : Path a a) : C(LoopQuotient, X) where
  toFun := Quot.lift
    (fun u : LoopInterval => p
      ⟨u.val, by simpa only [LoopInterval, unitInterval, zero_add] using u.property⟩)
    (by
      intro u v h
      cases h
      calc
        _ = p 0 := congrArg p (Subtype.ext rfl)
        _ = p 1 := p.source.trans p.target.symm
        _ = _ := congrArg p (Subtype.ext (zero_add (1 : ℝ)).symm))
  continuous_toFun := continuous_quot_lift _
    (p.continuous.comp loopIntervalHomeomorph.symm.continuous)

@[simp] theorem loopOnQuotient_unit (p : Path a a) (t : unitInterval) :
    loopOnQuotient p (loopQuotientMap t) = p t := rfl

/-- The actual continuous map of the circle induced by the closed path. -/
def loopOnCircle (p : Path a a) : C(LoopCircle, X) :=
  (loopOnQuotient p).comp (AddCircle.homeoIccQuot (1 : ℝ) 0 : C(LoopCircle, LoopQuotient))

@[simp] theorem loopOnCircle_unit (p : Path a a) (t : unitInterval) :
    loopOnCircle p ((t : ℝ) : LoopCircle) = p t := by
  change loopOnQuotient p (AddCircle.homeoIccQuot (1 : ℝ) 0 ((t : ℝ) : LoopCircle)) = p t
  rw [loopCircleQuotient_unit, loopOnQuotient_unit]

/-- Pull the circle map back to the real line to obtain its continuous periodic extension. -/
def loopPeriodic (p : Path a a) : C(ℝ, X) :=
  (loopOnCircle p).comp ⟨fun t : ℝ => (t : LoopCircle), AddCircle.continuous_mk' (1 : ℝ)⟩

@[simp] theorem loopPeriodic_apply (p : Path a a) (t : ℝ) :
    loopPeriodic p t = loopOnCircle p (t : LoopCircle) := rfl

/-- The periodic extension retains the literal path on the whole closed unit interval. -/
@[simp] theorem loopPeriodic_unit (p : Path a a) (t : unitInterval) :
    loopPeriodic p (t : ℝ) = p t := loopOnCircle_unit p t

theorem loopPeriodic_add_one (p : Path a a) (t : ℝ) :
    loopPeriodic p (t + 1) = loopPeriodic p t := by
  simp only [loopPeriodic_apply, loopCircle_add_one]

theorem loopPeriodic_add_int (p : Path a a) (t : ℝ) (k : ℤ) :
    loopPeriodic p (t + (k : ℝ)) = loopPeriodic p t := by
  simp only [loopPeriodic_apply, loopCircle_add_int]

@[simp] theorem loopPeriodic_zero (p : Path a a) : loopPeriodic p 0 = a :=
  (loopPeriodic_unit p 0).trans p.source

@[simp] theorem loopPeriodic_one (p : Path a a) : loopPeriodic p 1 = a :=
  (loopPeriodic_unit p 1).trans p.target

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryLoopSquares
