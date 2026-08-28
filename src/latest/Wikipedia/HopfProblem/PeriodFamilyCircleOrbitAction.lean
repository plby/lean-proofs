import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriodBasic
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# The actual delta-circle action on a fixed period torus

The fourth original period column is `![0, 1]`.  Its real translations
therefore descend to an action of the unit-period additive circle on the
original complex period quotient.  All formulas below retain that quotient;
the four circle coordinates are used only to describe its existing topology.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

open Elliptic PeriodTorusHigherHomology

local notation "Circle" => AddCircle (1 : ℝ)
open SpecialPeriods.Threefold.VerticalAction.Period (vector)

theorem torusCoordinates_add (p : PeriodDomain) (x y : p.Torus) :
    periodTorusCircleHomeomorph p (x + y) =
      periodTorusCircleHomeomorph p x + periodTorusCircleHomeomorph p y := by
  obtain ⟨u, rfl⟩ := flatProjection_surjective p x
  obtain ⟨v, rfl⟩ := flatProjection_surjective p y
  rw [← flatProjection_add, periodTorusCircleHomeomorph_flatProjection,
    periodTorusCircleHomeomorph_flatProjection, periodTorusCircleHomeomorph_flatProjection,
    map_add]

/-- The original fourth period column, with an arbitrary real coefficient. -/
theorem periodEquiv_real_delta (p : PeriodDomain) (t : ℝ) :
    periodEquiv p (Pi.single (3 : Fin 4) t) = vector (t : ℂ) := by
  rw [periodEquiv_matrix]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      vector]

/-- The delta circle as points of the original complex period torus. -/
def deltaCirclePoint (p : PeriodDomain) (t : Circle) : p.Torus :=
  (periodTorusCircleHomeomorph p).symm (Pi.single 3 t)

@[simp] theorem deltaCirclePoint_coe (p : PeriodDomain) (t : ℝ) :
    deltaCirclePoint p (t : Circle) =
      p.lattice.mkQ (vector (t : ℂ)) := by
  apply (periodTorusCircleHomeomorph p).injective
  rw [deltaCirclePoint, Homeomorph.apply_symm_apply]
  rw [← periodEquiv_real_delta]
  change Pi.single 3 (t : Circle) =
    periodTorusCircleHomeomorph p (flatProjection p (Pi.single 3 t))
  rw [periodTorusCircleHomeomorph_flatProjection]
  ext i
  fin_cases i <;> simp [coordinateProjection]

@[simp] theorem deltaCirclePoint_coordinates (p : PeriodDomain) (t : Circle) :
    periodTorusCircleHomeomorph p (deltaCirclePoint p t) = Pi.single 3 t :=
  (periodTorusCircleHomeomorph p).apply_symm_apply _

theorem deltaCirclePoint_continuous (p : PeriodDomain) : Continuous (deltaCirclePoint p) := by
  apply (periodTorusCircleHomeomorph p).symm.continuous.comp
  apply continuous_pi
  intro i
  by_cases hi : i = 3
  · subst i
    change Continuous (fun t : Circle => t)
    exact continuous_id
  · simpa only [Pi.single_apply, if_neg hi] using
      (continuous_const : Continuous (fun _ : Circle => (0 : Circle)))

@[simp] theorem deltaCirclePoint_zero (p : PeriodDomain) : deltaCirclePoint p 0 = 0 := by
  apply (periodTorusCircleHomeomorph p).injective
  simp

theorem deltaCirclePoint_add (p : PeriodDomain) (s t : Circle) :
    deltaCirclePoint p (s + t) = deltaCirclePoint p s + deltaCirclePoint p t := by
  apply (periodTorusCircleHomeomorph p).injective
  rw [torusCoordinates_add]
  simp only [deltaCirclePoint_coordinates]
  ext i
  fin_cases i <;> simp

/-- Translation by the actual delta circle, not a replacement torus action. -/
def circleFlow (p : PeriodDomain) (t : Circle) (x : p.Torus) : p.Torus :=
  x + deltaCirclePoint p t

@[simp] theorem circleFlow_coe (p : PeriodDomain) (t : ℝ) (x : p.Torus) :
    circleFlow p (t : Circle) x = x + p.lattice.mkQ (vector (t : ℂ)) := by
  rw [circleFlow, deltaCirclePoint_coe]

@[simp] theorem circleFlow_coe_mkQ (p : PeriodDomain) (t : ℝ) (z : ComplexPlane₂) :
    circleFlow p (t : Circle) (p.lattice.mkQ z) =
      p.lattice.mkQ (z + vector (t : ℂ)) := by
  rw [circleFlow_coe, map_add]

theorem circleFlow_coordinates (p : PeriodDomain) (t : Circle) (x : p.Torus) :
    periodTorusCircleHomeomorph p (circleFlow p t x) =
      periodTorusCircleHomeomorph p x + Pi.single 3 t := by
  rw [circleFlow, torusCoordinates_add, deltaCirclePoint_coordinates]

@[simp] theorem circleFlow_zero (p : PeriodDomain) (x : p.Torus) : circleFlow p 0 x = x := by
  simp [circleFlow]

theorem circleFlow_add (p : PeriodDomain) (s t : Circle) (x : p.Torus) :
    circleFlow p (s + t) x = circleFlow p s (circleFlow p t x) := by
  simp only [circleFlow, deltaCirclePoint_add]
  abel

theorem circleFlow_continuous (p : PeriodDomain) :
    Continuous (fun x : Circle × p.Torus => circleFlow p x.1 x.2) :=
  continuous_snd.add ((deltaCirclePoint_continuous p).comp continuous_fst)

/-- No nonzero circle parameter fixes a point of a regular period torus. -/
theorem circleFlow_eq_self_iff (p : PeriodDomain) (t : Circle) (x : p.Torus) :
    circleFlow p t x = x ↔ t = 0 := by
  constructor
  · intro h
    have hc := congrArg (fun y => periodTorusCircleHomeomorph p y 3) h
    rw [circleFlow_coordinates] at hc
    simpa using hc
  · rintro rfl
    exact circleFlow_zero p x

/-- This fixed-fibre action is the restriction of the original varying-period
flow, on the original fibre inclusion and complex covering representatives. -/
theorem fibreInclusion_circleFlow_real
    {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)
    (b : B) (t : ℝ) (x : (P.point b).Torus) :
    P.fibreInclusion b (circleFlow (P.point b) (t : Circle) x) =
      SpecialPeriods.Threefold.VerticalAction.Period.flow P (t : ℂ) (P.fibreInclusion b x) := by
  obtain ⟨z, rfl⟩ := (P.point b).lattice.mkQ_surjective x
  rw [circleFlow_coe_mkQ, P.fibreInclusion_mkQ, P.fibreInclusion_mkQ,
    SpecialPeriods.Threefold.VerticalAction.Period.flow_quotientMap]
  rfl

/-- The period-one additive action induced by the original vertical flow. -/
@[instance_reducible] def circleAction (p : PeriodDomain) : AddAction Circle p.Torus where
  vadd := circleFlow p
  zero_vadd := circleFlow_zero p
  add_vadd := circleFlow_add p

theorem circleAction_continuous (p : PeriodDomain) :
    letI := circleAction p
    ContinuousVAdd Circle p.Torus := by
  let := circleAction p
  exact ⟨circleFlow_continuous p⟩

/-- The literal orbit relation of that action on the original period quotient. -/
def circleOrbitSetoid (p : PeriodDomain) : Setoid p.Torus :=
  letI := circleAction p
  AddAction.orbitRel Circle p.Torus

abbrev CircleOrbit (p : PeriodDomain) := Quotient (circleOrbitSetoid p)

def circleOrbitProjection (p : PeriodDomain) : p.Torus → CircleOrbit p :=
  Quotient.mk (circleOrbitSetoid p)

theorem circleOrbitProjection_isOpenQuotientMap (p : PeriodDomain) :
    IsOpenQuotientMap (circleOrbitProjection p) := by
  let := circleAction p
  let := circleAction_continuous p
  exact AddAction.isOpenQuotientMap_quotientMk

theorem circleOrbitProjection_eq_iff (p : PeriodDomain) (x y : p.Torus) :
    circleOrbitProjection p x = circleOrbitProjection p y ↔
      ∃ t : Circle, circleFlow p t y = x :=
  Quotient.eq

@[simp] theorem circleOrbitProjection_circleFlow (p : PeriodDomain) (t : Circle)
    (x : p.Torus) :
    circleOrbitProjection p (circleFlow p t x) = circleOrbitProjection p x :=
  Quotient.sound ⟨t, rfl⟩

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
