import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLoopSquaresCircle
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansHomotopy
import Mathlib.Topology.CompactOpen

/-!
# Jointly continuous periodic extension of an actual loop square

The matching vertical edges allow each row of the given square to descend
through the genuine endpoint quotient. Since the homotopy parameter is
locally compact, the quotient-map product theorem proves joint continuity.
The actual interval-quotient circle homeomorphism and the real projection
then give a periodic homotopy whose unit-square restriction is exactly the
original square, with no extra homotopy or continuity assumption.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryLoopSquares

open SpecialPeriods.EllipticAttachingMeridians

variable {X : Type*} [TopologicalSpace X] {a b : X} {p : Path a a} {q : Path b b}

/-- A periodic real-time map is determined by its actual values on the closed unit interval. -/
theorem loopPeriodic_unique (f : ℝ → X) (hf : Function.Periodic f 1)
    (hp : ∀ t : unitInterval, f (t : ℝ) = p t) : f = loopPeriodic p := by
  have h : hf.lift = (loopOnCircle p : LoopCircle → X) := by
    funext z
    obtain ⟨t, rfl⟩ := loopUnitCircle_surjective z
    rw [Function.Periodic.lift_coe, loopOnCircle_unit]
    exact hp t
  funext t
  exact congrFun h (t : LoopCircle)

/-- Descend the actual square in its loop parameter by identifying only the two endpoints. -/
def loopSquareQuotient (S : LoopSquare p q) (z : unitInterval × LoopQuotient) : X :=
  Quot.lift
    (fun u : LoopInterval => S.map
      (z.1, ⟨u.val,
        by simpa only [LoopInterval, unitInterval, zero_add] using u.property⟩))
    (by
      intro u v h
      cases h
      calc
        _ = S.map (z.1, 0) := congrArg (fun t => S.map (z.1, t)) (Subtype.ext rfl)
        _ = S.map (z.1, 1) := S.closed z.1
        _ = _ := congrArg (fun t => S.map (z.1, t))
          (Subtype.ext (zero_add (1 : ℝ)).symm))
    z.2

@[simp] theorem loopSquareQuotient_unit (S : LoopSquare p q) (s t : unitInterval) :
    loopSquareQuotient S (s, loopQuotientMap t) = S.map (s, t) := rfl

/-- Compactness of the parameter interval makes this a jointly continuous quotient lift. -/
theorem continuous_loopSquareQuotient (S : LoopSquare p q) :
    Continuous (loopSquareQuotient S) := by
  apply loopQuotientMap_isQuotientMap.continuous_lift_prod_right
  change Continuous (fun z : unitInterval × unitInterval => S.map (z.1, z.2))
  exact S.map.continuous

/-- The actual square as a continuous map on the endpoint-quotient cylinder. -/
def quotientSquare (S : LoopSquare p q) : C(unitInterval × LoopQuotient, X) :=
  ⟨loopSquareQuotient S, continuous_loopSquareQuotient S⟩

/-- The same actual homotopy with the loop parameter on the additive circle. -/
def circleSquare (S : LoopSquare p q) : C(unitInterval × LoopCircle, X) :=
  (quotientSquare S).comp
    ⟨fun z => (z.1, AddCircle.homeoIccQuot (1 : ℝ) 0 z.2),
      continuous_fst.prodMk
        ((AddCircle.homeoIccQuot (1 : ℝ) 0).continuous.comp continuous_snd)⟩

/-- On every unit-interval representative the circle homotopy is exactly the original square. -/
@[simp] theorem circleSquare_unit (S : LoopSquare p q) (s t : unitInterval) :
    circleSquare S (s, ((t : ℝ) : LoopCircle)) = S.map (s, t) := by
  change loopSquareQuotient S
    (s, AddCircle.homeoIccQuot (1 : ℝ) 0 ((t : ℝ) : LoopCircle)) = _
  rw [loopCircleQuotient_unit, loopSquareQuotient_unit]

@[simp] theorem circleSquare_initial (S : LoopSquare p q) (z : LoopCircle) :
    circleSquare S (0, z) = loopOnCircle p z := by
  obtain ⟨t, rfl⟩ := loopUnitCircle_surjective z
  rw [circleSquare_unit, loopOnCircle_unit, S.initial]

@[simp] theorem circleSquare_final (S : LoopSquare p q) (z : LoopCircle) :
    circleSquare S (1, z) = loopOnCircle q z := by
  obtain ⟨t, rfl⟩ := loopUnitCircle_surjective z
  rw [circleSquare_unit, loopOnCircle_unit, S.final]

/-- The actual continuous homotopy between the two descended circle loops. -/
def circleHomotopy (S : LoopSquare p q) : (loopOnCircle p).Homotopy (loopOnCircle q) where
  toFun := circleSquare S
  continuous_toFun := (circleSquare S).continuous
  map_zero_left := circleSquare_initial S
  map_one_left := circleSquare_final S

/-- Pull back the circle homotopy to real time. -/
def periodicSquare (S : LoopSquare p q) : C(unitInterval × ℝ, X) :=
  (circleSquare S).comp
    ⟨fun z => (z.1, (z.2 : LoopCircle)),
      continuous_fst.prodMk
        ((AddCircle.continuous_mk' (1 : ℝ)).comp continuous_snd)⟩

@[simp] theorem periodicSquare_apply (S : LoopSquare p q) (s : unitInterval) (t : ℝ) :
    periodicSquare S (s, t) = circleSquare S (s, (t : LoopCircle)) := rfl

/-- The full unit-square restriction is literally the square supplied by the geometry. -/
@[simp] theorem periodicSquare_unit (S : LoopSquare p q) (s t : unitInterval) :
    periodicSquare S (s, (t : ℝ)) = S.map (s, t) :=
  circleSquare_unit S s t

/-- The initial endpoint is the actual periodic extension of the given initial loop. -/
@[simp] theorem periodicSquare_initial (S : LoopSquare p q) (t : ℝ) :
    periodicSquare S (0, t) = loopPeriodic p t :=
  circleSquare_initial S (t : LoopCircle)

/-- The final endpoint is the actual periodic extension of the given final loop. -/
@[simp] theorem periodicSquare_final (S : LoopSquare p q) (t : ℝ) :
    periodicSquare S (1, t) = loopPeriodic q t :=
  circleSquare_final S (t : LoopCircle)

/-- Integer periodicity holds at every homotopy parameter. -/
theorem periodicSquare_add_int (S : LoopSquare p q) (s : unitInterval) (t : ℝ) (k : ℤ) :
    periodicSquare S (s, t + (k : ℝ)) = periodicSquare S (s, t) := by
  change circleSquare S (s, ((t + (k : ℝ) : ℝ) : LoopCircle)) = _
  rw [loopCircle_add_int]
  rfl

/-- Period one is a property of the actual real-time map in each row. -/
theorem periodicSquare_periodic (S : LoopSquare p q) (s : unitInterval) :
    Function.Periodic (fun t : ℝ => periodicSquare S (s, t)) 1 := by
  intro t
  simpa only [Int.cast_one] using periodicSquare_add_int S s t 1

/-- Time zero retains exactly the original basepoint trajectory. -/
@[simp] theorem periodicSquare_tail (S : LoopSquare p q) (s : unitInterval) :
    periodicSquare S (s, 0) = S.tail s :=
  periodicSquare_unit S s 0

/-- The same actual trajectory occurs at every integer real time. -/
theorem periodicSquare_int (S : LoopSquare p q) (s : unitInterval) (k : ℤ) :
    periodicSquare S (s, (k : ℝ)) = S.tail s := by
  have h := periodicSquare_add_int S s 0 k
  simpa only [zero_add, periodicSquare_tail] using h

/-- The jointly continuous periodic homotopy between the actual real-time loop extensions. -/
def periodicHomotopy (S : LoopSquare p q) : (loopPeriodic p).Homotopy (loopPeriodic q) where
  toFun := periodicSquare S
  continuous_toFun := (periodicSquare S).continuous
  map_zero_left := periodicSquare_initial S
  map_one_left := periodicSquare_final S

@[simp] theorem periodicHomotopy_apply (S : LoopSquare p q) (s : unitInterval) (t : ℝ) :
    periodicHomotopy S (s, t) = periodicSquare S (s, t) := rfl

@[simp] theorem periodicHomotopy_unit (S : LoopSquare p q) (s t : unitInterval) :
    periodicHomotopy S (s, (t : ℝ)) = S.map (s, t) :=
  periodicSquare_unit S s t

theorem periodicHomotopy_add_int (S : LoopSquare p q) (s : unitInterval) (t : ℝ) (k : ℤ) :
    periodicHomotopy S (s, t + (k : ℝ)) = periodicHomotopy S (s, t) :=
  periodicSquare_add_int S s t k

/-- Any rowwise-periodic extension of this literal square equals the constructed one. -/
theorem periodicSquare_unique (S : LoopSquare p q) (F : unitInterval × ℝ → X)
    (hF : ∀ s : unitInterval, Function.Periodic (fun t : ℝ => F (s, t)) 1)
    (hunit : ∀ s t : unitInterval, F (s, (t : ℝ)) = S.map (s, t)) :
    F = periodicSquare S := by
  funext z
  have h : (hF z.1).lift = (fun c : LoopCircle => circleSquare S (z.1, c)) := by
    funext c
    obtain ⟨t, rfl⟩ := loopUnitCircle_surjective c
    rw [Function.Periodic.lift_coe, circleSquare_unit]
    exact hunit z.1 t
  exact congrFun h (z.2 : LoopCircle)

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryLoopSquares
