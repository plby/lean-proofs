import ErdosProblems.Erdos1002.PrefixFreezingAggregate
import ErdosProblems.Erdos1002.GaussFactorialTupleReplacement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Signed approximation windows and parity

The marked continued-fraction value coordinate has sign `(-1)^n`.  This
file makes the parity reduction used in the marked point-process proof
literal: at even depths a signed window is the usual positive approximation
window, while at odd depths its endpoints are reflected and reversed.  It
also identifies finite products of marked value-window indicators with
finite intersections of these signed approximation windows, up to the
null complement of the unit state space.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1002

noncomputable section

local instance gaussSignedApproximationPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- The signed, scaled exact approximation coordinate at depth `n`. -/
def gaussSignedScaledApproximationCoordinate
    (scale : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * gaussScaledApproximationCoordinate scale n x

theorem measurable_gaussSignedScaledApproximationCoordinate
    (scale : ℝ) (n : ℕ) :
    Measurable (gaussSignedScaledApproximationCoordinate scale n) := by
  exact measurable_const.mul
    (measurable_gaussScaledApproximationCoordinate scale n)

/-- Exact signed window, with the Gauss state-space condition retained. -/
def gaussSignedApproximationWindow
    (scale : ℝ) (n : ℕ) (lower upper : ℝ) : Set ℝ :=
  Ioc (0 : ℝ) 1 ∩
    gaussSignedScaledApproximationCoordinate scale n ⁻¹' Icc lower upper

theorem measurableSet_gaussSignedApproximationWindow
    (scale : ℝ) (n : ℕ) (lower upper : ℝ) :
    MeasurableSet
      (gaussSignedApproximationWindow scale n lower upper) := by
  exact measurableSet_Ioc.inter
    (measurableSet_Icc.preimage
      (measurable_gaussSignedScaledApproximationCoordinate scale n))

/-- Even depths carry the positive signed coordinate. -/
theorem gaussSignedApproximationWindow_eq_even
    {n : ℕ} (hn : Even n) (scale lower upper : ℝ) :
    gaussSignedApproximationWindow scale n lower upper =
      gaussApproximationWindow scale n lower upper := by
  ext x
  change
    (x ∈ Ioc (0 : ℝ) 1 ∧
      (-1 : ℝ) ^ n * gaussScaledApproximationCoordinate scale n x ∈
        Icc lower upper) ↔
      (x ∈ Ioc (0 : ℝ) 1 ∧
        gaussScaledApproximationCoordinate scale n x ∈ Icc lower upper)
  rw [hn.neg_one_pow]
  simp only [one_mul]

/-- Odd depths carry the negative coordinate, so a signed interval
`[lower,upper]` becomes the positive interval `[-upper,-lower]`. -/
theorem gaussSignedApproximationWindow_eq_odd
    {n : ℕ} (hn : Odd n) (scale lower upper : ℝ) :
    gaussSignedApproximationWindow scale n lower upper =
      gaussApproximationWindow scale n (-upper) (-lower) := by
  ext x
  change
    (x ∈ Ioc (0 : ℝ) 1 ∧
      (-1 : ℝ) ^ n * gaussScaledApproximationCoordinate scale n x ∈
        Icc lower upper) ↔
      (x ∈ Ioc (0 : ℝ) 1 ∧
        gaussScaledApproximationCoordinate scale n x ∈ Icc (-upper) (-lower))
  rw [hn.neg_one_pow]
  simp only [neg_one_mul, mem_Icc]
  constructor
  · rintro ⟨hx, hlower, hupper⟩
    exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, hlower, hupper⟩
    exact ⟨hx, by linarith, by linarith⟩

/-- Positive-window lower endpoint obtained after removing the parity sign. -/
def gaussParityOrientedLower (n : ℕ) (lower upper : ℝ) : ℝ :=
  if Even n then lower else -upper

/-- Positive-window upper endpoint obtained after removing the parity sign. -/
def gaussParityOrientedUpper (n : ℕ) (lower upper : ℝ) : ℝ :=
  if Even n then upper else -lower

/-- Uniform parity reduction, with no externally prescribed parity case. -/
theorem gaussSignedApproximationWindow_eq_oriented
    (scale : ℝ) (n : ℕ) (lower upper : ℝ) :
    gaussSignedApproximationWindow scale n lower upper =
      gaussApproximationWindow scale n
        (gaussParityOrientedLower n lower upper)
        (gaussParityOrientedUpper n lower upper) := by
  by_cases hn : Even n
  · rw [gaussSignedApproximationWindow_eq_even hn]
    simp only [gaussParityOrientedLower, gaussParityOrientedUpper, if_pos hn]
  · have hnOdd : Odd n := Nat.not_even_iff_odd.mp hn
    rw [gaussSignedApproximationWindow_eq_odd hnOdd]
    simp only [gaussParityOrientedLower, gaussParityOrientedUpper, if_neg hn]

/-- The second coordinate of the literal marked prefix point is exactly
the signed, logarithmically scaled approximation coordinate. -/
theorem gaussPrefixMarkedPoint_value_eq_signedScaledApproximation
    (N n : ℕ) (w : PositiveDigitWord n) (x : ℝ) :
    (gaussPrefixMarkedPoint N n w x).2.1 =
      gaussSignedScaledApproximationCoordinate
        (Real.log (N : ℝ)) n x := by
  unfold gaussPrefixMarkedPoint gaussSignedScaledApproximationCoordinate
    gaussScaledApproximationCoordinate
  ring

/-- Finite intersection of signed approximation windows. -/
def gaussSignedApproximationTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i ↦
    gaussSignedApproximationWindow scale (times i) (lower i) (upper i)

/-- Tuple of ordinary exact approximation windows with coordinate-dependent
endpoints. -/
def gaussHeterogeneousApproximationTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i ↦
    gaussApproximationWindow scale (times i) (lower i) (upper i)

/-- All signed coordinates can be removed simultaneously by orienting each
pair of endpoints according to the parity of its own depth. -/
theorem gaussSignedApproximationTupleEvent_eq_oriented
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    gaussSignedApproximationTupleEvent scale lower upper times =
      gaussHeterogeneousApproximationTupleEvent scale
        (fun i ↦ gaussParityOrientedLower
          (times i) (lower i) (upper i))
        (fun i ↦ gaussParityOrientedUpper
          (times i) (lower i) (upper i)) times := by
  ext x
  simp only [gaussSignedApproximationTupleEvent,
    gaussHeterogeneousApproximationTupleEvent,
    mem_orderedEventIntersection_ofFn_iff]
  constructor <;> intro hall i
  · rw [← gaussSignedApproximationWindow_eq_oriented]
    exact hall i
  · rw [gaussSignedApproximationWindow_eq_oriented]
    exact hall i

theorem measurableSet_gaussSignedApproximationTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    MeasurableSet
      (gaussSignedApproximationTupleEvent scale lower upper times) := by
  apply measurableSet_orderedEventIntersection
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact measurableSet_gaussSignedApproximationWindow _ _ _ _

theorem measurableSet_gaussHeterogeneousApproximationTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    MeasurableSet
      (gaussHeterogeneousApproximationTupleEvent
        scale lower upper times) := by
  apply measurableSet_orderedEventIntersection
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact measurableSet_gaussApproximationWindow _ _ _ _

/-- On the unit state space, the window-product event for the signed
coordinate functions is exactly the signed approximation tuple event. -/
theorem mem_closedWindowTupleEvent_signedApproximation_iff
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    x ∈ closedWindowTupleEvent lower upper
          (fun y i ↦ gaussSignedScaledApproximationCoordinate
            scale (times i) y) ↔
      x ∈ gaussSignedApproximationTupleEvent scale lower upper times := by
  unfold gaussSignedApproximationTupleEvent closedWindowTupleEvent
  rw [mem_orderedEventIntersection_ofFn_iff]
  constructor
  · intro hall i
    exact ⟨hx, Set.mem_iInter.mp hall i⟩
  · intro hall
    apply Set.mem_iInter.mpr
    intro i
    exact (hall i).2

/-- Hence the two literal finite intersections have exactly the same
uniform mass; the only set-theoretic discrepancy is outside the unit
state space, which has zero uniform measure. -/
theorem uniform01Measure_real_closedWindowTupleEvent_signed_eq
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    uniform01Measure.real
        (closedWindowTupleEvent lower upper
          (fun x i ↦ gaussSignedScaledApproximationCoordinate
            scale (times i) x)) =
      uniform01Measure.real
        (gaussSignedApproximationTupleEvent scale lower upper times) := by
  apply measureReal_congr
  filter_upwards [ae_nonterminating_uniform01] with x hx
  apply propext
  exact mem_closedWindowTupleEvent_signedApproximation_iff
    scale lower upper times ⟨hx.1.1, hx.1.2.le⟩

/-- Specialization to the actual second coordinate of selected marked
prefix points. -/
theorem uniform01Measure_real_closedWindowTupleEvent_markedValue_eq_signed
    {r : ℕ} (N : ℕ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    uniform01Measure.real
        (closedWindowTupleEvent lower upper
          (fun x i ↦
            (gaussPrefixMarkedPoint N (times i)
              (selectedGaussPrefixWord (times i) x) x).2.1)) =
      uniform01Measure.real
        (gaussSignedApproximationTupleEvent
          (Real.log (N : ℝ)) lower upper times) := by
  have hcoordinate :
      (fun x i ↦
          (gaussPrefixMarkedPoint N (times i)
            (selectedGaussPrefixWord (times i) x) x).2.1) =
        (fun x i ↦ gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) (times i) x) := by
    funext x i
    exact gaussPrefixMarkedPoint_value_eq_signedScaledApproximation
      N (times i) (selectedGaussPrefixWord (times i) x) x
  rw [hcoordinate]
  exact uniform01Measure_real_closedWindowTupleEvent_signed_eq
    (Real.log (N : ℝ)) lower upper times

/-- Endpoint-strip tuple mass written as one signed approximation tuple. -/
theorem uniform01Measure_real_closedEndpointStrip_markedValue_eq_signed
    {r : ℕ} (N : ℕ) (a b : Fin r → ℝ)
    (times : Fin r → ℕ) (eta : ℝ) (j : Fin r) (center : ℝ) :
    uniform01Measure.real
        (closedEndpointStripWindowTupleEvent a b
          (fun x i ↦
            (gaussPrefixMarkedPoint N (times i)
              (selectedGaussPrefixWord (times i) x) x).2.1)
          eta j center) =
      uniform01Measure.real
        (gaussSignedApproximationTupleEvent
          (Real.log (N : ℝ))
          (fun i ↦ if i = j then center - eta else a i - eta)
          (fun i ↦ if i = j then center + eta else b i + eta)
          times) := by
  unfold closedEndpointStripWindowTupleEvent
  exact uniform01Measure_real_closedWindowTupleEvent_markedValue_eq_signed
    N _ _ times

/-- The full boundary tuple mass is bounded by the two signed exact tuples
corresponding to its lower and upper endpoint strips. -/
theorem uniform01Measure_real_closedBoundaryWindow_markedValue_le_signed
    {r : ℕ} (N : ℕ) (a b : Fin r → ℝ)
    (times : Fin r → ℕ) (eta : ℝ) (j : Fin r) :
    uniform01Measure.real
        (closedBoundaryWindowTupleEvent a b
          (fun x i ↦
            (gaussPrefixMarkedPoint N (times i)
              (selectedGaussPrefixWord (times i) x) x).2.1)
          eta j) ≤
      uniform01Measure.real
          (gaussSignedApproximationTupleEvent
            (Real.log (N : ℝ))
            (fun i ↦ if i = j then a j - eta else a i - eta)
            (fun i ↦ if i = j then a j + eta else b i + eta)
            times) +
        uniform01Measure.real
          (gaussSignedApproximationTupleEvent
            (Real.log (N : ℝ))
            (fun i ↦ if i = j then b j - eta else a i - eta)
            (fun i ↦ if i = j then b j + eta else b i + eta)
            times) := by
  rw [closedBoundaryWindowTupleEvent_eq_union_endpointStrips]
  calc
    uniform01Measure.real
        (closedEndpointStripWindowTupleEvent a b
            (fun x i ↦
              (gaussPrefixMarkedPoint N (times i)
                (selectedGaussPrefixWord (times i) x) x).2.1)
            eta j (a j) ∪
          closedEndpointStripWindowTupleEvent a b
            (fun x i ↦
              (gaussPrefixMarkedPoint N (times i)
                (selectedGaussPrefixWord (times i) x) x).2.1)
            eta j (b j)) ≤
        uniform01Measure.real
            (closedEndpointStripWindowTupleEvent a b
              (fun x i ↦
                (gaussPrefixMarkedPoint N (times i)
                  (selectedGaussPrefixWord (times i) x) x).2.1)
              eta j (a j)) +
          uniform01Measure.real
            (closedEndpointStripWindowTupleEvent a b
              (fun x i ↦
                (gaussPrefixMarkedPoint N (times i)
                  (selectedGaussPrefixWord (times i) x) x).2.1)
              eta j (b j)) := measureReal_union_le _ _
    _ = _ := by
      rw [uniform01Measure_real_closedEndpointStrip_markedValue_eq_signed,
        uniform01Measure_real_closedEndpointStrip_markedValue_eq_signed]

end

end Erdos1002
