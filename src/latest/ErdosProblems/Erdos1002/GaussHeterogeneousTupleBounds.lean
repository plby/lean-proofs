import ErdosProblems.Erdos1002.GaussSignedApproximationWindows
import ErdosProblems.Erdos1002.GaussDigitQuasiBernoulli

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Mixing bounds for heterogeneous rare-digit tuples

Marked rectangles and freezing boundary terms generally give a different
positive window at each coordinate.  The homogeneous tuple estimates are
therefore not quite sufficient.  This file applies the proved Gauss digit
`psi`-mixing theorem directly to coordinate-dependent one-digit windows,
including the case with one distinguished endpoint strip.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1002

noncomputable section

/-- Pure one-digit tuple with coordinate-dependent positive windows. -/
def gaussHeterogeneousDigitTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i ↦
    (gaussOrbit (times i)) ⁻¹'
      scaledGaussFirstDigitWindow scale (lower i) (upper i)

theorem measurableSet_gaussHeterogeneousDigitTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    MeasurableSet
      (gaussHeterogeneousDigitTupleEvent scale lower upper times) := by
  apply measurableSet_orderedEventIntersection
  intro A hA
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
  exact (measurableSet_scaledGaussFirstDigitWindow _ _ _).preimage
    (measurable_gaussOrbit (times i))

/-- Direct heterogeneous product estimate from the abstract mixing
interface. -/
theorem GaussDigitPsiMixing.measure_heterogeneousDigitTupleEvent_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hgap : ∀ i j, i < j → times i + gap ≤ times j)
    (hrate : 0 ≤ rate gap) :
    gaussMeasure.real
        (gaussHeterogeneousDigitTupleEvent scale lower upper times) ≤
      (1 + rate gap) ^ (r - 1) *
        ∏ i, gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower i) (upper i)) := by
  let events : Fin r → Set ℝ := fun i ↦
    scaledGaussFirstDigitWindow scale (lower i) (upper i)
  have hmix := hpsi.measure_orderedIntersection_le hr times events gap
    (fun i ↦ measurableSet_scaledGaussFirstDigitWindow
      scale (lower i) (upper i))
    (fun i ↦ isGaussOneDigitEvent_scaledGaussFirstDigitWindow
      scale (lower i) (upper i))
    hgap0 hgap hrate
  simpa only [gaussHeterogeneousDigitTupleEvent, events] using! hmix

/-- Uniform mass corollary for a heterogeneous tuple. -/
theorem GaussDigitPsiMixing.measure_heterogeneousDigitTupleEvent_le_pow
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hgap : ∀ i j, i < j → times i + gap ≤ times j)
    (hrate : 0 ≤ rate gap) {windowMass : ℝ}
    (hwindow : ∀ i, gaussMeasure.real
      (scaledGaussFirstDigitWindow scale (lower i) (upper i)) ≤
        windowMass) :
    gaussMeasure.real
        (gaussHeterogeneousDigitTupleEvent scale lower upper times) ≤
      (1 + rate gap) ^ (r - 1) * windowMass ^ r := by
  have hbase := hpsi.measure_heterogeneousDigitTupleEvent_le
    (scale := scale) hr lower upper times gap hgap0 hgap hrate
  have hprod :
      (∏ i, gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower i) (upper i))) ≤
        windowMass ^ r := by
    calc
      (∏ i, gaussMeasure.real
          (scaledGaussFirstDigitWindow scale (lower i) (upper i))) ≤
          ∏ _i : Fin r, windowMass := by
        apply Finset.prod_le_prod
        · intro i _hi
          exact measureReal_nonneg
        · intro i _hi
          exact hwindow i
      _ = windowMass ^ r := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact hbase.trans (mul_le_mul_of_nonneg_left hprod (by positivity))

/-- Product estimate with one distinguished coordinate having the sharper
boundary-scale mass.  The underlying event is still an ordinary
heterogeneous digit tuple. -/
theorem GaussDigitPsiMixing.measure_heterogeneousDigitTupleEvent_le_distinguished
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ) (j : Fin r)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k)
    (hrate : 0 ≤ rate gap)
    {boundaryMass windowMass : ℝ}
    (hboundaryMass : 0 ≤ boundaryMass)
    (hboundary : gaussMeasure.real
      (scaledGaussFirstDigitWindow scale (lower j) (upper j)) ≤
        boundaryMass)
    (hwindow : ∀ i, i ≠ j → gaussMeasure.real
      (scaledGaussFirstDigitWindow scale (lower i) (upper i)) ≤
        windowMass) :
    gaussMeasure.real
        (gaussHeterogeneousDigitTupleEvent scale lower upper times) ≤
      (1 + rate gap) ^ (r - 1) *
        (boundaryMass * windowMass ^ (r - 1)) := by
  have hbase := hpsi.measure_heterogeneousDigitTupleEvent_le
    (scale := scale) hr lower upper times gap hgap0 hgap hrate
  have hprod := fin_prod_measure_le_boundary_mul_window_pow
    (fun i ↦ scaledGaussFirstDigitWindow scale (lower i) (upper i))
      j hboundaryMass hboundary hwindow
  exact hbase.trans (mul_le_mul_of_nonneg_left hprod (by positivity))

/-- Coordinate-dependent one-digit tuple with one distinguished endpoint
strip. -/
def gaussHeterogeneousBoundaryDigitBaseEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (center width : ℝ) (j i : Fin r) : Set ℝ :=
  if i = j then
    scaledGaussFirstDigitBoundaryStrip scale center width
  else scaledGaussFirstDigitWindow scale (lower i) (upper i)

def gaussHeterogeneousBoundaryDigitTupleEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (center width : ℝ) (times : Fin r → ℕ) (j : Fin r) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i ↦
    (gaussOrbit (times i)) ⁻¹'
      gaussHeterogeneousBoundaryDigitBaseEvent
        scale lower upper center width j i

theorem measurableSet_gaussHeterogeneousBoundaryDigitBaseEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (center width : ℝ) (j i : Fin r) :
    MeasurableSet (gaussHeterogeneousBoundaryDigitBaseEvent
      scale lower upper center width j i) := by
  by_cases hij : i = j
  · simp only [gaussHeterogeneousBoundaryDigitBaseEvent, if_pos hij]
    exact measurableSet_scaledGaussFirstDigitBoundaryStrip _ _ _
  · simp only [gaussHeterogeneousBoundaryDigitBaseEvent, if_neg hij]
    exact measurableSet_scaledGaussFirstDigitWindow _ _ _

theorem isGaussOneDigitEvent_gaussHeterogeneousBoundaryDigitBaseEvent
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (center width : ℝ) (j i : Fin r) :
    IsGaussOneDigitEvent (gaussHeterogeneousBoundaryDigitBaseEvent
      scale lower upper center width j i) := by
  by_cases hij : i = j
  · simp only [gaussHeterogeneousBoundaryDigitBaseEvent, if_pos hij]
    exact isGaussOneDigitEvent_scaledGaussFirstDigitBoundaryStrip _ _ _
  · simp only [gaussHeterogeneousBoundaryDigitBaseEvent, if_neg hij]
    exact isGaussOneDigitEvent_scaledGaussFirstDigitWindow _ _ _

/-- Heterogeneous boundary-tuple mass bound, retaining the boundary mass
and every ordinary window mass as explicit hypotheses. -/
theorem GaussDigitPsiMixing.measure_heterogeneousBoundaryDigitTupleEvent_le
    {rate : ℕ → ℝ} (hpsi : GaussDigitPsiMixing rate)
    {r : ℕ} (hr : 0 < r) {scale center width : ℝ}
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ) (j : Fin r)
    (gap : ℕ) (hgap0 : 0 < gap)
    (hgap : ∀ i k, i < k → times i + gap ≤ times k)
    (hrate : 0 ≤ rate gap)
    {boundaryMass windowMass : ℝ}
    (hboundaryMass : 0 ≤ boundaryMass)
    (hboundary : gaussMeasure.real
      (scaledGaussFirstDigitBoundaryStrip scale center width) ≤
        boundaryMass)
    (hwindow : ∀ i, i ≠ j → gaussMeasure.real
      (scaledGaussFirstDigitWindow scale (lower i) (upper i)) ≤
        windowMass) :
    gaussMeasure.real
        (gaussHeterogeneousBoundaryDigitTupleEvent
          scale lower upper center width times j) ≤
      (1 + rate gap) ^ (r - 1) *
        (boundaryMass * windowMass ^ (r - 1)) := by
  let events : Fin r → Set ℝ := fun i ↦
    gaussHeterogeneousBoundaryDigitBaseEvent
      scale lower upper center width j i
  have hmix := hpsi.measure_orderedIntersection_le hr times events gap
    (fun i ↦ measurableSet_gaussHeterogeneousBoundaryDigitBaseEvent
      scale lower upper center width j i)
    (fun i ↦ isGaussOneDigitEvent_gaussHeterogeneousBoundaryDigitBaseEvent
      scale lower upper center width j i)
    hgap0 hgap hrate
  have hprod :
      (∏ i, gaussMeasure.real (events i)) ≤
        boundaryMass * windowMass ^ (r - 1) := by
    apply fin_prod_measure_le_boundary_mul_window_pow
      events j hboundaryMass
    · simpa only [events, gaussHeterogeneousBoundaryDigitBaseEvent,
        if_pos rfl] using! hboundary
    · intro i hij
      simpa only [events, gaussHeterogeneousBoundaryDigitBaseEvent,
        if_neg hij] using! hwindow i hij
  calc
    gaussMeasure.real
        (gaussHeterogeneousBoundaryDigitTupleEvent
          scale lower upper center width times j) ≤
        (1 + rate gap) ^ (r - 1) * ∏ i,
          gaussMeasure.real (events i) := by
      simpa only [gaussHeterogeneousBoundaryDigitTupleEvent, events]
        using! hmix
    _ ≤ (1 + rate gap) ^ (r - 1) *
        (boundaryMass * windowMass ^ (r - 1)) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)

end

end Erdos1002
