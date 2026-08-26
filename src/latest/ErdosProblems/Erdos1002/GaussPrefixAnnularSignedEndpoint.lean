import ErdosProblems.Erdos1002.GaussPrefixAnnularTorusEventBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Null signed-window endpoints for selected Gauss prefixes

Literal annular cells are half-open, whereas the closed approximation
windows used in the canonical Fourier measure are technically more
convenient.  They are not pointwise equal.  This file proves the exact
almost-everywhere replacement under the finite-denominator and Legendre
conditions that occur in the literal/canonical comparison.
-/

open Filter MeasureTheory Set

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularSignedEndpointPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- At one fixed depth, the selected signed approximation coordinate
cannot equal a prescribed value almost everywhere, provided the selected
prefix has denominator at most `N` and lies in Legendre's range.

The proof sends the selected prefix to its genuine primitive resonance.
Its denominator belongs to the finite set `[1,N]`, and each resulting
scaled-resonance level set is already known to be null. -/
theorem
    ae_gaussSignedScaledApproximationCoordinate_ne_of_selectedDenominator_le
    {N n : ℕ} (hN : 2 ≤ N) (c : ℝ) :
    ∀ᵐ x ∂uniform01Measure,
      cfTerminalDenominator (selectedGaussPrefixWord n x).1 ≤ N →
      gaussApproximationCoordinate n x < (1 : ℝ) / 2 →
      gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x ≠ c := by
  have havoid :
      ∀ᵐ x ∂uniform01Measure, ∀ p : ℕ,
        p ∈ Finset.Icc 1 N →
          scaledResonanceCoordinate N p x ≠ c := by
    rw [ae_all_iff]
    intro p
    by_cases hpIcc : p ∈ Finset.Icc 1 N
    · have hp : 0 < p := by
        have := (Finset.mem_Icc.mp hpIcc).1
        omega
      have hnull :
          uniform01Measure
            {x : ℝ | scaledResonanceCoordinate N p x = c} = 0 :=
        uniform01Measure_scaledResonanceCoordinate_levelSet_eq_zero
          hN hp c
      exact
        (measure_eq_zero_iff_ae_notMem.mp hnull).mono
          (fun x hx _hpIcc heq ↦ hx heq)
    · exact Eventually.of_forall
        (fun _x hp ↦ (hpIcc hp).elim)
  filter_upwards [ae_nonterminating_uniform01, havoid] with
    x hxGood hxAvoid
  intro hden hsmall heq
  let w : PositiveDigitWord n := selectedGaussPrefixWord n x
  let p : ℕ := cfTerminalDenominator w.1
  have hdomain :
      x ∈ positivePrefixDomain n :=
    mem_positivePrefixDomain_of_nonterminating hxGood.1 hxGood.2
  have hw : x ∈ positivePrefixCylinder n w := by
    exact selectedGaussPrefixWord_mem hdomain
  have hp : 0 < p := cfTerminalDenominator_pos w.2.2
  have hpIcc : p ∈ Finset.Icc 1 N := by
    exact Finset.mem_Icc.mpr ⟨hp, hden⟩
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating
      hxGood.1 hxGood.2 (n + 1)
  have hpoint :=
    markedResonancePoint_terminalDenominator_eq_gaussPrefixMarkedPoint
      (N := N) w hxGood.1 hex hw hsmall
  have hcoordinate :
      scaledResonanceCoordinate N p x =
        gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x := by
    have hvalue :=
      congrArg (fun z : ℝ × ℝ × ℝ ↦ z.2.1) hpoint
    simpa only [p, markedResonancePoint,
      gaussPrefixMarkedPoint_value_eq_signedScaledApproximation] using!
      hvalue
  exact hxAvoid p hpIcc (hcoordinate.trans heq)

/-- Half-open variant of the signed approximation tuple event. -/
def gaussSignedApproximationTupleEventIco
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) : Set ℝ :=
  orderedEventIntersection <| List.ofFn fun i ↦
    Ioc (0 : ℝ) 1 ∩
      gaussSignedScaledApproximationCoordinate scale (times i) ⁻¹'
        Ico (lower i) (upper i)

theorem measurableSet_gaussSignedApproximationTupleEventIco
    {r : ℕ} (scale : ℝ) (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    MeasurableSet
      (gaussSignedApproximationTupleEventIco
        scale lower upper times) := by
  apply measurableSet_orderedEventIntersection
  intro E hE
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hE
  exact measurableSet_Ioc.inter
    (measurableSet_Ico.preimage
      (measurable_gaussSignedScaledApproximationCoordinate
        scale (times i)))

/-- Coordinatewise closed and half-open signed tuple windows agree almost
everywhere on the finite-denominator, Legendre-range carrier.

The carrier hypotheses are implications rather than an extra set in the
definition, so this statement can be intersected with any literal time,
torus, good-event, or chronological condition without changing it. -/
theorem ae_mem_gaussSignedApproximationTupleEvent_iff_Ico_of_carrier
    {r N : ℕ} (hN : 2 ≤ N)
    (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ) :
    ∀ᵐ x ∂uniform01Measure,
      (∀ j : Fin r,
        cfTerminalDenominator
            (selectedGaussPrefixWord (times j) x).1 ≤ N ∧
          gaussApproximationCoordinate (times j) x < (1 : ℝ) / 2) →
      (x ∈ gaussSignedApproximationTupleEvent
            (Real.log (N : ℝ)) lower upper times ↔
        x ∈ gaussSignedApproximationTupleEventIco
            (Real.log (N : ℝ)) lower upper times) := by
  have hne :
      ∀ᵐ x ∂uniform01Measure, ∀ j : Fin r,
        cfTerminalDenominator
            (selectedGaussPrefixWord (times j) x).1 ≤ N →
        gaussApproximationCoordinate (times j) x < (1 : ℝ) / 2 →
        gaussSignedScaledApproximationCoordinate
            (Real.log (N : ℝ)) (times j) x ≠ upper j := by
    rw [ae_all_iff]
    intro j
    exact
      ae_gaussSignedScaledApproximationCoordinate_ne_of_selectedDenominator_le
        hN (upper j)
  filter_upwards [hne] with x hxNe
  intro hcarrier
  simp only [gaussSignedApproximationTupleEvent,
    gaussSignedApproximationTupleEventIco,
    mem_orderedEventIntersection_ofFn_iff,
    gaussSignedApproximationWindow, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_Icc, Set.mem_Ico]
  constructor
  · intro hall j
    have hj := hall j
    exact ⟨hj.1, hj.2.1,
      lt_of_le_of_ne hj.2.2
        (hxNe j (hcarrier j).1 (hcarrier j).2)⟩
  · intro hall j
    have hj := hall j
    exact ⟨hj.1, hj.2.1, hj.2.2.le⟩

/-- Intersecting with any measurable carrier on which the denominator
and Legendre hypotheses hold preserves the exact uniform mass when
closed signed windows are replaced by half-open ones. -/
theorem uniform01Measure_real_signedTupleEvent_inter_eq_Ico
    {r N : ℕ} (hN : 2 ≤ N)
    (lower upper : Fin r → ℝ)
    (times : Fin r → ℕ)
    (carrier : Set ℝ)
    (hcarrier : ∀ x ∈ carrier, ∀ j : Fin r,
      cfTerminalDenominator
          (selectedGaussPrefixWord (times j) x).1 ≤ N ∧
        gaussApproximationCoordinate (times j) x < (1 : ℝ) / 2) :
    uniform01Measure.real
        (gaussSignedApproximationTupleEvent
            (Real.log (N : ℝ)) lower upper times ∩ carrier) =
      uniform01Measure.real
        (gaussSignedApproximationTupleEventIco
            (Real.log (N : ℝ)) lower upper times ∩ carrier) := by
  apply measureReal_congr
  filter_upwards
    [ae_mem_gaussSignedApproximationTupleEvent_iff_Ico_of_carrier
      hN lower upper times] with x hx
  apply propext
  constructor
  · rintro ⟨hsigned, hxCarrier⟩
    exact ⟨(hx (hcarrier x hxCarrier)).mp hsigned, hxCarrier⟩
  · rintro ⟨hsigned, hxCarrier⟩
    exact ⟨(hx (hcarrier x hxCarrier)).mpr hsigned, hxCarrier⟩

end

end Erdos1002
