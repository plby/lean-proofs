import ErdosProblems.Erdos1002.GaussPrefixDeepestCylinder
import ErdosProblems.Erdos1002.GaussPrefixMixedChronology
import ErdosProblems.Erdos1002.GaussPrefixMarkedPrefixCylinder
import ErdosProblems.Erdos1002.GaussDenominatorMaximal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Absolute carrier scale on the maximal denominator good event

This file connects the deterministic carrier-separation theorem to the
single process-level denominator good event.  It does not replace the good
event by a pointwise-in-time family: one membership hypothesis supplies the
simultaneous logarithmic denominator bounds, and a point in a deepest
cylinder transfers the bound to that cylinder's literal terminal
denominator.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixMarkedCarrierGoodEventPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- Direct lower and upper logarithmic denominator bounds extracted from
the maximal good event at one admissible depth. -/
theorem log_gaussPrefixDenominator_bounds_of_mem_linearGoodEvent
    {C L n : ℕ} {Δ x : ℝ}
    (hx : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hn : n ≤ C * L) :
    (n : ℝ) * gaussRoofMean - Δ * (L : ℝ) ≤
        Real.log
          (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ) ∧
      Real.log
          (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ) ≤
        (n : ℝ) * gaussRoofMean + Δ * (L : ℝ) := by
  have hdev := hx n hn
  have habs := abs_le.mp hdev
  constructor <;> linarith

/-- Exponentiated form of the preceding bounds.  Positivity of the selected
terminal denominator is proved from the positivity of its digit word. -/
theorem gaussPrefixDenominator_exp_bounds_of_mem_linearGoodEvent
    {C L n : ℕ} {Δ x : ℝ}
    (hx : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hn : n ≤ C * L) :
    Real.exp ((n : ℝ) * gaussRoofMean - Δ * (L : ℝ)) ≤
        (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ) ∧
      (cfTerminalDenominator (selectedGaussPrefixWord n x).1 : ℝ) ≤
        Real.exp ((n : ℝ) * gaussRoofMean + Δ * (L : ℝ)) := by
  have hlog :=
    log_gaussPrefixDenominator_bounds_of_mem_linearGoodEvent hx hn
  have hdenPos : (0 : ℝ) <
      cfTerminalDenominator (selectedGaussPrefixWord n x).1 := by
    exact_mod_cast cfTerminalDenominator_pos
      (selectedGaussPrefixWord n x).2.2
  constructor
  · calc
      Real.exp ((n : ℝ) * gaussRoofMean - Δ * (L : ℝ)) ≤
          Real.exp (Real.log
            (cfTerminalDenominator
              (selectedGaussPrefixWord n x).1 : ℝ)) :=
        Real.exp_le_exp.mpr hlog.1
      _ = (cfTerminalDenominator
          (selectedGaussPrefixWord n x).1 : ℝ) := Real.exp_log hdenPos
  · calc
      (cfTerminalDenominator
          (selectedGaussPrefixWord n x).1 : ℝ) =
          Real.exp (Real.log
            (cfTerminalDenominator
              (selectedGaussPrefixWord n x).1 : ℝ)) :=
        (Real.exp_log hdenPos).symm
      _ ≤ Real.exp ((n : ℝ) * gaussRoofMean + Δ * (L : ℝ)) :=
        Real.exp_le_exp.mpr hlog.2

/-- If one point of an exact-depth cylinder lies in the global denominator
good event, the deepest word itself has the corresponding exponential
terminal-denominator bounds.  No representative-point substitution is
made here. -/
theorem exactDepthTerminalDenominator_exp_bounds_of_goodPoint
    {C L m R : ℕ} {Δ x : ℝ}
    (w : ExactDepthBoundedPositiveWord R m)
    (hm : m ≤ C * L)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hxCell : x ∈ exactDepthBoundedCylinder w) :
    Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)) ≤
        (cfTerminalDenominator w.1.1 : ℝ) ∧
      (cfTerminalDenominator w.1.1 : ℝ) ≤
        Real.exp ((m : ℝ) * gaussRoofMean + Δ * (L : ℝ)) := by
  have hselected : selectedGaussPrefixWord m x = w.toPositive :=
    selectedGaussPrefixWord_eq_of_mem w.toPositive hxCell
  simpa only [hselected] using!
    gaussPrefixDenominator_exp_bounds_of_mem_linearGoodEvent hxGood hm

/-- Final absolute carrier floor on a good deepest cylinder.  The relative
non-cancellation comes from chronological separation; the absolute scale
comes only from the single maximal denominator good event. -/
theorem exp_half_le_abs_exactDepthCylinderMixedCarrier_of_gap_goodPoint
    {ι : Type*} [Fintype ι]
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ x : ℝ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (hm : m ≤ C * L)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hxCell : x ∈ exactDepthBoundedCylinder w) :
    Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)) / 2 ≤
      |exactDepthCylinderMixedCarrier N k h F w| := by
  have hQ :=
    (exactDepthTerminalDenominator_exp_bounds_of_goodPoint
      w hm hxGood hxCell).1
  have hcarrier :=
    half_terminalDenominator_le_abs_exactDepthCylinderMixedCarrier_of_gap
      N k h F hF w z₀ hdepth hcoeff hgap hweightBudget
  exact (div_le_div_of_nonneg_right hQ (by norm_num)).trans hcarrier

/-- Absolute carrier floor for the truncated prefix at a late-case split.
Only occurrences up to `m` enter the weight budget; later occurrences may
have arbitrary depths provided their Fourier weights vanish, exactly as in
the prefix--future decomposition. -/
theorem exp_half_le_abs_exactDepthCylinderMixedPrefixCarrier_of_gap_goodPoint
    {ι : Type*} [Fintype ι]
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ x : ℝ}
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (hm : m ≤ C * L)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hxCell : x ∈ exactDepthBoundedCylinder w) :
    Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)) / 2 ≤
      |exactDepthCylinderMixedPrefixCarrier N k h F w| := by
  have hQ :=
    (exactDepthTerminalDenominator_exp_bounds_of_goodPoint
      w hm hxGood hxCell).1
  have hcarrier :=
    half_terminalDenominator_le_abs_exactDepthCylinderMixedPrefixCarrier_of_gap
      N k h F w z₀ hdepth hcoeff hgap hweightBudget
  exact (div_le_div_of_nonneg_right hQ (by norm_num)).trans hcarrier

/-- Literal late-case one-cylinder oscillatory estimate.  Unlike the
all-occurrence theorem below, this integrates only the prefix character,
so no depth hypothesis is imposed on the future zero modes. -/
theorem norm_setIntegral_mixedPrefixCharacter_compactValue_le_of_gap_goodPoint
    {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ x A : ℝ}
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (lower upper : ι → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hm : m ≤ C * L)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hxCell : x ∈ exactDepthBoundedCylinder w) :
    ‖∫ y in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F m y ∂uniform01Measure‖ ≤
      2 / (Real.pi * (N : ℝ) *
        Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ))) := by
  obtain ⟨left, right, _hlr, hinterval⟩ :=
    exists_intervalIntegral_eq_setIntegral_mixedPrefixCharacter_compactValue
      N hN k h F w lower upper hlower hupper hsmall
  rw [hinterval]
  let E : ℝ :=
    Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ))
  let D : ℝ := exactDepthCylinderMixedPrefixCarrier N k h F w
  have hE : 0 < E := by
    dsimp only [E]
    positivity
  have hDfloor : E / 2 ≤ |D| := by
    exact exp_half_le_abs_exactDepthCylinderMixedPrefixCarrier_of_gap_goodPoint
      N k h F w z₀ hdepth hcoeff hgap hweightBudget hm hxGood hxCell
  have hD : D ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hDfloor
    linarith
  have hone :=
    norm_intervalIntegral_oscillatoryPhase_nat_mul_le
      left right D N (by omega) hD
  calc
    ‖∫ y : ℝ in left..right,
        oscillatoryPhase ((N : ℝ) * D) y‖ ≤
        1 / (Real.pi * (N : ℝ) * |D|) := hone
    _ ≤ 1 / (Real.pi * (N : ℝ) * (E / 2)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact mul_le_mul_of_nonneg_left hDfloor (by positivity)
    _ = 2 / (Real.pi * (N : ℝ) * E) := by
      field_simp

/-- Summed late-case prefix-cylinder bound over an arbitrary retained
family of exact-depth cells.  The quadratic cylinder count is proved inside
the theorem, rather than assumed as an external cardinality estimate. -/
theorem norm_sum_setIntegral_mixedPrefixCharacter_compactValue_le_of_gap_goodCells
    {ι : Type*} [Fintype ι]
    (N R : ℕ) (hN : 2 ≤ N) (hRN : R ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ A : ℝ}
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (lower upper : ι → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hm : m ≤ C * L)
    (cells : Finset (ExactDepthBoundedPositiveWord R m))
    (hGoodCell : ∀ w ∈ cells, ∃ x : ℝ,
      x ∈ gaussDenominatorLinearGoodEvent C L Δ ∧
        x ∈ exactDepthBoundedCylinder w) :
    ‖∑ w ∈ cells,
        ∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedPrefixCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F m y ∂uniform01Measure‖ ≤
      ((2 * (R + 1) ^ 2 : ℕ) : ℝ) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)))) := by
  let cellBound : ℝ :=
    2 / (Real.pi * (N : ℝ) *
      Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)))
  have hcellBound : 0 ≤ cellBound := by
    dsimp only [cellBound]
    positivity
  have hOne (w : ExactDepthBoundedPositiveWord R m) (hw : w ∈ cells) :
      ‖∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedPrefixCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F m y ∂uniform01Measure‖ ≤ cellBound := by
    obtain ⟨x, hxGood, hxCell⟩ := hGoodCell w hw
    have hxCell' : x ∈ exactDepthBoundedCylinder (w.mono hRN) := by
      simpa only [exactDepthBoundedCylinder_mono] using! hxCell
    simpa only [cellBound] using!
      norm_setIntegral_mixedPrefixCharacter_compactValue_le_of_gap_goodPoint
        N hN k h F (w.mono hRN) z₀ hdepth hcoeff hgap hweightBudget
          lower upper hlower hupper hsmall hm hxGood hxCell'
  have hcard : cells.card ≤ 2 * (R + 1) ^ 2 :=
    (Finset.card_le_univ cells).trans
      (card_exactDepthBoundedPositiveWord_le R m)
  calc
    ‖∑ w ∈ cells,
        ∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedPrefixCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F m y ∂uniform01Measure‖ ≤
        ∑ w ∈ cells,
          ‖∫ y in exactDepthBoundedCylinder (w.mono hRN),
            gaussPrefixMarkedMixedPrefixCharacter N
              (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
              k h F m y ∂uniform01Measure‖ := norm_sum_le _ _
    _ ≤ ∑ _w ∈ cells, cellBound := by
      exact Finset.sum_le_sum fun w hw ↦ hOne w hw
    _ = (cells.card : ℝ) * cellBound := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * (R + 1) ^ 2 : ℕ) : ℝ) * cellBound := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hcellBound
    _ = ((2 * (R + 1) ^ 2 : ℕ) : ℝ) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)))) := rfl

/-- A complete literal one-cylinder oscillatory estimate on the good
denominator event.  The integrand is the actual compact-window mixed tuple
character; the proof first converts it to one interval integral, then uses
the proved absolute carrier floor. -/
theorem norm_setIntegral_mixedTupleCharacter_compactValue_le_of_gap_goodPoint
    {ι : Type*} [Fintype ι]
    (N : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ x A : ℝ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (lower upper : ι → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hm : m ≤ C * L)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hxCell : x ∈ exactDepthBoundedCylinder w) :
    ‖∫ y in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F y ∂uniform01Measure‖ ≤
      2 / (Real.pi * (N : ℝ) *
        Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ))) := by
  obtain ⟨left, right, _hlr, hinterval⟩ :=
    exists_intervalIntegral_eq_setIntegral_mixedTupleCharacter_compactValue
      N hN k h F hF w lower upper hlower hupper hsmall
  rw [hinterval]
  let E : ℝ :=
    Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ))
  let D : ℝ := exactDepthCylinderMixedCarrier N k h F w
  have hE : 0 < E := by
    dsimp only [E]
    positivity
  have hDfloor : E / 2 ≤ |D| := by
    exact exp_half_le_abs_exactDepthCylinderMixedCarrier_of_gap_goodPoint
      N k h F hF w z₀ hdepth hcoeff hgap hweightBudget hm hxGood hxCell
  have hD : D ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hDfloor
    linarith
  have hone :=
    norm_intervalIntegral_oscillatoryPhase_nat_mul_le
      left right D N (by omega) hD
  calc
    ‖∫ y : ℝ in left..right,
        oscillatoryPhase ((N : ℝ) * D) y‖ ≤
        1 / (Real.pi * (N : ℝ) * |D|) := hone
    _ ≤ 1 / (Real.pi * (N : ℝ) * (E / 2)) := by
      apply one_div_le_one_div_of_le
      · positivity
      · exact mul_le_mul_of_nonneg_left hDfloor (by positivity)
    _ = 2 / (Real.pi * (N : ℝ) * E) := by
      field_simp

/-- Summed literal cylinder estimate for one separated mixed tuple under a
sharper cutoff `R ≤ N`.  Each retained exact-depth cylinder is required only
to contain one point of the global good event; the preceding theorem then
controls its complete cylinder integral.  The number of such cylinders is
bounded internally by the proved quadratic terminal-pair code. -/
theorem norm_sum_setIntegral_mixedTupleCharacter_compactValue_le_of_gap_goodCells
    {ι : Type*} [Fintype ι]
    (N R : ℕ) (hN : 2 ≤ N) (hRN : R ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ A : ℝ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (lower upper : ι → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hm : m ≤ C * L)
    (cells : Finset (ExactDepthBoundedPositiveWord R m))
    (hGoodCell : ∀ w ∈ cells, ∃ x : ℝ,
      x ∈ gaussDenominatorLinearGoodEvent C L Δ ∧
        x ∈ exactDepthBoundedCylinder w) :
    ‖∑ w ∈ cells,
        ∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤
      ((2 * (R + 1) ^ 2 : ℕ) : ℝ) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)))) := by
  let cellBound : ℝ :=
    2 / (Real.pi * (N : ℝ) *
      Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)))
  have hcellBound : 0 ≤ cellBound := by
    dsimp only [cellBound]
    positivity
  have hOne (w : ExactDepthBoundedPositiveWord R m) (hw : w ∈ cells) :
      ‖∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤ cellBound := by
    obtain ⟨x, hxGood, hxCell⟩ := hGoodCell w hw
    have hxCell' : x ∈ exactDepthBoundedCylinder (w.mono hRN) := by
      simpa only [exactDepthBoundedCylinder_mono] using! hxCell
    simpa only [cellBound] using!
      norm_setIntegral_mixedTupleCharacter_compactValue_le_of_gap_goodPoint
        N hN k h F hF (w.mono hRN) z₀ hdepth hcoeff hgap
          hweightBudget lower upper hlower hupper hsmall hm hxGood hxCell'
  have hcard : cells.card ≤ 2 * (R + 1) ^ 2 :=
    (Finset.card_le_univ cells).trans
      (card_exactDepthBoundedPositiveWord_le R m)
  calc
    ‖∑ w ∈ cells,
        ∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤
        ∑ w ∈ cells,
          ‖∫ y in exactDepthBoundedCylinder (w.mono hRN),
            gaussPrefixMarkedMixedTupleCharacter N
              (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
              k h F y ∂uniform01Measure‖ := norm_sum_le _ _
    _ ≤ ∑ _w ∈ cells, cellBound := by
      exact Finset.sum_le_sum fun w hw ↦ hOne w hw
    _ = (cells.card : ℝ) * cellBound := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * (R + 1) ^ 2 : ℕ) : ℝ) * cellBound := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hcellBound
    _ = ((2 * (R + 1) ^ 2 : ℕ) : ℝ) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp ((m : ℝ) * gaussRoofMean - Δ * (L : ℝ)))) := rfl

end

end Erdos1002
