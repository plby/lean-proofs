import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointSplit
import ErdosProblems.Erdos1002.GaussPrefixAnnularBadEventMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Contracted lower-retained annular Fourier tuples

This file isolates the genuinely oscillatory half of the annular
nonzero-mode argument.  A fixed contraction `eta > 0` is retained
throughout.  This is essential when the last nonzero Fourier coordinate is
also the deepest coordinate: without contraction, depths arbitrarily close
to the time-one horizon do not have a uniform oscillatory margin.

The definitions here deliberately duplicate only the one contracted
canonical family needed by this leaf.  The same expression occurs in the
literal-time transfer module; keeping this leaf below that large assembly
module avoids an import cycle.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularLowerRetainedPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-- The canonical chronological family built from time boxes contracted by
`eta` at both endpoints. -/
def lowerRetainedContractedCanonicalAnnularGridTupleFamily
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  canonicalMixedOrderParityBoxTimes N k e
    (fun z ↦ contractedAnnularTimeDepthBox N eta z.1)
    (annularOccurrenceParity k)

/-- The contracted, separated, interior tuples on the lower side of every
later midpoint band. -/
def contractedAnnularCanonicalLaterLowerMidpointTupleFamily
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  annularCanonicalLaterLowerMidpointTupleFamily
      rho N k hr e mode hmode ∩
    lowerRetainedContractedCanonicalAnnularGridTupleFamily
      N eta k e

@[simp] theorem
    mem_contractedAnnularCanonicalLaterLowerMidpointTupleFamily_iff
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k}
    {mode : Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : mode ≠ 0}
    {t : Fin (MixedOccurrenceCount k) → ℕ} :
    t ∈ contractedAnnularCanonicalLaterLowerMidpointTupleFamily
        eta rho N k hr e mode hmode ↔
      t ∈ annularCanonicalLaterLowerMidpointTupleFamily
          rho N k hr e mode hmode ∧
        t ∈ lowerRetainedContractedCanonicalAnnularGridTupleFamily
          N eta k e := by
  simp [contractedAnnularCanonicalLaterLowerMidpointTupleFamily]

/-- Contracted membership gives the literal contracted depth-box condition
at every chronological coordinate. -/
theorem contractedAnnularCanonicalLaterLowerMidpointTupleFamily_boxes
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k}
    {mode : Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : mode ≠ 0}
    {t : Fin (MixedOccurrenceCount k) → ℕ}
    (ht : t ∈ contractedAnnularCanonicalLaterLowerMidpointTupleFamily
        eta rho N k hr e mode hmode) :
    ∀ j, t j ∈ contractedAnnularTimeDepthBox N eta (e j).1 := by
  have htContracted :=
    (mem_contractedAnnularCanonicalLaterLowerMidpointTupleFamily_iff.mp
      ht).2
  obtain ⟨F, _horder, hboxes, htimes⟩ :=
    mem_canonicalMixedOrderParityBoxTimes_iff.mp htContracted
  intro j
  rw [← htimes]
  exact (hboxes j).1

/-- The lower retained family remains a subfamily of the uncontracted
canonical family. -/
theorem contractedAnnularCanonicalLaterLowerMidpointTupleFamily_subset_canonical
    {eta rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    contractedAnnularCanonicalLaterLowerMidpointTupleFamily
        eta rho N k hr e mode hmode ⊆
      canonicalAnnularGridTupleFamily N k e := by
  intro t ht
  have hlower :=
    (mem_contractedAnnularCanonicalLaterLowerMidpointTupleFamily_iff.mp
      ht).1
  have hinterior :=
    (mem_laterLowerMidpointNatTupleFamily_iff.mp hlower).1
  have hseparated :=
    (mem_lateFirstNatTupleFamily_iff.mp hinterior).1
  exact (mem_separatedNatTupleFamily_iff.mp hseparated).1

/-- Every contracted lower-retained tuple is chronological. -/
theorem contractedAnnularCanonicalLaterLowerMidpointTupleFamily_chronological
    {eta rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e mode hmode) :
    IsChronologicalNatTuple t :=
  canonicalAnnularGridTupleFamily_chronological N k e t
    (contractedAnnularCanonicalLaterLowerMidpointTupleFamily_subset_canonical
      k hr e mode hmode ht)

/-- The deepest chronological index of a nonempty tuple. -/
def annularDeepestIndex
    {r : ℕ} (hr : 0 < r) : Fin r :=
  ⟨r - 1, by omega⟩

theorem le_annularDeepestIndex
    {r : ℕ} (hr : 0 < r) (j : Fin r) :
    j ≤ annularDeepestIndex hr := by
  apply Fin.le_iff_val_le_val.mpr
  dsimp only [annularDeepestIndex]
  omega

/-- A chronological tuple attains its largest depth at
`annularDeepestIndex`. -/
theorem chronological_le_deepest
    {r : ℕ} (hr : 0 < r) {t : Fin r → ℕ}
    (hchronological : IsChronologicalNatTuple t) (j : Fin r) :
    t j ≤ t (annularDeepestIndex hr) := by
  by_cases hj : j = annularDeepestIndex hr
  · rw [hj]
  · have hjlt : j < annularDeepestIndex hr :=
      lt_of_le_of_ne (le_annularDeepestIndex hr j) hj
    exact (Nat.le_add_right (t j) 1).trans
      (hchronological j (annularDeepestIndex hr) hjlt)

/-- If the last nonzero coordinate is not deepest, the lower midpoint
condition applies to the deepest coordinate itself. -/
theorem lowerMidpoint_deepest_inequality_of_center_ne_deepest
    {r H W : ℕ} (hr : 0 < r)
    {centerIndex : Fin r} {t : Fin r → ℕ}
    (hcenter : centerIndex ≠ annularDeepestIndex hr)
    (hlower : ∀ j : Fin r, centerIndex < j →
      2 * t j + W ≤ H + t centerIndex) :
    2 * t (annularDeepestIndex hr) + W ≤
      H + t centerIndex := by
  have hcenterLe : centerIndex ≤ annularDeepestIndex hr :=
    le_annularDeepestIndex hr centerIndex
  have hcenterLt : centerIndex < annularDeepestIndex hr :=
    lt_of_le_of_ne hcenterLe hcenter
  exact hlower (annularDeepestIndex hr) hcenterLt

/-- The deepest coordinate of every contracted tuple stays below the
contracted time-one endpoint.  This is the endpoint margin needed in the
case where the last nonzero mode is itself deepest. -/
theorem contractedLower_deepest_lt_timeOneEndpoint
    {eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid) (hlog : 0 < Real.log (N : ℝ))
    {k : AnnularGridIndex grid → ℕ}
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    {t : Fin (MixedOccurrenceCount k) → ℕ}
    (ht : t ∈ contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e mode hmode) :
    t (annularDeepestIndex hr) <
      gaussLogDepthEndpoint N (1 - eta) := by
  let j := annularDeepestIndex hr
  have hbox :=
    contractedAnnularCanonicalLaterLowerMidpointTupleFamily_boxes ht j
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  exact
    lt_gaussLogDepthEndpoint_one_sub_of_mem_contractedAnnularTimeDepthBox
      hgrid hlog (e j).1 (htime (e j).1 hactive) hbox

/-- Complete deterministic alternative for the exponent in the early
cylinder estimate.  If the carrier coordinate is not deepest, the moving
midpoint band supplies the margin; if it is deepest, contraction supplies
the time-one margin. -/
theorem contractedLower_midpoint_or_timeOne_margin
    {eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid) (hlog : 0 < Real.log (N : ℝ))
    {k : AnnularGridIndex grid → ℕ}
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    {t : Fin (MixedOccurrenceCount k) → ℕ}
    (ht : t ∈ contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e mode hmode) :
    let s := annularLastNonzeroIndex mode hmode
    let d := annularDeepestIndex hr
    (s ≠ d ∧
        2 * t d + annularMidpointBandWidth rho N ≤
          annularDepthAmbientSize N + t s) ∨
      (s = d ∧
        t d < gaussLogDepthEndpoint N (1 - eta)) := by
  let s := annularLastNonzeroIndex mode hmode
  let d := annularDeepestIndex hr
  have hlowerMem :=
    (mem_contractedAnnularCanonicalLaterLowerMidpointTupleFamily_iff.mp
      ht).1
  have hlower :=
    (mem_laterLowerMidpointNatTupleFamily_iff.mp hlowerMem).2.2
  by_cases hsd : s = d
  · right
    refine ⟨hsd, ?_⟩
    exact contractedLower_deepest_lt_timeOneEndpoint
      hgrid hlog hr htime e mode hmode ht
  · left
    refine ⟨hsd, ?_⟩
    exact
      lowerMidpoint_deepest_inequality_of_center_ne_deepest
        hr hsd hlower

/-! ## Terminal-denominator restricted cylinder families -/

/-- Tighten the ambient terminal-denominator cutoff of an exact-depth
word when a sharper bound has been proved.  The digit word is unchanged. -/
def exactDepthBoundedPositiveWordTighten
    {N R m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (hR : cfTerminalDenominator w.1.1 ≤ R) :
    ExactDepthBoundedPositiveWord R m :=
  ⟨⟨w.1.1, w.1.2.1, w.1.2.2.1, hR⟩, w.2⟩

@[simp] theorem exactDepthBoundedPositiveWordTighten_val
    {N R m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (hR : cfTerminalDenominator w.1.1 ≤ R) :
    (exactDepthBoundedPositiveWordTighten w hR).1.1 = w.1.1 := rfl

/-- Any family of depth-`m` words whose actual terminal denominators are
at most `R` inherits the quadratic `O(R²)` word count, even when its
ambient type uses a larger cutoff `N`. -/
theorem card_exactDepthCells_le_of_terminalDenominator_le
    {N R m : ℕ}
    (cells : Finset (ExactDepthBoundedPositiveWord N m))
    (hR : ∀ w ∈ cells, cfTerminalDenominator w.1.1 ≤ R) :
    cells.card ≤ 2 * (R + 1) ^ 2 := by
  let f : (↥cells) → ExactDepthBoundedPositiveWord R m :=
    fun w ↦ exactDepthBoundedPositiveWordTighten w.1 (hR w.1 w.2)
  have hf : Function.Injective f := by
    intro w v hwv
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u ↦ u.1.1) hwv
  calc
    cells.card = Fintype.card (↥cells) := by
      simp
    _ ≤ Fintype.card (ExactDepthBoundedPositiveWord R m) :=
      Fintype.card_le_of_injective f hf
    _ ≤ 2 * (R + 1) ^ 2 :=
      card_exactDepthBoundedPositiveWord_le R m

/-- The exact depth-`m` cells whose complete prefix word satisfies the
simultaneous denominator envelope through depth `m`. -/
def exactDepthPrefixGoodCells
    (N m L : ℕ) (Delta : ℝ) :
    Finset (ExactDepthBoundedPositiveWord N m) :=
  Finset.univ.filter fun w ↦
    w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta

@[simp] theorem mem_exactDepthPrefixGoodCells_iff
    {N m L : ℕ} {Delta : ℝ}
    {w : ExactDepthBoundedPositiveWord N m} :
    w ∈ exactDepthPrefixGoodCells N m L Delta ↔
      w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta := by
  simp [exactDepthPrefixGoodCells]

/-- The prefix-good cells obey the quadratic count with the explicit
exponential cutoff supplied by the denominator envelope. -/
theorem card_exactDepthPrefixGoodCells_le
    {N m L R : ℕ} {Delta : ℝ}
    (hR :
      ⌈Real.exp
          ((m : ℝ) * gaussRoofMean + Delta * (L : ℝ))⌉₊ ≤ R) :
    (exactDepthPrefixGoodCells N m L Delta).card ≤
      2 * (R + 1) ^ 2 := by
  apply card_exactDepthCells_le_of_terminalDenominator_le
  intro w hw
  have hupper :=
    (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
      w.toPositive
      (mem_exactDepthPrefixGoodCells_iff.mp hw)
      (show m ≤ m by rfl)).2
  have htake : w.toPositive.1.take m = w.toPositive.1 := by
    calc
      w.toPositive.1.take m =
          w.toPositive.1.take w.toPositive.1.length :=
        congrArg (fun q ↦ w.toPositive.1.take q)
          w.toPositive.2.1.symm
      _ = w.toPositive.1 := List.take_length
  have hupper' :
      (cfTerminalDenominator w.1.1 : ℝ) ≤
        Real.exp
          ((m : ℝ) * gaussRoofMean + Delta * (L : ℝ)) := by
    simpa only [positiveDigitWordTake_val, htake] using! hupper
  have hcast :
      (cfTerminalDenominator w.1.1 : ℝ) ≤
        (⌈Real.exp
          ((m : ℝ) * gaussRoofMean + Delta * (L : ℝ))⌉₊ : ℝ) :=
    hupper'.trans (Nat.le_ceil _)
  have hnat :
      cfTerminalDenominator w.1.1 ≤
        ⌈Real.exp
          ((m : ℝ) * gaussRoofMean + Delta * (L : ℝ))⌉₊ := by
    exact_mod_cast hcast
  exact hnat.trans hR

variable {ι : Type*} [Fintype ι]

/-- Restricting a mixed character to the genuine prefix-good event is
exactly the finite sum over the prefix-good exact-depth cylinders.  The
proof first restricts to the finite deepest-cylinder support and then uses
the fact that the selected depth-`m` word is constant on each cylinder.
Thus no boundary term, countable interchange, or representative-point
argument is hidden. -/
theorem
    setIntegral_gaussPrefixMarkedMixedTupleCharacter_prefixGoodEvent_eq_sum
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i))
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (i₀ : ι) (j₀ : Fin (k i₀))
    {m L : ℕ} {Delta : ℝ}
    (hdepth : (F i₀ j₀ : ℕ) = m)
    (hm : 0 < m) :
    (∫ x in gaussDenominatorPrefixGoodEvent m L Delta,
        gaussPrefixMarkedMixedTupleCharacter N B k h F x
          ∂uniform01Measure) =
      ∑ w ∈ exactDepthPrefixGoodCells N m L Delta,
        ∫ x in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N B k h F x
            ∂uniform01Measure := by
  let f : ℝ → ℂ :=
    gaussPrefixMarkedMixedTupleCharacter N B k h F
  let G : Set ℝ := gaussDenominatorPrefixGoodEvent m L Delta
  let S : Set ℝ := exactDepthBoundedCylinderUnion N m
  have hG : MeasurableSet G :=
    measurableSet_gaussDenominatorPrefixGoodEvent m L Delta
  have hS : MeasurableSet S :=
    measurableSet_exactDepthBoundedCylinderUnion N m
  have hf : Integrable f uniform01Measure :=
    integrable_gaussPrefixMarkedMixedTupleCharacter
      N hB k h F uniform01Measure
  have hsupport : G.indicator f = S.indicator (G.indicator f) := by
    funext x
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
    · rw [Set.indicator_of_notMem hxS]
      have hzero :
          f x = 0 :=
        gaussPrefixMarkedMixedTupleCharacter_eq_zero_of_not_mem_depthUnion
          N B k h F i₀ j₀ (by simpa only [hdepth] using! hm) (by
            have hxS' :
                x ∉ exactDepthBoundedCylinderUnion N
                  (F i₀ j₀ : ℕ) := by
              rw [hdepth]
              simpa only [S] using! hxS
            exact hxS')
      simp only [Set.indicator, hzero, ite_self]
  have hpartition :
      (∫ x in G, f x ∂uniform01Measure) =
        ∑ w : ExactDepthBoundedPositiveWord N m,
          ∫ x in exactDepthBoundedCylinder w,
            G.indicator f x ∂uniform01Measure := by
    calc
      (∫ x in G, f x ∂uniform01Measure) =
          ∫ x, G.indicator f x ∂uniform01Measure := by
        rw [integral_indicator hG]
      _ = ∫ x, S.indicator (G.indicator f) x
            ∂uniform01Measure := by rw [← hsupport]
      _ = ∫ x in S, G.indicator f x ∂uniform01Measure := by
        rw [integral_indicator hS]
      _ = ∑ w : ExactDepthBoundedPositiveWord N m,
          ∫ x in exactDepthBoundedCylinder w,
            G.indicator f x ∂uniform01Measure := by
        exact integral_iUnion_fintype
          (fun w ↦ measurableSet_exactDepthBoundedCylinder w)
          (pairwise_disjoint_exactDepthBoundedCylinder N m)
          (fun _w ↦ (hf.indicator hG).integrableOn)
  rw [hpartition]
  calc
    (∑ w : ExactDepthBoundedPositiveWord N m,
        ∫ x in exactDepthBoundedCylinder w,
          G.indicator f x ∂uniform01Measure) =
      ∑ w : ExactDepthBoundedPositiveWord N m,
        if w.toPositive ∈
            gaussDenominatorPrefixGoodWords m L Delta then
          ∫ x in exactDepthBoundedCylinder w,
            f x ∂uniform01Measure
        else 0 := by
      apply Finset.sum_congr rfl
      intro w _hw
      by_cases hwGood :
          w.toPositive ∈
            gaussDenominatorPrefixGoodWords m L Delta
      · rw [if_pos hwGood]
        rw [← integral_indicator
          (measurableSet_exactDepthBoundedCylinder w),
          ← integral_indicator
            (measurableSet_exactDepthBoundedCylinder w)]
        apply integral_congr_ae
        filter_upwards with x
        by_cases hxCell : x ∈ exactDepthBoundedCylinder w
        · have hselected :
              selectedGaussPrefixWord m x = w.toPositive :=
            selectedGaussPrefixWord_eq_of_mem w.toPositive hxCell
          have hxG : x ∈ G := by
            simpa only [G, gaussDenominatorPrefixGoodEvent,
              Set.mem_preimage, hselected] using! hwGood
          simp [Set.indicator_of_mem hxCell,
            Set.indicator_of_mem hxG]
        · simp [Set.indicator_of_notMem hxCell]
      · rw [if_neg hwGood]
        calc
          (∫ x in exactDepthBoundedCylinder w,
              G.indicator f x ∂uniform01Measure) =
              ∫ _x : ℝ, (0 : ℂ) ∂uniform01Measure := by
            rw [← integral_indicator
              (measurableSet_exactDepthBoundedCylinder w)]
            apply integral_congr_ae
            filter_upwards with x
            by_cases hxCell : x ∈ exactDepthBoundedCylinder w
            · have hselected :
                  selectedGaussPrefixWord m x = w.toPositive :=
                selectedGaussPrefixWord_eq_of_mem w.toPositive hxCell
              have hxNotG : x ∉ G := by
                simpa only [G, gaussDenominatorPrefixGoodEvent,
                  Set.mem_preimage, hselected] using! hwGood
              simp [Set.indicator_of_mem hxCell,
                Set.indicator_of_notMem hxNotG]
            · simp [Set.indicator_of_notMem hxCell]
          _ = 0 := by simp
    _ = ∑ w ∈ exactDepthPrefixGoodCells N m L Delta,
        ∫ x in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N B k h F x
            ∂uniform01Measure := by
      simp only [exactDepthPrefixGoodCells, Finset.sum_filter, f]

/-- Finite combinatorial domination used on the denominator-bad event.
Any family of `r`-tuples taking values in a finite depth set and satisfying
all `r` one-depth events injects into the full Cartesian power of the
active depth set. -/
theorem sum_orderedEventIndicators_le_finiteEventCount_pow
    {Ω : Type*} {r : ℕ}
    (s : Finset ℕ) (E : ℕ → Set Ω)
    (tuples : Finset (Fin r → ℕ))
    (hbound : ∀ t ∈ tuples, ∀ j, t j ∈ s)
    (x : Ω) :
    (∑ t ∈ tuples,
        (orderedEventIntersection (List.ofFn fun j ↦ E (t j))).indicator
          (fun _x ↦ (1 : ℝ)) x) ≤
      (finiteEventCount s E x : ℝ) ^ r := by
  classical
  let active : Finset ℕ := s.filter fun n ↦ x ∈ E n
  let selected : Finset (Fin r → ℕ) :=
    tuples.filter fun t ↦ ∀ j, t j ∈ active
  let encode : (↥selected) → (Fin r → ↥active) := fun t j ↦
    ⟨t.1 j, (Finset.mem_filter.mp t.2).2 j⟩
  have hencode : Function.Injective encode := by
    intro t u htu
    apply Subtype.ext
    funext j
    exact congrArg (fun f ↦ (f j).1) htu
  have hcard :
      selected.card ≤ active.card ^ r := by
    calc
      selected.card = Fintype.card (↥selected) := by simp
      _ ≤ Fintype.card (Fin r → ↥active) :=
        Fintype.card_le_of_injective encode hencode
      _ = active.card ^ r := by simp
  have hcount :
      finiteEventCount s E x = active.card := by
    unfold finiteEventCount
    dsimp only [active]
    rw [Finset.card_filter]
  have hselectedEq :
      tuples.filter (fun t ↦ ∀ j, x ∈ E (t j)) = selected := by
    ext t
    simp only [selected, active, Finset.mem_filter]
    constructor
    · rintro ⟨ht, hall⟩
      exact ⟨ht, fun j ↦ ⟨hbound t ht j, hall j⟩⟩
    · rintro ⟨ht, hall⟩
      exact ⟨ht, fun j ↦ (hall j).2⟩
  calc
    (∑ t ∈ tuples,
        (orderedEventIntersection (List.ofFn fun j ↦ E (t j))).indicator
          (fun _x ↦ (1 : ℝ)) x) =
        (selected.card : ℝ) := by
      have hsum :
          (∑ t ∈ tuples,
              (orderedEventIntersection
                (List.ofFn fun j ↦ E (t j))).indicator
                (fun _x ↦ (1 : ℝ)) x) =
            ((tuples.filter (fun t ↦ ∀ j, x ∈ E (t j))).card : ℝ) := by
        simp only [Set.indicator,
          mem_orderedEventIntersection_ofFn_iff,
          Finset.sum_boole]
      rw [hsum, hselectedEq]
    _ ≤ (active.card : ℝ) ^ r := by exact_mod_cast hcard
    _ = (finiteEventCount s E x : ℝ) ^ r := by rw [hcount]

/-- The modulus of a mixed Fourier character is exactly the indicator of
its underlying simultaneous marked event. -/
theorem norm_gaussPrefixMarkedMixedTupleCharacter_eq_indicator
    {N : ℕ} {B : ι → Set (ℝ × ℝ × ℝ)}
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) (x : ℝ) :
    ‖gaussPrefixMarkedMixedTupleCharacter N B k h F x‖ =
      (mixedTupleEvent (fun i ↦ gaussPrefixMarkedEvent N (B i)) F).indicator
        (fun _x ↦ (1 : ℝ)) x := by
  classical
  by_cases hall :
      ∀ i j, x ∈ gaussPrefixMarkedEvent N (B i) (F i j)
  · have hmixed :
        x ∈ mixedTupleEvent
          (fun i ↦ gaussPrefixMarkedEvent N (B i)) F := by
      exact Set.mem_iInter.mpr fun i ↦
        Set.mem_iInter.mpr (hall i)
    rw [Set.indicator_of_mem hmixed]
    unfold gaussPrefixMarkedMixedTupleCharacter
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro i _hi
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro j _hj
    rw [norm_gaussPrefixMarkedDepthCharacter, if_pos (hall i j)]
  · have hmixed :
        x ∉ mixedTupleEvent
          (fun i ↦ gaussPrefixMarkedEvent N (B i)) F := by
      simpa only [mixedTupleEvent, tupleEvent, Set.mem_iInter] using! hall
    rw [Set.indicator_of_notMem hmixed]
    push_neg at hall
    obtain ⟨i, j, hj⟩ := hall
    unfold gaussPrefixMarkedMixedTupleCharacter
    rw [norm_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [norm_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [norm_gaussPrefixMarkedDepthCharacter, if_neg hj]

/-- A sharpened summed-cylinder estimate for cells whose ambient type is
cut off at `N` but whose actual terminal denominators are at most `R`.
This is the form needed after selecting the prefix-good cells. -/
theorem
    norm_sum_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_prefixGoodCells_sharp
    (N R : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {L m gap : ℕ} {Delta A : ℝ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (lower upper : ι → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (cells : Finset (ExactDepthBoundedPositiveWord N m))
    (hGoodCell : ∀ w ∈ cells,
      w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta)
    (hterminal :
      ∀ w ∈ cells, cfTerminalDenominator w.1.1 ≤ R) :
    ‖∑ w ∈ cells,
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤
      ((2 * (R + 1) ^ 2 : ℕ) : ℝ) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp
            (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Delta * (L : ℝ)))) := by
  let cellBound : ℝ :=
    2 / (Real.pi * (N : ℝ) *
      Real.exp
        (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
          Delta * (L : ℝ)))
  have hcellBound : 0 ≤ cellBound := by
    dsimp only [cellBound]
    positivity
  have hOne (w : ExactDepthBoundedPositiveWord N m) (hw : w ∈ cells) :
      ‖∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤ cellBound := by
    simpa only [cellBound] using!
      norm_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_prefixGoodWord
        N hN k h F hF w (hGoodCell w hw) z₀ hcoeff hgap
          hweightBudget lower upper hlower hupper hsmall
  have hcard : cells.card ≤ 2 * (R + 1) ^ 2 :=
    card_exactDepthCells_le_of_terminalDenominator_le cells hterminal
  calc
    ‖∑ w ∈ cells,
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤
        ∑ w ∈ cells,
          ‖∫ y in exactDepthBoundedCylinder w,
            gaussPrefixMarkedMixedTupleCharacter N
              (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
              k h F y ∂uniform01Measure‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _w ∈ cells, cellBound := by
      exact Finset.sum_le_sum fun w hw ↦ hOne w hw
    _ = (cells.card : ℝ) * cellBound := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 * (R + 1) ^ 2 : ℕ) : ℝ) * cellBound := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hcellBound
    _ = ((2 * (R + 1) ^ 2 : ℕ) : ℝ) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp
            (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Delta * (L : ℝ)))) := rfl

/-! ## An explicit exponential cylinder envelope -/

/-- The harmless natural ceiling in the terminal cutoff costs at most a
factor nine after squaring. -/
theorem natCeil_exp_add_one_sq_le
    {x : ℝ} (hx : 0 ≤ x) :
    (((⌈Real.exp x⌉₊ + 1) ^ 2 : ℕ) : ℝ) ≤
      9 * Real.exp (2 * x) := by
  have hexpOne : 1 ≤ Real.exp x := by
    simpa only [Real.exp_zero] using! Real.exp_le_exp.mpr hx
  have hceil :
      (⌈Real.exp x⌉₊ : ℝ) < Real.exp x + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos x).le
  have hlinear :
      ((⌈Real.exp x⌉₊ : ℝ) + 1) ≤ 3 * Real.exp x := by
    linarith
  have hnonneg : 0 ≤ ((⌈Real.exp x⌉₊ : ℝ) + 1) := by positivity
  have hsquare :=
    pow_le_pow_left₀ hnonneg hlinear 2
  push_cast
  calc
    ((⌈Real.exp x⌉₊ : ℝ) + 1) ^ 2 ≤
        (3 * Real.exp x) ^ 2 := hsquare
    _ = 9 * Real.exp (2 * x) := by
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring

/-- Convenient real envelope for the complete prefix-good cylinder sum
attached to one tuple. -/
def lowerRetainedEarlyCylinderEnvelope
    (N L m center : ℕ) (Delta : ℝ) : ℝ :=
  (36 / Real.pi) *
    Real.exp
      (2 * (m : ℝ) * gaussRoofMean -
        (center : ℝ) * gaussRoofMean -
        Real.log (N : ℝ) + 3 * Delta * (L : ℝ))

/-- The sharpened prefix-good cylinder estimate in a ceiling-free
exponential form. -/
theorem
    norm_sum_exactDepthPrefixGoodCells_mixedTupleCharacter_le_envelope
    (N : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {L m gap : ℕ} {Delta A : ℝ}
    (hDelta : 0 ≤ Delta)
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (lower upper : ι → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ‖∑ w ∈ exactDepthPrefixGoodCells N m L Delta,
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤
      lowerRetainedEarlyCylinderEnvelope
        N L m (F z₀.1 z₀.2 : ℕ) Delta := by
  let x : ℝ :=
    (m : ℝ) * gaussRoofMean + Delta * (L : ℝ)
  let R : ℕ := ⌈Real.exp x⌉₊
  have hx : 0 ≤ x := by
    dsimp only [x]
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg m) gaussRoofMean_pos.le)
      (mul_nonneg hDelta (Nat.cast_nonneg L))
  have hraw :=
    norm_sum_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_prefixGoodCells_sharp
      N R hN k h F hF z₀ hcoeff hgap hweightBudget
      lower upper hlower hupper hsmall
      (exactDepthPrefixGoodCells N m L Delta)
      (fun w hw ↦ mem_exactDepthPrefixGoodCells_iff.mp hw)
      (fun w hw ↦ by
        have hupperWord :=
          (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
            w.toPositive
            (mem_exactDepthPrefixGoodCells_iff.mp hw)
            (show m ≤ m by rfl)).2
        have htake : w.toPositive.1.take m = w.toPositive.1 := by
          calc
            w.toPositive.1.take m =
                w.toPositive.1.take w.toPositive.1.length :=
              congrArg (fun q ↦ w.toPositive.1.take q)
                w.toPositive.2.1.symm
            _ = w.toPositive.1 := List.take_length
        have hupperWord' :
            (cfTerminalDenominator w.1.1 : ℝ) ≤ Real.exp x := by
          simpa only [positiveDigitWordTake_val, htake, x] using!
            hupperWord
        have hcast :
            (cfTerminalDenominator w.1.1 : ℝ) ≤ (R : ℝ) :=
          hupperWord'.trans (by
            dsimp only [R]
            exact Nat.le_ceil _)
        exact_mod_cast hcast)
  have hsq :
      (((R + 1) ^ 2 : ℕ) : ℝ) ≤ 9 * Real.exp (2 * x) := by
    simpa only [R] using! natCeil_exp_add_one_sq_le hx
  have hNreal : (0 : ℝ) < (N : ℝ) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hden :
      0 < Real.pi * (N : ℝ) *
        Real.exp
          (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
            Delta * (L : ℝ)) := by positivity
  have hcastSq :
      ((2 * (R + 1) ^ 2 : ℕ) : ℝ) ≤
        2 * (9 * Real.exp (2 * x)) := by
    push_cast
    have hsq' :
        ((R : ℝ) + 1) ^ 2 ≤ 9 * Real.exp (2 * x) := by
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using! hsq
    exact mul_le_mul_of_nonneg_left hsq' (by norm_num)
  calc
    ‖∑ w ∈ exactDepthPrefixGoodCells N m L Delta,
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤
      ((2 * (R + 1) ^ 2 : ℕ) : ℝ) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp
            (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Delta * (L : ℝ)))) := hraw
    _ ≤
      (2 * (9 * Real.exp (2 * x))) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp
            (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Delta * (L : ℝ)))) := by
      exact mul_le_mul_of_nonneg_right hcastSq (by positivity)
    _ = lowerRetainedEarlyCylinderEnvelope
        N L m (F z₀.1 z₀.2 : ℕ) Delta := by
      unfold lowerRetainedEarlyCylinderEnvelope
      rw [show
        2 * (m : ℝ) * gaussRoofMean -
              ((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Real.log (N : ℝ) + 3 * Delta * (L : ℝ) =
            2 * x -
              (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
                Delta * (L : ℝ)) -
              Real.log (N : ℝ) by
        dsimp only [x]
        ring]
      rw [Real.exp_sub, Real.exp_sub, Real.exp_log hNreal]
      field_simp [ne_of_gt hpi]
      rw [show
        2 * x -
              (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
                Delta * (L : ℝ)) =
            2 * x +
              (Delta * (L : ℝ) -
                ((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean) by
        ring]
      rw [Real.exp_add, Real.exp_sub]
      field_simp
      ring

/-! ## Uniform decay of the lower-retained cylinder envelope -/

/-- A fixed denominator tolerance small enough for both possible early
margins. -/
def lowerRetainedDenominatorTolerance (eta rho : ℝ) : ℝ :=
  gaussRoofMean * min eta rho / 6

theorem lowerRetainedDenominatorTolerance_pos
    {eta rho : ℝ} (heta : 0 < eta) (hrho : 0 < rho) :
    0 < lowerRetainedDenominatorTolerance eta rho := by
  unfold lowerRetainedDenominatorTolerance
  exact div_pos
    (mul_pos gaussRoofMean_pos (lt_min heta hrho))
    (by norm_num)

/-- Exponent supplied by the lower side of the moving midpoint band. -/
def lowerRetainedMidpointExponent
    (rho Delta : ℝ) (N : ℕ) : ℝ :=
  (annularDepthAmbientSize N : ℝ) * gaussRoofMean -
    (annularMidpointBandWidth rho N : ℝ) * gaussRoofMean -
    Real.log (N : ℝ) +
    3 * Delta * (annularDepthAmbientSize N : ℝ)

/-- Exponent supplied by the fixed contraction at the time-one endpoint. -/
def lowerRetainedTimeOneExponent
    (eta Delta : ℝ) (N : ℕ) : ℝ :=
  -eta * Real.log (N : ℝ) +
    3 * Delta * (annularDepthAmbientSize N : ℝ)

/-- The uniform exponent valid in both last-nonzero/deepest alternatives. -/
def lowerRetainedUniformExponent
    (eta rho Delta : ℝ) (N : ℕ) : ℝ :=
  max
    (lowerRetainedMidpointExponent rho Delta N)
    (lowerRetainedTimeOneExponent eta Delta N)

theorem tendsto_lowerRetainedMidpointExponent_div_log
    {eta rho : ℝ} (hrho : 0 ≤ rho) :
    Tendsto
      (fun N : ℕ ↦
        lowerRetainedMidpointExponent rho
            (lowerRetainedDenominatorTolerance eta rho) N /
          Real.log (N : ℝ))
      atTop
      (nhds (-rho + min eta rho / 2)) := by
  let Delta := lowerRetainedDenominatorTolerance eta rho
  have hH := tendsto_annularDepthAmbientSize_div_log
  have hW := tendsto_annularMidpointBandWidth_div_log hrho
  have hcalc :=
    (((hH.mul_const gaussRoofMean).sub
      (hW.mul_const gaussRoofMean)).sub
      (tendsto_const_nhds :
        Tendsto (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1))).add
      (hH.const_mul (3 * Delta))
  have hcalc' :
      Tendsto
        (fun N : ℕ ↦
          ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)) * gaussRoofMean -
            ((annularMidpointBandWidth rho N : ℝ) /
              Real.log (N : ℝ)) * gaussRoofMean -
            1 +
            (3 * Delta) *
              ((annularDepthAmbientSize N : ℝ) /
                Real.log (N : ℝ)))
        atTop
        (nhds (-rho + min eta rho / 2)) := by
    have hlimit :
        1 / gaussRoofMean * gaussRoofMean -
              rho / gaussRoofMean * gaussRoofMean -
              1 +
              3 * (gaussRoofMean * min eta rho / 6) *
                (1 / gaussRoofMean) =
            -rho + min eta rho / 2 := by
      field_simp [ne_of_gt gaussRoofMean_pos]
      ring
    rw [← hlimit]
    simpa only [Delta, lowerRetainedDenominatorTolerance] using! hcalc
  apply hcalc'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  unfold lowerRetainedMidpointExponent
  field_simp [ne_of_gt hlog]
  ring

theorem tendsto_lowerRetainedTimeOneExponent_div_log
    (eta rho : ℝ) :
    Tendsto
      (fun N : ℕ ↦
        lowerRetainedTimeOneExponent eta
            (lowerRetainedDenominatorTolerance eta rho) N /
          Real.log (N : ℝ))
      atTop
      (nhds (-eta + min eta rho / 2)) := by
  let Delta := lowerRetainedDenominatorTolerance eta rho
  have hH := tendsto_annularDepthAmbientSize_div_log
  have hcalc :=
    (tendsto_const_nhds :
      Tendsto (fun _N : ℕ ↦ -eta) atTop (nhds (-eta))).add
      (hH.const_mul (3 * Delta))
  have hcalc' :
      Tendsto
        (fun N : ℕ ↦
          -eta +
            (3 * Delta) *
              ((annularDepthAmbientSize N : ℝ) /
                Real.log (N : ℝ)))
        atTop
        (nhds (-eta + min eta rho / 2)) := by
    have hlimit :
        -eta +
              3 * (gaussRoofMean * min eta rho / 6) *
                (1 / gaussRoofMean) =
            -eta + min eta rho / 2 := by
      field_simp [ne_of_gt gaussRoofMean_pos]
      ring
    rw [← hlimit]
    simpa only [Delta, lowerRetainedDenominatorTolerance] using! hcalc
  apply hcalc'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  unfold lowerRetainedTimeOneExponent
  field_simp [ne_of_gt hlog]
  ring

/-- Both deterministic exponents are eventually bounded by the same
strictly negative multiple of `log N`. -/
theorem eventually_lowerRetainedUniformExponent_le_neg_log
    {eta rho : ℝ} (heta : 0 < eta) (hrho : 0 < rho) :
    ∀ᶠ N : ℕ in atTop,
      lowerRetainedUniformExponent eta rho
          (lowerRetainedDenominatorTolerance eta rho) N ≤
        -(min eta rho / 4) * Real.log (N : ℝ) := by
  have hmin : 0 < min eta rho := lt_min heta hrho
  have hmidLimit :
      -rho + min eta rho / 2 < -(min eta rho / 4) := by
    have hle := min_le_right eta rho
    linarith
  have honeLimit :
      -eta + min eta rho / 2 < -(min eta rho / 4) := by
    have hle := min_le_left eta rho
    linarith
  have hmid :=
    (tendsto_lowerRetainedMidpointExponent_div_log
      (eta := eta) hrho.le).eventually_lt_const hmidLimit
  have hone :=
    (tendsto_lowerRetainedTimeOneExponent_div_log eta rho).eventually_lt_const
      honeLimit
  filter_upwards
    [hmid, hone,
      tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hmidN honeN hlog
  have hmidMul :=
    mul_le_mul_of_nonneg_right hmidN.le hlog.le
  have honeMul :=
    mul_le_mul_of_nonneg_right honeN.le hlog.le
  unfold lowerRetainedUniformExponent
  apply max_le
  · have hrewrite :
        lowerRetainedMidpointExponent rho
              (lowerRetainedDenominatorTolerance eta rho) N =
            (lowerRetainedMidpointExponent rho
                (lowerRetainedDenominatorTolerance eta rho) N /
              Real.log (N : ℝ)) *
              Real.log (N : ℝ) := by
        field_simp [ne_of_gt hlog]
    rw [hrewrite]
    exact hmidMul
  · have hrewrite :
        lowerRetainedTimeOneExponent eta
              (lowerRetainedDenominatorTolerance eta rho) N =
            (lowerRetainedTimeOneExponent eta
                (lowerRetainedDenominatorTolerance eta rho) N /
              Real.log (N : ℝ)) *
              Real.log (N : ℝ) := by
        field_simp [ne_of_gt hlog]
    rw [hrewrite]
    exact honeMul

/-- A fixed nonnegative polynomial is eventually dominated by every
positive exponential.  This local copy keeps the lower-retained leaf
independent of the unrelated near-resonance parameter module. -/
theorem lowerRetained_eventually_const_mul_pow_le_exp
    (C : ℝ) (r : ℕ) (b : ℝ) (hC : 0 ≤ C) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, C * x ^ r ≤ Real.exp (b * x) := by
  have hlittle :=
    (isLittleO_pow_exp_pos_mul_atTop r hb).const_mul_left C
  have hbound := hlittle.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hleft : 0 ≤ C * x ^ r :=
    mul_nonneg hC (pow_nonneg hx0 r)
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft,
    abs_of_pos (Real.exp_pos _), one_mul] using! hx

/-- Any fixed polynomial number of contracted lower-retained tuples is
absorbed by the uniform exponential cylinder margin.  In particular, this
is the scalar convergence needed after summing the one-tuple cylinder
estimate over all chronological tags and tuples. -/
theorem
    tendsto_const_mul_annularDepth_pow_mul_exp_lowerRetainedUniform_zero
    (C : ℝ) (r : ℕ) (hC : 0 ≤ C)
    {eta rho : ℝ} (heta : 0 < eta) (hrho : 0 < rho) :
    Tendsto
      (fun N : ℕ ↦
        C * (annularDepthAmbientSize N : ℝ) ^ r *
          Real.exp
            (lowerRetainedUniformExponent eta rho
              (lowerRetainedDenominatorTolerance eta rho) N))
      atTop (nhds 0) := by
  let c : ℝ := min eta rho / 4
  let b : ℝ := c / 2
  let D : ℝ := 1 / gaussRoofMean + 1
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (lt_min heta hrho) (by norm_num)
  have hb : 0 < b := half_pos hc
  have hD : 0 < D := by
    dsimp only [D]
    exact add_pos (one_div_pos.mpr gaussRoofMean_pos) zero_lt_one
  have hratio :
      ∀ᶠ N : ℕ in atTop,
        (annularDepthAmbientSize N : ℝ) /
            Real.log (N : ℝ) < D := by
    apply
      tendsto_annularDepthAmbientSize_div_log.eventually_lt_const
    dsimp only [D]
    linarith
  have hdepth :
      ∀ᶠ N : ℕ in atTop,
        (annularDepthAmbientSize N : ℝ) ≤
          D * Real.log (N : ℝ) := by
    filter_upwards
      [hratio,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N hratioN hlog
    have hmul :=
      mul_le_mul_of_nonneg_right hratioN.le hlog.le
    calc
      (annularDepthAmbientSize N : ℝ) =
          ((annularDepthAmbientSize N : ℝ) /
            Real.log (N : ℝ)) * Real.log (N : ℝ) := by
              field_simp [ne_of_gt hlog]
      _ ≤ D * Real.log (N : ℝ) := hmul
  have hpolyReal :
      ∀ᶠ x : ℝ in atTop,
        (C * D ^ r) * x ^ r ≤ Real.exp (b * x) :=
    lowerRetained_eventually_const_mul_pow_le_exp
      (C * D ^ r) r b
      (mul_nonneg hC (pow_nonneg hD.le r)) hb
  have hpoly :
      ∀ᶠ N : ℕ in atTop,
        (C * D ^ r) * Real.log (N : ℝ) ^ r ≤
          Real.exp (b * Real.log (N : ℝ)) :=
    tendsto_log_natCast_atTop.eventually hpolyReal
  have hexponent :=
    eventually_lowerRetainedUniformExponent_le_neg_log heta hrho
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        C * (annularDepthAmbientSize N : ℝ) ^ r *
            Real.exp
              (lowerRetainedUniformExponent eta rho
                (lowerRetainedDenominatorTolerance eta rho) N) ≤
          Real.exp (-b * Real.log (N : ℝ)) := by
    filter_upwards
      [hdepth, hpoly, hexponent,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N hdepthN hpolyN hexponentN hlog
    have hdepthPow :
        (annularDepthAmbientSize N : ℝ) ^ r ≤
          (D * Real.log (N : ℝ)) ^ r :=
      pow_le_pow_left₀ (by positivity) hdepthN r
    have hcount :
        C * (annularDepthAmbientSize N : ℝ) ^ r ≤
          (C * D ^ r) * Real.log (N : ℝ) ^ r := by
      calc
        C * (annularDepthAmbientSize N : ℝ) ^ r ≤
            C * (D * Real.log (N : ℝ)) ^ r :=
          mul_le_mul_of_nonneg_left hdepthPow hC
        _ = (C * D ^ r) * Real.log (N : ℝ) ^ r := by
          rw [mul_pow]
          ring
    have hexp :
        Real.exp
            (lowerRetainedUniformExponent eta rho
              (lowerRetainedDenominatorTolerance eta rho) N) ≤
          Real.exp (-c * Real.log (N : ℝ)) :=
      Real.exp_le_exp.mpr (by simpa only [c] using! hexponentN)
    calc
      C * (annularDepthAmbientSize N : ℝ) ^ r *
          Real.exp
            (lowerRetainedUniformExponent eta rho
              (lowerRetainedDenominatorTolerance eta rho) N) ≤
          ((C * D ^ r) * Real.log (N : ℝ) ^ r) *
            Real.exp (-c * Real.log (N : ℝ)) :=
        mul_le_mul hcount hexp (Real.exp_pos _).le
          (mul_nonneg
            (mul_nonneg hC (pow_nonneg hD.le r))
            (pow_nonneg hlog.le r))
      _ ≤
          Real.exp (b * Real.log (N : ℝ)) *
            Real.exp (-c * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hpolyN (Real.exp_pos _).le
      _ = Real.exp (-b * Real.log (N : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [b]
        ring
  have hlinear :
      Tendsto (fun N : ℕ ↦ b * Real.log (N : ℝ)) atTop atTop :=
    tendsto_log_natCast_atTop.const_mul_atTop hb
  have hzero :
      Tendsto (fun N : ℕ ↦ Real.exp (-b * Real.log (N : ℝ)))
        atTop (nhds 0) := by
    have h :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
    convert! h using 1
    funext N
    dsimp only [Function.comp_apply]
    congr 1
    ring
  exact squeeze_zero'
    (Eventually.of_forall fun N ↦ by positivity) hupper hzero

/-! ## Uniform one-tuple cancellation on prefix-good cylinders -/

set_option maxHeartbeats 800000 in
/-- A contracted lower-retained chronological tuple, realized as a
globally injective labeled depth tuple, has its entire prefix-good
deepest-cylinder sum bounded by the uniform lower-retained exponent.

Every hypothesis used by the oscillatory estimate is exposed: the
chronological realization, the fixed Fourier-weight budget, the compact
value bounds, and the small-window condition.  In particular, the proof
does not choose a tuple-dependent carrier implicitly: it uses exactly the
last nonzero chronological index. -/
theorem
    norm_sum_contractedLowerRetained_prefixGoodCells_le_uniformExponent
    {eta rho A : ℝ} {N grid : ℕ}
    (heta : 0 < eta) (hrho : 0 < rho)
    (hN : 2 ≤ N) (hgrid : 0 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    {k : AnnularGridIndex grid → ℕ}
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e mode hmode)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (htimes : fixedOrderMixedTimes N k e F = t)
    (hweightBudget :
      2 * (∑ z : GaussPrefixMixedOccurrence k,
        |(unflattenedAnnularFourierMode e mode
          z.1 z.2 : ℝ)|) ≤
        ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ))
    (lower upper : AnnularGridIndex grid → ℝ)
    (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2) :
    ‖∑ w ∈ exactDepthPrefixGoodCells N
          (t (annularDeepestIndex hr))
          (annularDepthAmbientSize N)
          (lowerRetainedDenominatorTolerance eta rho),
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k (unflattenedAnnularFourierMode e mode) F.1 y
            ∂uniform01Measure‖ ≤
      (36 / Real.pi) *
        Real.exp
          (lowerRetainedUniformExponent eta rho
            (lowerRetainedDenominatorTolerance eta rho) N) := by
  let s := annularLastNonzeroIndex mode hmode
  let d := annularDeepestIndex hr
  let z₀ : GaussPrefixMixedOccurrence k := e s
  let Delta := lowerRetainedDenominatorTolerance eta rho
  have hchronological :
      IsChronologicalNatTuple t :=
    contractedAnnularCanonicalLaterLowerMidpointTupleFamily_chronological
      k hr e mode hmode t ht
  have hFdepth :
      ∀ i j, (F.1 i j : ℕ) ≤ t d := by
    intro i j
    let q : Fin (MixedOccurrenceCount k) :=
      e.symm (⟨i, j⟩ : GaussPrefixMixedOccurrence k)
    have hq :=
      chronological_le_deepest hr hchronological q
    calc
      (F.1 i j : ℕ) =
          fixedOrderMixedTimes N k e F q := by
        dsimp only [fixedOrderMixedTimes, q]
        rw [e.apply_symm_apply]
      _ = t q := congrFun htimes q
      _ ≤ t d := hq
  have hcoeff :
      unflattenedAnnularFourierMode e mode z₀.1 z₀.2 ≠ 0 := by
    dsimp only [z₀, unflattenedAnnularFourierMode]
    simpa only [e.symm_apply_apply, s] using!
      annularLastNonzeroIndex_ne_zero mode hmode
  have hlowerMem :=
    (mem_contractedAnnularCanonicalLaterLowerMidpointTupleFamily_iff.mp
      ht).1
  have hinterior :=
    (mem_laterLowerMidpointNatTupleFamily_iff.mp hlowerMem).1
  have hlate :=
    (mem_lateFirstNatTupleFamily_iff.mp hinterior).1
  have hsep :
      IsSeparatedNatTuple (annularSeparationGap N) t :=
    (mem_separatedNatTupleFamily_iff.mp hlate).2
  have hgap :
      ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
        unflattenedAnnularFourierMode e mode z.1 z.2 ≠ 0 →
          (F.1 z.1 z.2 : ℕ) + annularSeparationGap N ≤
            (F.1 z₀.1 z₀.2 : ℕ) := by
    intro z hz hzMode
    let j : Fin (MixedOccurrenceCount k) := e.symm z
    have hjNe : j ≠ s := by
      intro hjs
      apply hz
      dsimp only [z₀]
      calc
        z = e j := (e.apply_symm_apply z).symm
        _ = e s := congrArg e hjs
    have hjMode : mode j ≠ 0 := by
      simpa only [unflattenedAnnularFourierMode, j] using! hzMode
    have hjGap :=
      gap_before_annularLastNonzeroIndex
        mode hmode t hsep j hjNe hjMode
    have hjTime :
        (F.1 z.1 z.2 : ℕ) = t j := by
      calc
        (F.1 z.1 z.2 : ℕ) =
            fixedOrderMixedTimes N k e F j := by
          dsimp only [fixedOrderMixedTimes, j]
          rw [e.apply_symm_apply]
        _ = t j := congrFun htimes j
    have hsTime :
        (F.1 z₀.1 z₀.2 : ℕ) = t s := by
      dsimp only [z₀, fixedOrderMixedTimes] at *
      simpa only using! congrFun htimes s
    simpa only [hjTime, hsTime, s] using! hjGap
  have hcenter :
      (F.1 z₀.1 z₀.2 : ℕ) = t s := by
    dsimp only [z₀, fixedOrderMixedTimes] at *
    simpa only using! congrFun htimes s
  have hraw :=
    norm_sum_exactDepthPrefixGoodCells_mixedTupleCharacter_le_envelope
      N hN k (unflattenedAnnularFourierMode e mode) F.1
      (L := annularDepthAmbientSize N)
      (m := t d)
      (gap := annularSeparationGap N)
      (Delta := Delta)
      (A := A)
      (lowerRetainedDenominatorTolerance_pos heta hrho).le
      hFdepth z₀ hcoeff hgap (by
        calc
          _ ≤ 2 * ∑ z : GaussPrefixMixedOccurrence k,
                |(unflattenedAnnularFourierMode e mode
                  z.1 z.2 : ℝ)| := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Finset.sum_le_univ_sum_of_nonneg
              (fun z ↦ abs_nonneg
                (unflattenedAnnularFourierMode e mode
                  z.1 z.2 : ℝ))
          _ ≤ ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) :=
            hweightBudget)
      lower upper hlower hupper hsmall
  have hmargin :=
    contractedLower_midpoint_or_timeOne_margin
      hgrid hlog hr htime e mode hmode ht
  have hexponent :
      2 * (t d : ℝ) * gaussRoofMean -
            (t s : ℝ) * gaussRoofMean -
            Real.log (N : ℝ) +
            3 * Delta * (annularDepthAmbientSize N : ℝ) ≤
        lowerRetainedUniformExponent eta rho Delta N := by
    rcases hmargin with hmid | hone
    · have hnat := hmid.2
      have hnatReal :
          2 * (t d : ℝ) +
              (annularMidpointBandWidth rho N : ℝ) ≤
            (annularDepthAmbientSize N : ℝ) + (t s : ℝ) := by
        exact_mod_cast hnat
      have hmu :=
        mul_le_mul_of_nonneg_right hnatReal gaussRoofMean_pos.le
      apply le_trans ?_ (le_max_left _ _)
      unfold lowerRetainedMidpointExponent
      nlinarith
    · have hsd := hone.1
      have hsd' : s = d := by
        simpa only [s, d] using! hsd
      have hceil := hone.2
      have hmReal :
          (t d : ℝ) <
            (1 - eta) * Real.log (N : ℝ) / gaussRoofMean := by
        exact Nat.lt_ceil.mp (by
          simpa only [gaussLogDepthEndpoint] using! hceil)
      have hmMu :
          (t d : ℝ) * gaussRoofMean <
            (1 - eta) * Real.log (N : ℝ) :=
        (lt_div_iff₀ gaussRoofMean_pos).mp hmReal
      apply le_trans ?_ (le_max_right _ _)
      unfold lowerRetainedTimeOneExponent
      rw [hsd']
      nlinarith
  calc
    ‖∑ w ∈ exactDepthPrefixGoodCells N (t d)
          (annularDepthAmbientSize N) Delta,
        ∫ y in exactDepthBoundedCylinder w,
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k (unflattenedAnnularFourierMode e mode) F.1 y
            ∂uniform01Measure‖ ≤
        lowerRetainedEarlyCylinderEnvelope N
          (annularDepthAmbientSize N) (t d)
          (F.1 z₀.1 z₀.2 : ℕ) Delta := hraw
    _ =
        (36 / Real.pi) *
          Real.exp
            (2 * (t d : ℝ) * gaussRoofMean -
              (t s : ℝ) * gaussRoofMean -
              Real.log (N : ℝ) +
              3 * Delta * (annularDepthAmbientSize N : ℝ)) := by
      unfold lowerRetainedEarlyCylinderEnvelope
      rw [hcenter]
    _ ≤
        (36 / Real.pi) *
          Real.exp (lowerRetainedUniformExponent eta rho Delta N) := by
      apply mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexponent)
      positivity

/-! ## The contracted prefix-good aggregate -/

/-- Harmless values for inactive grid cells make the compact-value
endpoints uniformly bounded on the whole grid-index type.  Active
occurrences retain the literal annular endpoints. -/
def activeAnnularOccurrenceSignedLower
    {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (ε A : ℝ) (i : AnnularGridIndex grid) : ℝ :=
  if 0 < k i then annularOccurrenceSignedLower ε A i else 0

def activeAnnularOccurrenceSignedUpper
    {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (ε A : ℝ) (i : AnnularGridIndex grid) : ℝ :=
  if 0 < k i then annularOccurrenceSignedUpper ε A i else 0

@[simp] theorem activeAnnularOccurrenceSignedLower_of_pos
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    {ε A : ℝ} {i : AnnularGridIndex grid} (hi : 0 < k i) :
    activeAnnularOccurrenceSignedLower k ε A i =
      annularOccurrenceSignedLower ε A i := by
  simp [activeAnnularOccurrenceSignedLower, hi]

@[simp] theorem activeAnnularOccurrenceSignedUpper_of_pos
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    {ε A : ℝ} {i : AnnularGridIndex grid} (hi : 0 < k i) :
    activeAnnularOccurrenceSignedUpper k ε A i =
      annularOccurrenceSignedUpper ε A i := by
  simp [activeAnnularOccurrenceSignedUpper, hi]

theorem abs_activeAnnularOccurrenceSignedLower_le
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (i : AnnularGridIndex grid) :
    |activeAnnularOccurrenceSignedLower k ε A i| ≤ A := by
  by_cases hi : 0 < k i
  · rw [activeAnnularOccurrenceSignedLower_of_pos hi]
    exact abs_annularOccurrenceSignedLower_le
      hε hεA hgrid i (hsigned i hi)
  · rw [activeAnnularOccurrenceSignedLower]
    simp only [if_neg hi, abs_zero]
    exact hε.le.trans hεA.le

theorem abs_activeAnnularOccurrenceSignedUpper_le
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (i : AnnularGridIndex grid) :
    |activeAnnularOccurrenceSignedUpper k ε A i| ≤ A := by
  by_cases hi : 0 < k i
  · rw [activeAnnularOccurrenceSignedUpper_of_pos hi]
    exact abs_annularOccurrenceSignedUpper_le
      hε hεA hgrid i (hsigned i hi)
  · rw [activeAnnularOccurrenceSignedUpper]
    simp only [if_neg hi, abs_zero]
    exact hε.le.trans hεA.le

/-- Inactive endpoint sanitization does not change a mixed character:
every actual occurrence lies in an active grid cell. -/
theorem gaussPrefixMarkedMixedTupleCharacter_activeAnnular_eq
    {ε A : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) (x : ℝ) :
    gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A i)
          (activeAnnularOccurrenceSignedUpper k ε A i))
        k h F x =
      gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ compactValueMarkedRegion
          (annularOccurrenceSignedLower ε A i)
          (annularOccurrenceSignedUpper ε A i))
        k h F x := by
  unfold gaussPrefixMarkedMixedTupleCharacter
  apply Finset.prod_congr rfl
  intro i _hi
  by_cases hactive : 0 < k i
  · simp only [activeAnnularOccurrenceSignedLower,
      activeAnnularOccurrenceSignedUpper, if_pos hactive]
  · have hk : k i = 0 := Nat.eq_zero_of_not_pos hactive
    let : IsEmpty (Fin (k i)) :=
      ⟨fun j ↦ Fin.elim0 (hk ▸ j)⟩
    simp

theorem flattenedAnnular_oriented_lower_ge_epsilon
    {ε A : ℝ} (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) :
    ε ≤
      gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) j := by
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have hidx : (e j).1.signed.1 + 1 ≤ grid :=
    Nat.succ_le_iff.mpr (hsigned (e j).1 hactive)
  have hlowerIcc :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA (e j).1.sign).le
      hgrid (Nat.le_of_lt (hsigned (e j).1 hactive))
  have hupperIcc :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA (e j).1.sign).le
      hgrid hidx
  cases hs : (e j).1.sign
  · rw [flattenedAnnular_oriented_lower_of_sign_false
      ε A e j hs]
    unfold flattenedAnnularSignedUpper
    simp [signedGridLower, signedGridUpper, hs] at hupperIcc ⊢
    linarith
  · rw [flattenedAnnular_oriented_lower_of_sign_true
      ε A e j hs]
    unfold flattenedAnnularSignedLower
    simp [signedGridLower, signedGridUpper, hs] at hlowerIcc ⊢
    linarith

/-- A chronological tag together with one contracted lower-retained
tuple. -/
def AnnularContractedLowerRetainedTaggedTuple
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :=
  Σ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    ↥(contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))

instance annularContractedLowerRetainedTaggedTupleFintype
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Fintype
      (AnnularContractedLowerRetainedTaggedTuple
        eta rho N k hr mode hmode) := by
  unfold AnnularContractedLowerRetainedTaggedTuple
  infer_instance

instance annularContractedLowerRetainedTaggedTupleDecidableEq
    (eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    DecidableEq
      (AnnularContractedLowerRetainedTaggedTuple
        eta rho N k hr mode hmode) :=
  Classical.decEq _

def annularContractedLowerRetainedTimes
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    Fin (MixedOccurrenceCount k) → ℕ :=
  p.2.1

theorem annularContractedLowerRetainedTimes_mem_canonical
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedLowerRetainedTimes p ∈
      canonicalAnnularGridTupleFamily N k p.1 :=
  contractedAnnularCanonicalLaterLowerMidpointTupleFamily_subset_canonical
    k hr p.1 (mode p.1) (hmode p.1) p.2.2

theorem annularContractedLowerRetainedTimes_parity
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode)
    (j : Fin (MixedOccurrenceCount k)) :
    annularContractedLowerRetainedTimes p j % 2 =
      (flattenedAnnularParity p.1 j).1 := by
  have hcanonical :=
    annularContractedLowerRetainedTimes_mem_canonical p
  rcases mem_canonicalMixedOrderParityBoxTimes_iff.mp hcanonical with
    ⟨F, _horder, hboxes, htimes⟩
  have hj := (hboxes j).2
  rw [htimes] at hj
  exact hj

/-- Every signed annular tuple event in the tagged family is contained in
the homogeneous positive approximation window `[ε,A]` at each selected
depth. -/
theorem annularContractedLowerRetained_signedEvent_subset_windowEvent
    {ε A eta rho : ℝ} (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    gaussSignedApproximationTupleEvent
        (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1)
        (annularContractedLowerRetainedTimes p) ⊆
      orderedEventIntersection
        (List.ofFn fun j ↦
          gaussApproximationWindow (Real.log (N : ℝ))
            (annularContractedLowerRetainedTimes p j) ε A) := by
  intro x hx
  have hallSigned :=
    mem_orderedEventIntersection_ofFn_iff.mp hx
  apply mem_orderedEventIntersection_ofFn_iff.mpr
  intro j
  have hj := hallSigned j
  rw [gaussSignedApproximationWindow_eq_oriented] at hj
  have hlowerEq :
      gaussParityOrientedLower
          (annularContractedLowerRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) =
        gaussPrescribedParityOrientedLower
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1) j := by
    apply gaussParityOrientedLower_eq_of_mod_two_eq
    rw [Nat.mod_eq_of_lt
      (flattenedAnnularParity p.1 j).isLt]
    exact annularContractedLowerRetainedTimes_parity p j
  have hupperEq :
      gaussParityOrientedUpper
          (annularContractedLowerRetainedTimes p j)
          (flattenedAnnularSignedLower ε A p.1 j)
          (flattenedAnnularSignedUpper ε A p.1 j) =
        gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity p.1)
          (flattenedAnnularSignedLower ε A p.1)
          (flattenedAnnularSignedUpper ε A p.1) j := by
    apply gaussParityOrientedUpper_eq_of_mod_two_eq
    rw [Nat.mod_eq_of_lt
      (flattenedAnnularParity p.1 j).isLt]
    exact annularContractedLowerRetainedTimes_parity p j
  rw [hlowerEq, hupperEq] at hj
  rcases hj with ⟨hxUnit, hjValue⟩
  refine ⟨hxUnit, ?_⟩
  exact ⟨
    (flattenedAnnular_oriented_lower_ge_epsilon
      hεA hgrid hsigned p.1 j).trans hjValue.1,
    hjValue.2.trans
      (flattenedAnnular_oriented_upper_le
        hεA hgrid hsigned p.1 j)⟩

theorem exists_annularContractedLowerRetainedRealization
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    ∃ F : GloballyInjectiveMixedDepthTuple N k,
      canonicalMixedOccurrenceOrder N k F = p.1 ∧
        fixedOrderMixedTimes N k p.1 F =
          annularContractedLowerRetainedTimes p := by
  rcases mem_canonicalMixedOrderParityBoxTimes_iff.mp
      (annularContractedLowerRetainedTimes_mem_canonical p) with
    ⟨F, horder, _hboxes, htimes⟩
  exact ⟨F, horder, htimes⟩

def annularContractedLowerRetainedRealization
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    GloballyInjectiveMixedDepthTuple N k :=
  Classical.choose (exists_annularContractedLowerRetainedRealization p)

theorem annularContractedLowerRetainedRealization_times
    {eta rho : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    fixedOrderMixedTimes N k p.1
        (annularContractedLowerRetainedRealization p) =
      annularContractedLowerRetainedTimes p :=
  (Classical.choose_spec
    (exists_annularContractedLowerRetainedRealization p)).2

theorem
    annularContractedLowerRetained_mixedEvent_subset_windowEvent_of_mem_Ioc
    {ε A eta rho : ℝ} (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    {hr : 0 < MixedOccurrenceCount k}
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    {mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ}
    {hmode : ∀ e, mode e ≠ 0}
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode)
    {x : ℝ} (hxIoc : x ∈ Ioc (0 : ℝ) 1)
    (hxMixed :
      x ∈ mixedTupleEvent
        (fun i ↦ gaussPrefixMarkedEvent N
          (compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i)))
        (annularContractedLowerRetainedRealization p).1) :
    x ∈ orderedEventIntersection
      (List.ofFn fun j ↦
        gaussApproximationWindow (Real.log (N : ℝ))
          (annularContractedLowerRetainedTimes p j) ε A) := by
  apply
    annularContractedLowerRetained_signedEvent_subset_windowEvent
      hεA hgrid hsigned p
  apply mem_orderedEventIntersection_ofFn_iff.mpr
  intro j
  let z : GaussPrefixMixedOccurrence k := p.1 j
  have hevent :
      x ∈ gaussPrefixMarkedEvent N
        (compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A z.1)
          (activeAnnularOccurrenceSignedUpper k ε A z.1))
        ((annularContractedLowerRetainedRealization p).1 z.1 z.2) := by
    exact Set.mem_iInter.mp
      (Set.mem_iInter.mp hxMixed z.1) z.2
  have hdata := selectedGaussPrefixWord_data_of_mem hevent
  have hactive : 0 < k z.1 := by
    have hz := z.2.isLt
    omega
  have htime :
      ((annularContractedLowerRetainedRealization p).1 z.1 z.2 : ℕ) =
        annularContractedLowerRetainedTimes p j := by
    have hj :=
      congrFun (annularContractedLowerRetainedRealization_times p) j
    simpa only [fixedOrderMixedTimes, z] using! hj
  rw [← htime]
  refine ⟨hxIoc, ?_⟩
  change
    gaussSignedScaledApproximationCoordinate
        (Real.log (N : ℝ))
        ((annularContractedLowerRetainedRealization p).1
          z.1 z.2 : ℕ) x ∈
      Icc (flattenedAnnularSignedLower ε A p.1 j)
        (flattenedAnnularSignedUpper ε A p.1 j)
  have hv := hdata.2.2.2.2.1
  change
    (gaussPrefixMarkedPoint N
      ((annularContractedLowerRetainedRealization p).1
        z.1 z.2 : ℕ)
      (selectedGaussPrefixWord
        ((annularContractedLowerRetainedRealization p).1
          z.1 z.2 : ℕ) x) x).2.1 ∈
      Icc (activeAnnularOccurrenceSignedLower k ε A z.1)
        (activeAnnularOccurrenceSignedUpper k ε A z.1) at hv
  rw [activeAnnularOccurrenceSignedLower_of_pos hactive,
    activeAnnularOccurrenceSignedUpper_of_pos hactive] at hv
  simpa only [z,
    gaussPrefixMarkedPoint_value_eq_signedScaledApproximation] using! hv

/-- The exact prefix-good cylinder contribution selected for one tagged
contracted lower tuple. -/
def annularContractedLowerRetainedPrefixGoodCylinderContribution
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∑ w ∈ exactDepthPrefixGoodCells N
      (annularContractedLowerRetainedTimes p
        (annularDeepestIndex hr))
      (annularDepthAmbientSize N)
      (lowerRetainedDenominatorTolerance eta rho),
    ∫ y in exactDepthBoundedCylinder w,
      gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A i)
          (activeAnnularOccurrenceSignedUpper k ε A i))
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedLowerRetainedRealization p).1 y
        ∂uniform01Measure

/-- Sum of all prefix-good cylinder contributions in the contracted lower
family. -/
def annularContractedLowerRetainedPrefixGoodCylinderSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedLowerRetainedPrefixGoodCylinderContribution
      ε A eta rho N k hr mode hmode p

set_option maxHeartbeats 400000 in
/-- The homogeneous-window bound for one fixed ordering of the labelled
occurrences.  Keeping this estimate separate prevents the dependent sum over
all orderings from obscuring the elementary finite-set injection. -/
theorem sum_contractedLowerRetained_windowIndicators_for_order_le
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : Fin (MixedOccurrenceCount k) → ℤ)
    (hh : h ≠ 0)
    (hN : 1 < N) (x : ℝ) :
    (∑ p ∈
        contractedAnnularCanonicalLaterLowerMidpointTupleFamily
          eta rho N k hr e h hh,
      (orderedEventIntersection
        (List.ofFn fun j ↦
          gaussApproximationWindow (Real.log (N : ℝ)) (p j) ε A)).indicator
        (fun _x ↦ (1 : ℝ)) x) ≤
      (gaussApproximationWindowCount
        (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
        MixedOccurrenceCount k := by
  classical
  unfold gaussApproximationWindowCount
  exact sum_orderedEventIndicators_le_finiteEventCount_pow
    (Finset.range (annularDepthAmbientSize N))
    (fun n ↦ gaussApproximationWindow
      (Real.log (N : ℝ)) n ε A)
    (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e h hh)
    (fun t ht j ↦ Finset.mem_range.mpr
      (canonicalAnnularGridTupleFamily_lt_ambient
        hgrid k htime hN e t
        (contractedAnnularCanonicalLaterLowerMidpointTupleFamily_subset_canonical
          k hr e h hh ht) j))
    x

/-- Pointwise homogeneous-window domination after summing all contracted
lower tuples, written as a nested sum over the finitely many labelled
orders.  This form avoids an expensive dependent-`Sigma` normalization. -/
theorem sum_annularContractedLowerRetained_windowIndicators_le
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 1 < N) (x : ℝ) :
    (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
      ∑ p ∈
          contractedAnnularCanonicalLaterLowerMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e),
        (orderedEventIntersection
          (List.ofFn fun j ↦
            gaussApproximationWindow (Real.log (N : ℝ))
              (p j) ε A)).indicator
          (fun _x ↦ (1 : ℝ)) x) ≤
      (Fintype.card
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) : ℝ) *
        (gaussApproximationWindowCount
          (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
          MixedOccurrenceCount k := by
  classical
  have hsum :
      (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∑ p ∈
          contractedAnnularCanonicalLaterLowerMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e),
          (orderedEventIntersection
            (List.ofFn fun j ↦
              gaussApproximationWindow (Real.log (N : ℝ))
                (p j) ε A)).indicator
            (fun _x ↦ (1 : ℝ)) x) ≤
      ∑ _e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        (gaussApproximationWindowCount
          (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
          MixedOccurrenceCount k := by
    apply Finset.sum_le_sum
    intro e _he
    exact sum_contractedLowerRetained_windowIndicators_for_order_le
      hgrid k hr htime e (mode e) (hmode e) hN x
  calc
    _ ≤ ∑ _e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      (gaussApproximationWindowCount
        (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
        MixedOccurrenceCount k := hsum
    _ = _ := by simp

theorem card_annularContractedLowerRetainedTaggedTuple_le
    {eta rho : ℝ} {N grid : ℕ}
    (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hN : 1 < N) :
    Fintype.card
        (AnnularContractedLowerRetainedTaggedTuple
          eta rho N k hr mode hmode) ≤
      Fintype.card
          (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k) *
        annularDepthAmbientSize N ^ MixedOccurrenceCount k := by
  calc
    Fintype.card
        (AnnularContractedLowerRetainedTaggedTuple
          eta rho N k hr mode hmode) =
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e)).card := by
      simp [AnnularContractedLowerRetainedTaggedTuple]
    _ ≤ ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          (canonicalAnnularGridTupleFamily N k e).card := by
      apply Finset.sum_le_sum
      intro e _he
      exact Finset.card_le_card
        (contractedAnnularCanonicalLaterLowerMidpointTupleFamily_subset_canonical
          k hr e (mode e) (hmode e))
    _ = aggregateTupleFamilyCard
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) := rfl
    _ ≤ _ :=
      aggregate_canonicalAnnularGridTupleFamily_card_le
        hgrid k htime hN

/-- The full Fourier weight of every tag is eventually absorbed by the
common square-root separation gap. -/
theorem eventually_annularContractedLowerRetained_fullWeightBudget
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        2 * (∑ z : GaussPrefixMixedOccurrence k,
          |(unflattenedAnnularFourierMode e (mode e)
            z.1 z.2 : ℝ)|) ≤
          ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) := by
  have hgapHalf :
      Tendsto (fun N ↦ annularSeparationGap N / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num)).comp
      tendsto_annularSeparationGap_atTop
  have hpowNat :
      Tendsto (fun N ↦ 2 ^ (annularSeparationGap N / 2))
        atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℕ) < 2 by norm_num)).comp hgapHalf
  have hpowReal :
      Tendsto
        (fun N ↦ ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  let M : ℝ :=
    2 * ∑ e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      ∑ z : GaussPrefixMixedOccurrence k,
        |(unflattenedAnnularFourierMode e (mode e)
          z.1 z.2 : ℝ)|
  filter_upwards [hpowReal.eventually_ge_atTop M] with N hN
  intro e
  calc
    2 * (∑ z : GaussPrefixMixedOccurrence k,
        |(unflattenedAnnularFourierMode e (mode e)
          z.1 z.2 : ℝ)|) ≤ M := by
      dsimp only [M]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.single_le_sum
        (fun (e' : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k) _he ↦
          Finset.sum_nonneg fun
            (z : GaussPrefixMixedOccurrence k) _hz ↦
          abs_nonneg
            (unflattenedAnnularFourierMode e' (mode e')
              z.1 z.2 : ℝ))
        (Finset.mem_univ e)
    _ ≤ ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) := hN

set_option maxHeartbeats 800000 in
/-- After summing over every chronological tag and contracted lower tuple,
the complete prefix-good cylinder surrogate tends to zero. -/
theorem
    tendsto_annularContractedLowerRetainedPrefixGoodCylinderSum_zero
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedLowerRetainedPrefixGoodCylinderSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let C : ℝ :=
    (Fintype.card
      (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k) : ℝ) * (36 / Real.pi)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hmajorant :=
    tendsto_const_mul_annularDepth_pow_mul_exp_lowerRetainedUniform_zero
      C (MixedOccurrenceCount k) hC heta hrho
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A / Real.log (N : ℝ) < (1 : ℝ) / 2 := by
    have hlogTwoA :
        ∀ᶠ N : ℕ in atTop,
          2 * A < Real.log (N : ℝ) :=
      tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)
    filter_upwards
      [hlogTwoA,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N htwoA hlog
    exact (div_lt_iff₀ hlog).2 (by linarith)
  have hweights :=
    eventually_annularContractedLowerRetained_fullWeightBudget mode
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        ‖annularContractedLowerRetainedPrefixGoodCylinderSum
            ε A eta rho N k hr mode hmode‖ ≤
          C * (annularDepthAmbientSize N : ℝ) ^
              MixedOccurrenceCount k *
            Real.exp
              (lowerRetainedUniformExponent eta rho
                (lowerRetainedDenominatorTolerance eta rho) N) := by
    filter_upwards
      [eventually_ge_atTop 2,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0,
        hsmall, hweights] with N hN hlog hsmallN hweightsN
    let K : ℝ :=
      (36 / Real.pi) *
        Real.exp
          (lowerRetainedUniformExponent eta rho
            (lowerRetainedDenominatorTolerance eta rho) N)
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hcardNat :=
      card_annularContractedLowerRetainedTaggedTuple_le
        (eta := eta) (rho := rho)
        hgrid k hr htime mode hmode hN
    have hcardReal :
        (Fintype.card
          (AnnularContractedLowerRetainedTaggedTuple
            eta rho N k hr mode hmode) : ℝ) ≤
          (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
            (annularDepthAmbientSize N : ℝ) ^
              MixedOccurrenceCount k := by
      exact_mod_cast hcardNat
    unfold annularContractedLowerRetainedPrefixGoodCylinderSum
    calc
      ‖∑ p : AnnularContractedLowerRetainedTaggedTuple
            eta rho N k hr mode hmode,
          annularContractedLowerRetainedPrefixGoodCylinderContribution
            ε A eta rho N k hr mode hmode p‖ ≤
          ∑ p : AnnularContractedLowerRetainedTaggedTuple
              eta rho N k hr mode hmode,
            ‖annularContractedLowerRetainedPrefixGoodCylinderContribution
              ε A eta rho N k hr mode hmode p‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _p : AnnularContractedLowerRetainedTaggedTuple
              eta rho N k hr mode hmode, K := by
        apply Finset.sum_le_sum
        intro p _hp
        unfold
          annularContractedLowerRetainedPrefixGoodCylinderContribution
        simpa only [K] using!
          norm_sum_contractedLowerRetained_prefixGoodCells_le_uniformExponent
            heta hrho hN hgrid hlog hr htime
            p.1 (mode p.1) (hmode p.1)
            (annularContractedLowerRetainedTimes p) p.2.2
            (annularContractedLowerRetainedRealization p)
            (annularContractedLowerRetainedRealization_times p)
            (hweightsN p.1)
            (activeAnnularOccurrenceSignedLower k ε A)
            (activeAnnularOccurrenceSignedUpper k ε A)
            (abs_activeAnnularOccurrenceSignedLower_le
              hε hεA hgrid hsigned)
            (abs_activeAnnularOccurrenceSignedUpper_le
              hε hεA hgrid hsigned)
            hsmallN
      _ =
          (Fintype.card
            (AnnularContractedLowerRetainedTaggedTuple
              eta rho N k hr mode hmode) : ℝ) * K := by
        simp
      _ ≤
          ((Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
            (annularDepthAmbientSize N : ℝ) ^
              MixedOccurrenceCount k) * K :=
        mul_le_mul_of_nonneg_right hcardReal hK
      _ =
          C * (annularDepthAmbientSize N : ℝ) ^
              MixedOccurrenceCount k *
            Real.exp
              (lowerRetainedUniformExponent eta rho
                (lowerRetainedDenominatorTolerance eta rho) N) := by
        dsimp only [C, K]
        ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _) hupper hmajorant

/-! ## Returning from the cylinder surrogate to the moving statistic -/

/-- The actual moving Fourier contribution of one tagged contracted
lower-retained tuple. -/
def annularContractedLowerRetainedMovingContribution
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) : ℂ :=
  ∫ x, gaussMovingSignedMarkedTupleIntegrand
    N (Real.log (N : ℝ))
    (flattenedAnnularSignedLower ε A p.1)
    (flattenedAnnularSignedUpper ε A p.1)
    (mode p.1)
    (annularContractedLowerRetainedTimes p) x
    ∂uniform01Measure

/-- The actual contracted lower-retained Fourier aggregate, indexed by the
same tagged type as the prefix-cylinder surrogate. -/
def annularContractedLowerRetainedMovingSum
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode,
    annularContractedLowerRetainedMovingContribution
      ε A eta rho N k hr mode hmode p

/-- The cylinder contribution is literally the mixed character restricted
to the prefix denominator-good event.  Positivity of the separation gap
ensures that the deepest selected depth is nonzero, as required by the
finite exact-depth cylinder partition. -/
theorem
    annularContractedLowerRetainedPrefixGoodCylinderContribution_eq_setIntegral
    {ε A eta rho : ℝ} {N grid : ℕ}
    (hgap : 0 < annularSeparationGap N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    annularContractedLowerRetainedPrefixGoodCylinderContribution
        ε A eta rho N k hr mode hmode p =
      ∫ x in gaussDenominatorPrefixGoodEvent
          (annularContractedLowerRetainedTimes p
            (annularDeepestIndex hr))
          (annularDepthAmbientSize N)
          (lowerRetainedDenominatorTolerance eta rho),
        gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i))
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedLowerRetainedRealization p).1 x
          ∂uniform01Measure := by
  let d := annularDeepestIndex hr
  let t := annularContractedLowerRetainedTimes p
  let F := annularContractedLowerRetainedRealization p
  have htMem := p.2.2
  have hlower :=
    (mem_contractedAnnularCanonicalLaterLowerMidpointTupleFamily_iff.mp
      htMem).1
  have hinterior :=
    (mem_laterLowerMidpointNatTupleFamily_iff.mp hlower).1
  have hlate :=
    (mem_lateFirstNatTupleFamily_iff.mp hinterior).1
  have hfirst :
      annularSeparationGap N ≤ t ⟨0, hr⟩ :=
    (mem_lateFirstNatTupleFamily_iff.mp hinterior).2
  have hchronological : IsChronologicalNatTuple t :=
    contractedAnnularCanonicalLaterLowerMidpointTupleFamily_chronological
      k hr p.1 (mode p.1) (hmode p.1) t htMem
  have hfirstDeepest :
      t ⟨0, hr⟩ ≤ t d :=
    chronological_le_deepest hr hchronological ⟨0, hr⟩
  have hdeepPos : 0 < t d :=
    hgap.trans_le (hfirst.trans hfirstDeepest)
  let z : GaussPrefixMixedOccurrence k := p.1 d
  have hdepth :
      (F.1 z.1 z.2 : ℕ) = t d := by
    have htimes :=
      congrFun (annularContractedLowerRetainedRealization_times p) d
    simpa only [fixedOrderMixedTimes, F, t, z] using! htimes
  unfold annularContractedLowerRetainedPrefixGoodCylinderContribution
  symm
  exact
    setIntegral_gaussPrefixMarkedMixedTupleCharacter_prefixGoodEvent_eq_sum
      N
      (fun i ↦
        measurableSet_compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A i)
          (activeAnnularOccurrenceSignedUpper k ε A i))
      k
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      F.1 z.1 z.2
      (by simpa only [t, d] using! hdepth)
      (by simpa only [t, d] using! hdeepPos)

/-- On the global denominator-good event, the moving tuple integrand is
the prefix-good mixed character used by the exact cylinder surrogate.
Both the inclusion into the tuple-dependent prefix event and the
continued-fraction bridge are asserted almost everywhere, so rational
endpoints and terminating expansions are not silently discarded. -/
theorem
    ae_annularContractedLowerRetained_moving_eq_prefixIndicator_on_globalGood
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      lowerRetainedDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ))
    (p : AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode) :
    ∀ᵐ x ∂uniform01Measure,
      x ∈ gaussDenominatorLinearGoodEvent 1
          (annularDepthAmbientSize N)
          (lowerRetainedDenominatorTolerance eta rho) →
        gaussMovingSignedMarkedTupleIntegrand
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A p.1)
            (flattenedAnnularSignedUpper ε A p.1)
            (mode p.1)
            (annularContractedLowerRetainedTimes p) x =
          (gaussDenominatorPrefixGoodEvent
            (annularContractedLowerRetainedTimes p
              (annularDeepestIndex hr))
            (annularDepthAmbientSize N)
            (lowerRetainedDenominatorTolerance eta rho)).indicator
            (gaussPrefixMarkedMixedTupleCharacter N
              (fun i ↦ compactValueMarkedRegion
                (activeAnnularOccurrenceSignedLower k ε A i)
                (activeAnnularOccurrenceSignedUpper k ε A i))
              k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedLowerRetainedRealization p).1) x := by
  have hcanonical :=
    annularContractedLowerRetainedTimes_mem_canonical p
  have hdeepLt :
      annularContractedLowerRetainedTimes p
          (annularDeepestIndex hr) <
        annularDepthAmbientSize N :=
    canonicalAnnularGridTupleFamily_lt_ambient
      hgrid k htime (by omega) p.1
      (annularContractedLowerRetainedTimes p) hcanonical
      (annularDeepestIndex hr)
  have hprefix :
      gaussDenominatorLinearGoodEvent 1
          (annularDepthAmbientSize N)
          (lowerRetainedDenominatorTolerance eta rho)
        ≤ᵐ[uniform01Measure]
      gaussDenominatorPrefixGoodEvent
          (annularContractedLowerRetainedTimes p
            (annularDeepestIndex hr))
          (annularDepthAmbientSize N)
          (lowerRetainedDenominatorTolerance eta rho) := by
    apply gaussDenominatorLinearGoodEvent_ae_subset_prefixGoodEvent
    simpa only [one_mul] using! hdeepLt.le
  filter_upwards [ae_nonterminating_uniform01, hprefix] with
      x hxNonterm hxPrefix hxGood
  have hxPrefixGood :
      x ∈ gaussDenominatorPrefixGoodEvent
          (annularContractedLowerRetainedTimes p
            (annularDeepestIndex hr))
          (annularDepthAmbientSize N)
          (lowerRetainedDenominatorTolerance eta rho) :=
    hxPrefix hxGood
  have hbound :
      ∀ j,
        fixedOrderMixedTimes N k p.1
            (annularContractedLowerRetainedRealization p) j ≤
          1 * annularDepthAmbientSize N := by
    intro j
    rw [annularContractedLowerRetainedRealization_times p]
    simpa only [one_mul] using!
      (canonicalAnnularGridTupleFamily_lt_ambient
        hgrid k htime (by omega) p.1
        (annularContractedLowerRetainedTimes p) hcanonical j).le
  have hboxes :
      ∀ j,
        fixedOrderMixedTimes N k p.1
            (annularContractedLowerRetainedRealization p) j ∈
          contractedAnnularTimeDepthBox N eta (p.1 j).1 := by
    intro j
    rw [annularContractedLowerRetainedRealization_times p]
    exact
      contractedAnnularCanonicalLaterLowerMidpointTupleFamily_boxes
        p.2.2 j
  have hbridge :=
    gaussMovingAnnularMarkedTupleIntegrand_eq_mixedCharacter_of_good_contracted
      hε hεA hgrid hN k p.1
      (unflattenedAnnularFourierMode p.1 (mode p.1))
      (annularContractedLowerRetainedRealization p)
      htime hsigned hsmall hxNonterm.1 hxNonterm.2 hxGood
      hbound hmargin hboxes
  rw [flattenedAnnularFourierMode_unflattened,
    annularContractedLowerRetainedRealization_times p] at hbridge
  calc
    gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A p.1)
        (flattenedAnnularSignedUpper ε A p.1)
        (mode p.1)
        (annularContractedLowerRetainedTimes p) x =
      gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A i)
          (activeAnnularOccurrenceSignedUpper k ε A i))
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedLowerRetainedRealization p).1 x :=
      hbridge.trans
        (gaussPrefixMarkedMixedTupleCharacter_activeAnnular_eq
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedLowerRetainedRealization p).1 x).symm
    _ =
      (gaussDenominatorPrefixGoodEvent
        (annularContractedLowerRetainedTimes p
          (annularDeepestIndex hr))
        (annularDepthAmbientSize N)
        (lowerRetainedDenominatorTolerance eta rho)).indicator
        (gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion
            (activeAnnularOccurrenceSignedLower k ε A i)
            (activeAnnularOccurrenceSignedUpper k ε A i))
          k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularContractedLowerRetainedRealization p).1) x :=
      (Set.indicator_of_mem hxPrefixGood _).symm

/-- A finite-family good/bad comparison for complex integrals.  If two
integrands agree on `good` and each is bounded by the same event
indicator, then the difference of their aggregate integrals is controlled
by twice the corresponding event count on `goodᶜ`. -/
theorem norm_sum_integral_sub_le_goodCompl_indicatorSum
    {α ι : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsFiniteMeasure mu]
    (s : Finset ι) (good : Set α) (hgood : MeasurableSet good)
    (E : ι → Set α) (hE : ∀ i ∈ s, MeasurableSet (E i))
    (f g : ι → α → ℂ)
    (hf : ∀ i ∈ s, Integrable (f i) mu)
    (hg : ∀ i ∈ s, Integrable (g i) mu)
    (heq :
      ∀ᵐ x ∂mu, x ∈ good → ∀ i ∈ s, f i x = g i x)
    (hbound :
      ∀ᵐ x ∂mu, ∀ i ∈ s,
        ‖f i x‖ ≤ (E i).indicator (fun _x ↦ (1 : ℝ)) x ∧
        ‖g i x‖ ≤ (E i).indicator (fun _x ↦ (1 : ℝ)) x) :
    ‖∑ i ∈ s,
        ((∫ x, f i x ∂mu) - ∫ x, g i x ∂mu)‖ ≤
      ∫ x in goodᶜ,
        2 * ∑ i ∈ s,
          (E i).indicator (fun _x ↦ (1 : ℝ)) x ∂mu := by
  let q : α → ℂ := fun x ↦
    ∑ i ∈ s, (f i x - g i x)
  let count : α → ℝ := fun x ↦
    ∑ i ∈ s, (E i).indicator (fun _x ↦ (1 : ℝ)) x
  have hqInt : Integrable q mu := by
    dsimp only [q]
    apply integrable_finset_sum
    intro i hi
    exact (hf i hi).sub (hg i hi)
  have hcountInt : Integrable count mu := by
    dsimp only [count]
    apply integrable_finset_sum
    intro i hi
    exact (integrable_const (1 : ℝ)).indicator (hE i hi)
  have hdomInt :
      Integrable (goodᶜ.indicator (fun x ↦ 2 * count x)) mu :=
    (hcountInt.const_mul 2).indicator hgood.compl
  have hsumIntegral :
      (∑ i ∈ s,
          ((∫ x, f i x ∂mu) - ∫ x, g i x ∂mu)) =
        ∫ x, q x ∂mu := by
    calc
      (∑ i ∈ s,
          ((∫ x, f i x ∂mu) - ∫ x, g i x ∂mu)) =
          ∑ i ∈ s, ∫ x, (f i x - g i x) ∂mu := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_sub (hf i hi) (hg i hi)]
      _ = ∫ x, q x ∂mu := by
        dsimp only [q]
        rw [integral_finset_sum]
        intro i hi
        exact (hf i hi).sub (hg i hi)
  rw [hsumIntegral]
  calc
    ‖∫ x, q x ∂mu‖ ≤ ∫ x, ‖q x‖ ∂mu :=
      norm_integral_le_integral_norm q
    _ ≤ ∫ x, goodᶜ.indicator (fun y ↦ 2 * count y) x ∂mu := by
      apply integral_mono_ae hqInt.norm hdomInt
      filter_upwards [heq, hbound] with x heqx hboundx
      by_cases hx : x ∈ good
      · have hqZero : q x = 0 := by
          dsimp only [q]
          apply Finset.sum_eq_zero
          intro i hi
          rw [heqx hx i hi, sub_self]
        have hxCompl : x ∉ goodᶜ := by
          simpa only [Set.mem_compl_iff, not_not] using! hx
        rw [hqZero, norm_zero, Set.indicator_of_notMem hxCompl]
      · rw [Set.indicator_of_mem (by
          simpa only [Set.mem_compl_iff] using! hx)]
        calc
          ‖q x‖ ≤ ∑ i ∈ s, ‖f i x - g i x‖ := by
            dsimp only [q]
            exact norm_sum_le _ _
          _ ≤ ∑ i ∈ s, (‖f i x‖ + ‖g i x‖) := by
            apply Finset.sum_le_sum
            intro i hi
            exact norm_sub_le _ _
          _ ≤ ∑ i ∈ s,
              ((E i).indicator (fun _x ↦ (1 : ℝ)) x +
                (E i).indicator (fun _x ↦ (1 : ℝ)) x) := by
            apply Finset.sum_le_sum
            intro i hi
            exact add_le_add (hboundx i hi).1 (hboundx i hi).2
          _ = 2 * count x := by
            dsimp only [count]
            rw [Finset.sum_add_distrib]
            ring
    _ = ∫ x in goodᶜ, 2 * count x ∂mu := by
      rw [integral_indicator hgood.compl]
    _ = ∫ x in goodᶜ,
        2 * ∑ i ∈ s,
          (E i).indicator (fun _x ↦ (1 : ℝ)) x ∂mu := by
      rfl

/-- Reindex the tagged homogeneous-window count as the nested finite sum
over chronological labels and raw time tuples. -/
theorem sum_annularContractedLowerRetained_taggedWindowIndicators_eq_nested
    {ε A eta rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (x : ℝ) :
    (∑ p : AnnularContractedLowerRetainedTaggedTuple
        eta rho N k hr mode hmode,
      (orderedEventIntersection
        (List.ofFn fun j ↦
          gaussApproximationWindow (Real.log (N : ℝ))
            (annularContractedLowerRetainedTimes p j) ε A)).indicator
        (fun _x ↦ (1 : ℝ)) x) =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∑ t ∈
          contractedAnnularCanonicalLaterLowerMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e),
          (orderedEventIntersection
            (List.ofFn fun j ↦
              gaussApproximationWindow
                (Real.log (N : ℝ)) (t j) ε A)).indicator
            (fun _x ↦ (1 : ℝ)) x := by
  classical
  let f := fun
      (e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (p : ↥(contractedAnnularCanonicalLaterLowerMidpointTupleFamily
        eta rho N k hr e (mode e) (hmode e))) ↦
    (orderedEventIntersection
      (List.ofFn fun j ↦
        gaussApproximationWindow (Real.log (N : ℝ))
          (annularContractedLowerRetainedTimes
            (⟨e, p⟩ :
              AnnularContractedLowerRetainedTaggedTuple
                eta rho N k hr mode hmode) j) ε A)).indicator
      (fun _x ↦ (1 : ℝ)) x
  change
    (∑ p : Σ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ↥(contractedAnnularCanonicalLaterLowerMidpointTupleFamily
          eta rho N k hr e (mode e) (hmode e)),
      f p.1 p.2) = _
  rw [Fintype.sum_sigma']
  apply Finset.sum_congr rfl
  intro e _he
  rw [← Finset.attach_eq_univ
    (s := contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))]
  simp only [f, annularContractedLowerRetainedTimes]
  exact Finset.sum_attach
    (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))
    (fun t ↦
      (orderedEventIntersection
        (List.ofFn fun j ↦
          gaussApproximationWindow
            (Real.log (N : ℝ)) (t j) ε A)).indicator
        (fun _x ↦ (1 : ℝ)) x)

/-- Finite-`N` comparison between the actual contracted moving Fourier
aggregate and its exact prefix-cylinder surrogate.  The entire error is
localized to the complement of one global denominator-good event. -/
theorem
    norm_annularContractedLowerRetainedMovingSum_sub_prefixGood_le_badIntegral
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    (hgap : 0 < annularSeparationGap N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      lowerRetainedDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ)) :
    ‖annularContractedLowerRetainedMovingSum
          ε A eta rho N k hr mode hmode -
        annularContractedLowerRetainedPrefixGoodCylinderSum
          ε A eta rho N k hr mode hmode‖ ≤
      ∫ x in
          (gaussDenominatorLinearGoodEvent 1
            (annularDepthAmbientSize N)
            (lowerRetainedDenominatorTolerance eta rho))ᶜ,
        2 * ∑ p : AnnularContractedLowerRetainedTaggedTuple
            eta rho N k hr mode hmode,
          (orderedEventIntersection
            (List.ofFn fun j ↦
              gaussApproximationWindow (Real.log (N : ℝ))
                (annularContractedLowerRetainedTimes p j) ε A)).indicator
            (fun _x ↦ (1 : ℝ)) x
          ∂uniform01Measure := by
  classical
  let T :=
    AnnularContractedLowerRetainedTaggedTuple
      eta rho N k hr mode hmode
  let good : Set ℝ :=
    gaussDenominatorLinearGoodEvent 1
      (annularDepthAmbientSize N)
      (lowerRetainedDenominatorTolerance eta rho)
  let P : T → Set ℝ := fun p ↦
    gaussDenominatorPrefixGoodEvent
      (annularContractedLowerRetainedTimes p
        (annularDeepestIndex hr))
      (annularDepthAmbientSize N)
      (lowerRetainedDenominatorTolerance eta rho)
  let B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ) := fun i ↦
    compactValueMarkedRegion
      (activeAnnularOccurrenceSignedLower k ε A i)
      (activeAnnularOccurrenceSignedUpper k ε A i)
  let f : T → ℝ → ℂ := fun p x ↦
    gaussMovingSignedMarkedTupleIntegrand
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A p.1)
      (flattenedAnnularSignedUpper ε A p.1)
      (mode p.1)
      (annularContractedLowerRetainedTimes p) x
  let g : T → ℝ → ℂ := fun p ↦
    (P p).indicator
      (gaussPrefixMarkedMixedTupleCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedLowerRetainedRealization p).1)
  let E : T → Set ℝ := fun p ↦
    orderedEventIntersection
      (List.ofFn fun j ↦
        gaussApproximationWindow (Real.log (N : ℝ))
          (annularContractedLowerRetainedTimes p j) ε A)
  have hgoodMeas : MeasurableSet good := by
    exact measurableSet_gaussDenominatorLinearGoodEvent
      1 (annularDepthAmbientSize N)
        (lowerRetainedDenominatorTolerance eta rho)
  have hEMeas : ∀ p ∈ (Finset.univ : Finset T),
      MeasurableSet (E p) := by
    intro p _hp
    dsimp only [E]
    apply measurableSet_orderedEventIntersection
    intro S hS
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS
    exact measurableSet_gaussApproximationWindow _ _ _ _
  have hfInt : ∀ p ∈ (Finset.univ : Finset T),
      Integrable (f p) uniform01Measure := by
    intro p _hp
    exact integrable_gaussMovingSignedMarkedTupleIntegrand
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A p.1)
      (flattenedAnnularSignedUpper ε A p.1)
      (mode p.1)
      (annularContractedLowerRetainedTimes p)
      uniform01Measure
  have hgInt : ∀ p ∈ (Finset.univ : Finset T),
      Integrable (g p) uniform01Measure := by
    intro p _hp
    dsimp only [g]
    exact
      (integrable_gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ measurableSet_compactValueMarkedRegion
          (activeAnnularOccurrenceSignedLower k ε A i)
          (activeAnnularOccurrenceSignedUpper k ε A i))
        k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularContractedLowerRetainedRealization p).1
        uniform01Measure).indicator
          (measurableSet_gaussDenominatorPrefixGoodEvent
            (annularContractedLowerRetainedTimes p
              (annularDeepestIndex hr))
            (annularDepthAmbientSize N)
            (lowerRetainedDenominatorTolerance eta rho))
  have heq :
      ∀ᵐ x ∂uniform01Measure,
        x ∈ good →
          ∀ p ∈ (Finset.univ : Finset T), f p x = g p x := by
    have hall :
        ∀ᵐ x ∂uniform01Measure,
          ∀ p : T, x ∈ good → f p x = g p x := by
      apply Filter.eventually_all.mpr
      intro p
      simpa only [good, f, g, P, B] using!
        ae_annularContractedLowerRetained_moving_eq_prefixIndicator_on_globalGood
          hε hεA hgrid hN k hr htime hsigned mode hmode
          hsmall hmargin p
    filter_upwards [hall] with x hx hxGood
    intro p _hp
    exact hx p hxGood
  have hbound :
      ∀ᵐ x ∂uniform01Measure,
        ∀ p ∈ (Finset.univ : Finset T),
          ‖f p x‖ ≤ (E p).indicator (fun _x ↦ (1 : ℝ)) x ∧
          ‖g p x‖ ≤ (E p).indicator (fun _x ↦ (1 : ℝ)) x := by
    filter_upwards [ae_nonterminating_uniform01] with x hxUnit
    intro p _hp
    constructor
    · dsimp only [f, E]
      rw [norm_gaussMovingSignedMarkedTupleIntegrand]
      exact
        (Set.indicator_le_indicator_of_subset
          (annularContractedLowerRetained_signedEvent_subset_windowEvent
            hεA hgrid hsigned p)
          (fun _x ↦ by norm_num)) x
    · dsimp only [g]
      rw [norm_indicator_eq_indicator_norm]
      calc
        (P p).indicator
            (fun y ↦ ‖gaussPrefixMarkedMixedTupleCharacter N B k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedLowerRetainedRealization p).1 y‖) x ≤
          ‖gaussPrefixMarkedMixedTupleCharacter N B k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedLowerRetainedRealization p).1 x‖ :=
          indicator_norm_le_norm_self
            (s := P p)
            (f := gaussPrefixMarkedMixedTupleCharacter N B k
              (unflattenedAnnularFourierMode p.1 (mode p.1))
              (annularContractedLowerRetainedRealization p).1)
            (a := x)
        _ =
          (mixedTupleEvent
            (fun i ↦ gaussPrefixMarkedEvent N (B i))
            (annularContractedLowerRetainedRealization p).1).indicator
              (fun _x ↦ (1 : ℝ)) x := by
          exact norm_gaussPrefixMarkedMixedTupleCharacter_eq_indicator
            k
            (unflattenedAnnularFourierMode p.1 (mode p.1))
            (annularContractedLowerRetainedRealization p).1 x
        _ ≤ (E p).indicator (fun _x ↦ (1 : ℝ)) x := by
          by_cases hxMixed :
              x ∈ mixedTupleEvent
                (fun i ↦ gaussPrefixMarkedEvent N (B i))
                (annularContractedLowerRetainedRealization p).1
          · have hxWindow :
                x ∈ E p := by
              apply
                annularContractedLowerRetained_mixedEvent_subset_windowEvent_of_mem_Ioc
                  hεA hgrid hsigned p
              · exact ⟨hxUnit.1.1, hxUnit.1.2.le⟩
              · simpa only [B] using! hxMixed
            rw [Set.indicator_of_mem hxMixed,
              Set.indicator_of_mem hxWindow]
          · rw [Set.indicator_of_notMem hxMixed]
            exact Set.indicator_nonneg (fun _x ↦ by norm_num) x
  have hcompare :=
    norm_sum_integral_sub_le_goodCompl_indicatorSum
      uniform01Measure (Finset.univ : Finset T)
      good hgoodMeas E hEMeas f g hfInt hgInt heq hbound
  have hprefix :
      annularContractedLowerRetainedPrefixGoodCylinderSum
          ε A eta rho N k hr mode hmode =
        ∑ p : T, ∫ x, g p x ∂uniform01Measure := by
    unfold annularContractedLowerRetainedPrefixGoodCylinderSum
    apply Finset.sum_congr rfl
    intro p _hp
    rw [
      annularContractedLowerRetainedPrefixGoodCylinderContribution_eq_setIntegral
        hgap k hr mode hmode p]
    dsimp only [g, P, B]
    rw [integral_indicator
      (measurableSet_gaussDenominatorPrefixGoodEvent
        (annularContractedLowerRetainedTimes p
          (annularDeepestIndex hr))
        (annularDepthAmbientSize N)
        (lowerRetainedDenominatorTolerance eta rho))]
  unfold annularContractedLowerRetainedMovingSum
  rw [hprefix, ← Finset.sum_sub_distrib]
  simpa only [T, good, E, f, g] using! hcompare

/-- Replace the tagged bad-event integrand by the fixed power of the
homogeneous approximation-window count. -/
theorem
    norm_annularContractedLowerRetainedMovingSum_sub_prefixGood_le_badMoment
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {N grid : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    (hgap : 0 < annularSeparationGap N)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hmargin :
      lowerRetainedDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ)) :
    ‖annularContractedLowerRetainedMovingSum
          ε A eta rho N k hr mode hmode -
        annularContractedLowerRetainedPrefixGoodCylinderSum
          ε A eta rho N k hr mode hmode‖ ≤
      ∫ x in gaussDenominatorLinearBadEvent 1
          (annularDepthAmbientSize N)
          (lowerRetainedDenominatorTolerance eta rho),
        2 *
          (Fintype.card
            (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k) : ℝ) *
          (gaussApproximationWindowCount
            (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
              MixedOccurrenceCount k
          ∂uniform01Measure := by
  let bad : Set ℝ :=
    gaussDenominatorLinearBadEvent 1
      (annularDepthAmbientSize N)
      (lowerRetainedDenominatorTolerance eta rho)
  have hfirst :=
    norm_annularContractedLowerRetainedMovingSum_sub_prefixGood_le_badIntegral
      hε hεA hgrid hN hgap k hr htime hsigned mode hmode
      hsmall hmargin
  rw [← gaussDenominatorLinearBadEvent_eq_compl
    1 (annularDepthAmbientSize N)
      (lowerRetainedDenominatorTolerance eta rho)] at hfirst
  refine hfirst.trans ?_
  have hleftInt :
      Integrable
        (fun x ↦
          2 * ∑ p : AnnularContractedLowerRetainedTaggedTuple
              eta rho N k hr mode hmode,
            (orderedEventIntersection
              (List.ofFn fun j ↦
                gaussApproximationWindow (Real.log (N : ℝ))
                  (annularContractedLowerRetainedTimes p j) ε A)).indicator
              (fun _x ↦ (1 : ℝ)) x)
        (uniform01Measure.restrict bad) := by
    apply Integrable.mono_measure _ Measure.restrict_le_self
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro p _hp
    apply (integrable_const (1 : ℝ)).indicator
    apply measurableSet_orderedEventIntersection
    intro S hS
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hS
    exact measurableSet_gaussApproximationWindow _ _ _ _
  have hrightInt :
      Integrable
        (fun x ↦
          2 *
            (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
            (gaussApproximationWindowCount
              (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                MixedOccurrenceCount k)
        (uniform01Measure.restrict bad) := by
    apply Integrable.mono_measure _ Measure.restrict_le_self
    exact
      (integrable_gaussApproximationWindowCount_pow
        (Real.log (N : ℝ)) (annularDepthAmbientSize N)
        (MixedOccurrenceCount k) ε A).const_mul
          (2 *
            (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ))
  apply integral_mono hleftInt hrightInt
  intro x
  dsimp only
  rw [
    sum_annularContractedLowerRetained_taggedWindowIndicators_eq_nested
      k hr mode hmode x]
  have hpoint :=
    sum_annularContractedLowerRetained_windowIndicators_le
      (ε := ε) (A := A) (eta := eta) (rho := rho) (N := N)
      hgrid k hr htime mode hmode (by omega) x
  simpa only [mul_assoc] using!
    mul_le_mul_of_nonneg_left hpoint (by norm_num : (0 : ℝ) ≤ 2)

/-- The standard annular depth horizon is eventually bounded by a fixed
multiple of `log N`. -/
theorem exists_eventually_annularDepthAmbientSize_le_mul_log :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ N : ℕ in atTop,
        (annularDepthAmbientSize N : ℝ) ≤
          D * Real.log (N : ℝ) := by
  let ell : ℝ := 1 / gaussRoofMean
  let D : ℝ := ell + 1
  have hD : 0 ≤ D := by
    dsimp only [D, ell]
    have hone : 0 < (1 : ℝ) / gaussRoofMean :=
      div_pos (by norm_num) gaussRoofMean_pos
    linarith
  have hellD : ell < D := by
    dsimp only [D]
    linarith
  have hratio :
      ∀ᶠ N : ℕ in atTop,
        (annularDepthAmbientSize N : ℝ) /
            Real.log (N : ℝ) < D :=
    tendsto_annularDepthAmbientSize_div_log.eventually_lt_const hellD
  refine ⟨D, hD, ?_⟩
  filter_upwards
    [hratio,
      tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hratioN hlog
  exact ((div_lt_iff₀ hlog).mp hratioN).le

/-- For fixed positive contraction parameters, the chosen denominator
tolerance leaves the required time-one contraction margin eventually. -/
theorem eventually_lowerRetainedDenominatorTolerance_mul_ambient_le_margin
    {eta rho : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      lowerRetainedDenominatorTolerance eta rho *
          (annularDepthAmbientSize N : ℝ) ≤
        eta * Real.log (N : ℝ) := by
  let Delta := lowerRetainedDenominatorTolerance eta rho
  have hlimit :
      Delta * (1 / gaussRoofMean) < eta := by
    have hmin := min_le_left eta rho
    dsimp only [Delta, lowerRetainedDenominatorTolerance]
    field_simp [ne_of_gt gaussRoofMean_pos]
    nlinarith
  have hratio :
      Tendsto
        (fun N : ℕ ↦
          Delta *
            ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)))
        atTop (nhds (Delta * (1 / gaussRoofMean))) :=
    tendsto_const_nhds.mul tendsto_annularDepthAmbientSize_div_log
  have hlt := hratio.eventually_lt_const hlimit
  filter_upwards
    [hlt,
      tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hltN hlog
  have hdiv :
      Delta * (annularDepthAmbientSize N : ℝ) /
          Real.log (N : ℝ) < eta := by
    calc
      Delta * (annularDepthAmbientSize N : ℝ) /
          Real.log (N : ℝ) =
          Delta *
            ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)) := by ring
      _ < eta := hltN
  exact ((div_lt_iff₀ hlog).mp hdiv).le

/-- The actual contracted moving aggregate and the exact prefix-cylinder
surrogate have the same limit. -/
theorem
    tendsto_annularContractedLowerRetainedMovingSum_sub_prefixGood_zero
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedLowerRetainedMovingSum
            ε A eta rho N k hr mode hmode -
          annularContractedLowerRetainedPrefixGoodCylinderSum
            ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  let C : ℝ :=
    2 *
      (Fintype.card
        (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k) : ℝ)
  let moment : ℕ → ℝ := fun N ↦
    ∫ x in gaussDenominatorLinearBadEvent 1
        (annularDepthAmbientSize N)
        (lowerRetainedDenominatorTolerance eta rho),
      (gaussApproximationWindowCount
        (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
          MixedOccurrenceCount k
      ∂uniform01Measure
  have hmoment : Tendsto moment atTop (nhds 0) := by
    simpa only [moment] using!
      tendsto_gaussApproximationWindowCount_pow_on_denominatorBadEvent
        annularDepthAmbientSize annularDepthAmbientSize
        (MixedOccurrenceCount k) 1
        hr hε hεA
        exists_eventually_annularDepthAmbientSize_le_mul_log
        (by norm_num)
        (lowerRetainedDenominatorTolerance_pos heta hrho)
        tendsto_annularDepthAmbientSize_atTop
  have hmajor :
      Tendsto
        (fun N : ℕ ↦
          ∫ x in gaussDenominatorLinearBadEvent 1
              (annularDepthAmbientSize N)
              (lowerRetainedDenominatorTolerance eta rho),
            C *
              (gaussApproximationWindowCount
                (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                  MixedOccurrenceCount k
            ∂uniform01Measure)
        atTop (nhds 0) := by
    have hmul := hmoment.const_mul C
    simpa only [moment, integral_const_mul, mul_zero] using! hmul
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A / Real.log (N : ℝ) < (1 : ℝ) / 2 := by
    have hlogTwoA :
        ∀ᶠ N : ℕ in atTop,
          2 * A < Real.log (N : ℝ) :=
      tendsto_log_natCast_atTop.eventually_gt_atTop (2 * A)
    filter_upwards
      [hlogTwoA,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N htwoA hlog
    exact (div_lt_iff₀ hlog).2 (by linarith)
  have hmargin :=
    eventually_lowerRetainedDenominatorTolerance_mul_ambient_le_margin
      (rho := rho) heta
  have hgap :
      ∀ᶠ N : ℕ in atTop, 0 < annularSeparationGap N :=
    tendsto_annularSeparationGap_atTop.eventually_gt_atTop 0
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        ‖annularContractedLowerRetainedMovingSum
              ε A eta rho N k hr mode hmode -
            annularContractedLowerRetainedPrefixGoodCylinderSum
              ε A eta rho N k hr mode hmode‖ ≤
          ∫ x in gaussDenominatorLinearBadEvent 1
              (annularDepthAmbientSize N)
              (lowerRetainedDenominatorTolerance eta rho),
            C *
              (gaussApproximationWindowCount
                (Real.log (N : ℝ)) (annularDepthAmbientSize N) ε A x : ℝ) ^
                  MixedOccurrenceCount k
            ∂uniform01Measure := by
    filter_upwards [eventually_ge_atTop 2, hgap, hsmall, hmargin] with
        N hN hgapN hsmallN hmarginN
    simpa only [C, mul_assoc] using!
      norm_annularContractedLowerRetainedMovingSum_sub_prefixGood_le_badMoment
        hε hεA hgrid hN hgapN k hr htime hsigned mode hmode
        hsmallN hmarginN
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _N ↦ norm_nonneg _) hupper hmajor

/-- Fixed positive `eta` and `rho` give cancellation of the actual
contracted lower-retained moving Fourier aggregate. -/
theorem tendsto_annularContractedLowerRetainedMovingSum_zero
    {ε A eta rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (heta : 0 < eta) (hrho : 0 < rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    Tendsto
      (fun N : ℕ ↦
        annularContractedLowerRetainedMovingSum
          ε A eta rho N k hr mode hmode)
      atTop (nhds 0) := by
  have hdiff :=
    tendsto_annularContractedLowerRetainedMovingSum_sub_prefixGood_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  have hprefix :=
    tendsto_annularContractedLowerRetainedPrefixGoodCylinderSum_zero
      hε hεA heta hrho hgrid k hr htime hsigned mode hmode
  have hadd := hdiff.add hprefix
  convert! hadd using 1
  · funext N
    ring
  · ring_nf

/-- The tagged moving aggregate is exactly the paper-facing nested sum over
chronological orders and contracted lower-retained tuple families. -/
theorem annularContractedLowerRetainedMovingSum_eq_nested
    (ε A eta rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    annularContractedLowerRetainedMovingSum
        ε A eta rho N k hr mode hmode =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (mode e)
          (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
            eta rho N k hr e (mode e) (hmode e)) := by
  classical
  let f := fun
      (e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (p : ↥(contractedAnnularCanonicalLaterLowerMidpointTupleFamily
        eta rho N k hr e (mode e) (hmode e))) ↦
    ∫ x, gaussMovingSignedMarkedTupleIntegrand
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (mode e) p.1 x
      ∂uniform01Measure
  unfold annularContractedLowerRetainedMovingSum
    annularContractedLowerRetainedMovingContribution
  change
    (∑ p : Σ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ↥(contractedAnnularCanonicalLaterLowerMidpointTupleFamily
          eta rho N k hr e (mode e) (hmode e)),
      f p.1 p.2) = _
  rw [Fintype.sum_sigma']
  apply Finset.sum_congr rfl
  intro e _he
  unfold uniformMovingSignedMarkedFourierTupleSum
    movingSignedMarkedFourierTupleSum
  rw [← Finset.attach_eq_univ
    (s := contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))]
  simp only [f]
  exact Finset.sum_attach
    (contractedAnnularCanonicalLaterLowerMidpointTupleFamily
      eta rho N k hr e (mode e) (hmode e))
    (fun t ↦
      ∫ x, gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (mode e) t x
        ∂uniform01Measure)

end

end Erdos1002
