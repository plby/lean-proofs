import ErdosProblems.Erdos1002.GaussPrefixAnnularCoefficientBridge
import ErdosProblems.Erdos1002.GaussPrefixAnnularBoundaryCells
import ErdosProblems.Erdos1002.GaussPrefixAnnularTimeZeroMarkedMeasure
import ErdosProblems.Erdos1002.MarkedBadEventMomentDeletion
import ErdosProblems.Erdos1002.GaussPrefixAnnularTorusEventBridge
import ErdosProblems.Erdos1002.GaussPrefixAnnularSignedEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Literal-to-canonical transfer for annular Gauss-prefix tuples

The literal marked cells use the random logarithmic denominator
`log Q_n(x) / log N`, whereas the canonical Fourier argument uses the
deterministic depth clock `n * gaussRoofMean / log N`.  These two clocks
are not equal at finite `N`.

This file keeps that discrepancy explicit.  It introduces contracted and
expanded canonical tuple families and proves the exact pointwise sandwich
on the global denominator good event.  In particular, disagreement between
the literal time cells and the unshifted canonical boxes is supported on
the expanded-minus-contracted boundary family.  The final sections turn
that support statement into finite integral bounds and state the order of
limits used to remove the boundary and the denominator bad event.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology Real

namespace Erdos1002

noncomputable section

set_option maxHeartbeats 800000

open MultivariateFactorialMomentMethod

/-! ## Contracted, unshifted, and expanded time conditions -/

/-- The literal simultaneous denominator-time condition in one fixed
chronological occurrence order. -/
def gaussPrefixAnnularLiteralTimeCondition
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ) (x : ℝ) : Prop :=
  ∀ j,
    gaussPrefixLogDenominatorTime N (t j) x ∈
      intervalGridCell 0 1 grid (e j).1.time

/-- Simultaneous membership in the contracted deterministic time boxes. -/
def gaussPrefixAnnularContractedTimeCondition
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    (eta : ℝ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ) : Prop :=
  ∀ j, t j ∈ contractedAnnularTimeDepthBox N eta (e j).1

/-- Simultaneous membership in the unshifted deterministic time boxes. -/
def gaussPrefixAnnularCanonicalTimeCondition
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ) : Prop :=
  ∀ j, t j ∈ annularOccurrenceDepthBoxes N k (e j)

/-- Simultaneous membership in the expanded deterministic time boxes. -/
def gaussPrefixAnnularExpandedTimeCondition
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    (eta : ℝ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ) : Prop :=
  ∀ j, t j ∈ expandedAnnularTimeDepthBox N eta (e j).1

/-- A nonzero annular signed cell determines the parity of the
continued-fraction depth.  The positivity of the exact approximation
coordinate is proved on the nonterminating full-measure set; no sign
convention is inferred from a possibly zero totalized coordinate. -/
theorem depth_parity_eq_annularGridDepthParity_of_signed_mem
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid) (hi : i.signed.1 < grid)
    {N n : ℕ} {x : ℝ} (hlog : 0 < Real.log (N : ℝ))
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hsigned :
      gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x ∈
        intervalGridCell
          (signedGridLower ε A i.sign)
          (signedGridUpper ε A i.sign) grid i.signed) :
    n % 2 = (annularGridDepthParity i).1 := by
  have hdomain : x ∈ positivePrefixDomain n :=
    mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
  have hxCylinder :
      x ∈ positivePrefixCylinder n (selectedGaussPrefixWord n x) :=
    selectedGaussPrefixWord_mem hdomain
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating
      hxUnit hxNonterm (n + 1)
  have htheta :
      0 < gaussApproximationCoordinate n x :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix
      (selectedGaussPrefixWord n x) hxUnit hex hxCylinder
  have hscaled :
      0 < gaussScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x := by
    unfold gaussScaledApproximationCoordinate
    exact mul_pos hlog htheta
  unfold intervalGridCell at hsigned
  rw [if_pos hi] at hsigned
  cases hs : i.sign
  · have hupper :=
      intervalGridPoint_mem_Icc
        (signedGridLower_lt_upper hεA i.sign).le hgrid
        (show i.signed.1 + 1 ≤ grid by omega)
    have hupper' :
        intervalGridPoint (-A) (-ε) grid (i.signed.1 + 1) ∈
          Icc (-A) (-ε) := by
      simpa only [hs, signedGridLower, signedGridUpper,
        Bool.false_eq_true, if_false] using! hupper
    have hnegative :
        gaussSignedScaledApproximationCoordinate
            (Real.log (N : ℝ)) n x < 0 := by
      have hupperNeg :
          intervalGridPoint
              (signedGridLower ε A i.sign)
              (signedGridUpper ε A i.sign)
              grid (i.signed.1 + 1) < 0 := by
        have hupperNeg' :
            intervalGridPoint (-A) (-ε) grid (i.signed.1 + 1) < 0 :=
          hupper'.2.trans_lt (neg_neg_of_pos hε)
        simpa only [hs, signedGridLower, signedGridUpper,
          Bool.false_eq_true, if_false] using! hupperNeg'
      exact hsigned.2.trans hupperNeg
    have hnotEven : ¬ Even n := by
      intro heven
      have hp :
          gaussSignedScaledApproximationCoordinate
              (Real.log (N : ℝ)) n x =
            gaussScaledApproximationCoordinate
              (Real.log (N : ℝ)) n x := by
        unfold gaussSignedScaledApproximationCoordinate
        rw [heven.neg_one_pow, one_mul]
      linarith [hscaled, hnegative, hp]
    have hodd : Odd n := Nat.not_even_iff_odd.mp hnotEven
    simpa only [annularGridDepthParity, hs, if_false] using!
      (Nat.odd_iff.mp hodd)
  · have hlower :=
      intervalGridPoint_mem_Icc
        (signedGridLower_lt_upper hεA i.sign).le hgrid
        (Nat.le_of_lt hi)
    have hlower' :
        intervalGridPoint ε A grid i.signed.1 ∈ Icc ε A := by
      simpa only [hs, signedGridLower, signedGridUpper, if_true] using!
        hlower
    have hpositive :
        0 <
          gaussSignedScaledApproximationCoordinate
            (Real.log (N : ℝ)) n x := by
      have hlowerPos :
          0 <
            intervalGridPoint
              (signedGridLower ε A i.sign)
              (signedGridUpper ε A i.sign)
              grid i.signed.1 := by
        have hlowerPos' :
            0 < intervalGridPoint ε A grid i.signed.1 :=
          hε.trans_le hlower'.1
        simpa only [hs, signedGridLower, signedGridUpper, if_true] using!
          hlowerPos'
      exact hlowerPos.trans_le hsigned.1
    have heven : Even n := by
      by_contra hnotEven
      have hodd : Odd n := Nat.not_even_iff_odd.mp hnotEven
      have hp :
          gaussSignedScaledApproximationCoordinate
              (Real.log (N : ℝ)) n x =
            -gaussScaledApproximationCoordinate
              (Real.log (N : ℝ)) n x := by
        unfold gaussSignedScaledApproximationCoordinate
        rw [hodd.neg_one_pow, neg_one_mul]
      linarith [hscaled, hpositive, hp]
    simpa only [annularGridDepthParity, hs, if_true] using!
      (Nat.even_iff.mp heven)

/-- Membership in an active annular signed cell forces Legendre's
`theta < 1/2` cutoff once the logarithmic scale is large enough. -/
theorem gaussApproximationCoordinate_lt_half_of_mem_annularSignedCell
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid) (_hi : i.signed.1 < grid)
    {N n : ℕ} {x : ℝ} (hN : 2 ≤ N)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hsigned :
      gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x ∈
        intervalGridCell
          (signedGridLower ε A i.sign)
          (signedGridUpper ε A i.sign) grid i.signed) :
    gaussApproximationCoordinate n x < (1 : ℝ) / 2 := by
  let w : PositiveDigitWord n := selectedGaussPrefixWord n x
  have hdomain : x ∈ positivePrefixDomain n :=
    mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
  have hxCylinder : x ∈ positivePrefixCylinder n w :=
    selectedGaussPrefixWord_mem hdomain
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating
      hxUnit hxNonterm (n + 1)
  have htheta : 0 < gaussApproximationCoordinate n x :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix
      w hxUnit hex hxCylinder
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have habs :
      |gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x| ≤ A := by
    apply abs_le.mpr
    have hcell :=
      intervalGridCell_subset_Icc
        (signedGridLower_lt_upper hεA i.sign) hgrid i.signed hsigned
    cases hs : i.sign
    · have hcell' :
          gaussSignedScaledApproximationCoordinate
              (Real.log (N : ℝ)) n x ∈ Icc (-A) (-ε) := by
        simpa only [hs, signedGridLower, signedGridUpper,
          Bool.false_eq_true, if_false] using! hcell
      exact ⟨hcell'.1, hcell'.2.trans (by linarith)⟩
    · have hcell' :
          gaussSignedScaledApproximationCoordinate
              (Real.log (N : ℝ)) n x ∈ Icc ε A := by
        simpa only [hs, signedGridLower, signedGridUpper, if_true] using! hcell
      exact ⟨(by linarith [hcell'.1]), hcell'.2⟩
  have habsFormula :
      |gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x| =
        Real.log (N : ℝ) * gaussApproximationCoordinate n x := by
    unfold gaussSignedScaledApproximationCoordinate
      gaussScaledApproximationCoordinate
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_of_pos hlog, abs_of_pos htheta]
  have hthetaLe :
      gaussApproximationCoordinate n x ≤
        A / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlog).2
    calc
      gaussApproximationCoordinate n x * Real.log (N : ℝ) =
          Real.log (N : ℝ) * gaussApproximationCoordinate n x := mul_comm _ _
      _ = |gaussSignedScaledApproximationCoordinate
          (Real.log (N : ℝ)) n x| := habsFormula.symm
      _ ≤ A := habs
  exact hthetaLe.trans_lt hsmall

/-- Nonnegative endpoint expansion contains the unshifted depth box. -/
theorem annularOccurrenceDepthBoxes_subset_expanded
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    {eta : ℝ} (heta : 0 ≤ eta)
    (z : GaussPrefixMixedOccurrence k) :
    annularOccurrenceDepthBoxes N k z ⊆
      expandedAnnularTimeDepthBox N eta z.1 := by
  intro n hn
  unfold annularOccurrenceDepthBoxes annularTimeDepthLower
    annularTimeDepthUpper at hn
  unfold expandedAnnularTimeDepthBox
  rw [Finset.mem_Ico] at hn ⊢
  constructor
  · exact (Nat.ceil_mono (by
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · linarith
        · exact Real.log_natCast_nonneg N
      · exact gaussRoofMean_pos.le)).trans hn.1
  · exact hn.2.trans_le (Nat.ceil_mono (by
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · linarith
        · exact Real.log_natCast_nonneg N
      · exact gaussRoofMean_pos.le))

/-- Nonnegative contraction is contained in the unshifted depth box. -/
theorem contractedAnnularTimeDepthBox_subset_annularOccurrenceDepthBoxes
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    {eta : ℝ} (heta : 0 ≤ eta)
    (z : GaussPrefixMixedOccurrence k) :
    contractedAnnularTimeDepthBox N eta z.1 ⊆
      annularOccurrenceDepthBoxes N k z := by
  intro n hn
  unfold contractedAnnularTimeDepthBox at hn
  unfold annularOccurrenceDepthBoxes annularTimeDepthLower
    annularTimeDepthUpper
  rw [Finset.mem_Ico] at hn ⊢
  constructor
  · exact (Nat.ceil_mono (by
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · linarith
        · exact Real.log_natCast_nonneg N
      · exact gaussRoofMean_pos.le)).trans hn.1
  · exact hn.2.trans_le (Nat.ceil_mono (by
      apply div_le_div_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · linarith
        · exact Real.log_natCast_nonneg N
      · exact gaussRoofMean_pos.le))

theorem canonicalTimeCondition_imp_expanded
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    {eta : ℝ} (heta : 0 ≤ eta)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (hcanonical :
      gaussPrefixAnnularCanonicalTimeCondition (N := N) e t) :
    gaussPrefixAnnularExpandedTimeCondition (N := N) eta e t := by
  intro j
  exact annularOccurrenceDepthBoxes_subset_expanded heta (e j)
    (hcanonical j)

theorem contractedTimeCondition_imp_canonical
    {grid N : ℕ} {k : AnnularGridIndex grid → ℕ}
    {eta : ℝ} (heta : 0 ≤ eta)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (hcontracted :
      gaussPrefixAnnularContractedTimeCondition (N := N) eta e t) :
    gaussPrefixAnnularCanonicalTimeCondition (N := N) e t := by
  intro j
  exact
    contractedAnnularTimeDepthBox_subset_annularOccurrenceDepthBoxes
      heta (e j) (hcontracted j)

/-- The simultaneous contracted-to-literal half of the denominator-clock
sandwich, with every rounding and range hypothesis exposed. -/
theorem literalTimeCondition_of_contracted_on_good
    {N L C grid : ℕ} {Delta eta x : ℝ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (htime : ∀ i : AnnularGridIndex grid, 0 < k i → i.time.1 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hbound : ∀ j, t j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hcontracted :
      gaussPrefixAnnularContractedTimeCondition (N := N) eta e t) :
    gaussPrefixAnnularLiteralTimeCondition (N := N) e t x := by
  exact
    forall_gaussPrefixLogDenominatorTime_mem_timeCell_of_contractedBoxes
      e t htime hlog hxGood hbound hmargin hcontracted

/-- The simultaneous literal-to-expanded half of the denominator-clock
sandwich. -/
theorem expandedTimeCondition_of_literal_on_good
    {N L C grid : ℕ} {Delta eta x : ℝ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (htime : ∀ i : AnnularGridIndex grid, 0 < k i → i.time.1 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hbound : ∀ j, t j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hliteral :
      gaussPrefixAnnularLiteralTimeCondition (N := N) e t x) :
    gaussPrefixAnnularExpandedTimeCondition (N := N) eta e t := by
  exact
    forall_mem_expandedBoxes_of_gaussPrefixLogDenominatorTime_mem_timeCell
      e t htime hlog hxGood hbound hmargin hliteral

/-- On the good event, any disagreement between the literal denominator
cells and the unshifted deterministic cells is supported on the explicit
expanded-minus-contracted boundary condition. -/
theorem expanded_and_not_contracted_of_literal_xor_canonical_on_good
    {N L C grid : ℕ} {Delta eta x : ℝ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (htime : ∀ i : AnnularGridIndex grid, 0 < k i → i.time.1 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hbound : ∀ j, t j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (heta : 0 ≤ eta)
    (hxor :
      (gaussPrefixAnnularLiteralTimeCondition (N := N) e t x ∧
          ¬ gaussPrefixAnnularCanonicalTimeCondition (N := N) e t) ∨
        (gaussPrefixAnnularCanonicalTimeCondition (N := N) e t ∧
          ¬ gaussPrefixAnnularLiteralTimeCondition (N := N) e t x)) :
    gaussPrefixAnnularExpandedTimeCondition (N := N) eta e t ∧
      ¬ gaussPrefixAnnularContractedTimeCondition (N := N) eta e t := by
  rcases hxor with ⟨hliteral, hnotCanonical⟩ |
      ⟨hcanonical, hnotLiteral⟩
  · refine ⟨expandedTimeCondition_of_literal_on_good
      e t htime hlog hxGood hbound hmargin hliteral, ?_⟩
    intro hcontracted
    exact hnotCanonical
      (contractedTimeCondition_imp_canonical heta e t hcontracted)
  · refine ⟨canonicalTimeCondition_imp_expanded heta e t hcanonical, ?_⟩
    intro hcontracted
    exact hnotLiteral
      (literalTimeCondition_of_contracted_on_good
        e t htime hlog hxGood hbound hmargin hcontracted)

/-! ## Tagged contracted, expanded, and boundary tuple families -/

/-- The chronological parity-restricted family obtained from the
contracted time boxes. -/
def contractedCanonicalAnnularGridTupleFamily
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  canonicalMixedOrderParityBoxTimes N k e
    (fun z ↦ contractedAnnularTimeDepthBox N eta z.1)
    (annularOccurrenceParity k)

/-- The chronological parity-restricted family obtained from the
expanded time boxes. -/
def expandedCanonicalAnnularGridTupleFamily
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  canonicalMixedOrderParityBoxTimes N k e
    (fun z ↦ expandedAnnularTimeDepthBox N eta z.1)
    (annularOccurrenceParity k)

/-- Labeled source tuples underlying the contracted chronological family.
The separate source representation is useful when comparing directly with
the labeled mixed-factorial expansion. -/
def contractedAnnularCanonicalOrderSource
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    Finset (GloballyInjectiveMixedDepthTuple N k) :=
  (canonicalMixedOrderClass N k e).filter fun F ↦
    ∀ j,
      fixedOrderMixedTimes N k e F j ∈
          contractedAnnularTimeDepthBox N eta (e j).1 ∧
        fixedOrderMixedTimes N k e F j % 2 =
          (annularOccurrenceParity k (e j)).1

/-- Labeled source tuples underlying the expanded chronological family. -/
def expandedAnnularCanonicalOrderSource
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    Finset (GloballyInjectiveMixedDepthTuple N k) :=
  (canonicalMixedOrderClass N k e).filter fun F ↦
    ∀ j,
      fixedOrderMixedTimes N k e F j ∈
          expandedAnnularTimeDepthBox N eta (e j).1 ∧
        fixedOrderMixedTimes N k e F j % 2 =
          (annularOccurrenceParity k (e j)).1

theorem contractedCanonicalAnnularGridTupleFamily_eq_image_source
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    contractedCanonicalAnnularGridTupleFamily N eta k e =
      (contractedAnnularCanonicalOrderSource N eta k e).image
        (fixedOrderMixedTimes N k e) := by
  rfl

theorem expandedCanonicalAnnularGridTupleFamily_eq_image_source
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    expandedCanonicalAnnularGridTupleFamily N eta k e =
      (expandedAnnularCanonicalOrderSource N eta k e).image
        (fixedOrderMixedTimes N k e) := by
  rfl

theorem canonicalAnnularGridTupleFamily_eq_image_source
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    canonicalAnnularGridTupleFamily N k e =
      (annularCanonicalOrderSource N k e).image
        (fixedOrderMixedTimes N k e) := by
  rfl

/-- The explicit time-boundary family.  It is a genuine finset
difference, so all multiplicities and chronological order tags remain
visible. -/
def annularCanonicalTimeBoundaryTupleFamily
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  expandedCanonicalAnnularGridTupleFamily N eta k e \
    contractedCanonicalAnnularGridTupleFamily N eta k e

theorem contractedCanonicalAnnularGridTupleFamily_subset_canonical
    {grid N : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    contractedCanonicalAnnularGridTupleFamily N eta k e ⊆
      canonicalAnnularGridTupleFamily N k e := by
  intro t ht
  obtain ⟨F, horder, hbox, hFt⟩ :=
    mem_canonicalMixedOrderParityBoxTimes_iff.mp ht
  apply mem_canonicalMixedOrderParityBoxTimes_iff.mpr
  refine ⟨F, horder, ?_, hFt⟩
  intro j
  exact ⟨
    contractedAnnularTimeDepthBox_subset_annularOccurrenceDepthBoxes
      heta (e j) (hbox j).1,
    (hbox j).2⟩

theorem canonicalAnnularGridTupleFamily_subset_expanded
    {grid N : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    canonicalAnnularGridTupleFamily N k e ⊆
      expandedCanonicalAnnularGridTupleFamily N eta k e := by
  intro t ht
  obtain ⟨F, horder, hbox, hFt⟩ :=
    mem_canonicalMixedOrderParityBoxTimes_iff.mp ht
  apply mem_canonicalMixedOrderParityBoxTimes_iff.mpr
  refine ⟨F, horder, ?_, hFt⟩
  intro j
  exact ⟨
    annularOccurrenceDepthBoxes_subset_expanded
      heta (e j) (hbox j).1,
    (hbox j).2⟩

theorem contractedCanonicalAnnularGridTupleFamily_subset_expanded
    {grid N : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    contractedCanonicalAnnularGridTupleFamily N eta k e ⊆
      expandedCanonicalAnnularGridTupleFamily N eta k e :=
  (contractedCanonicalAnnularGridTupleFamily_subset_canonical
      heta k e).trans
    (canonicalAnnularGridTupleFamily_subset_expanded heta k e)

theorem mem_annularCanonicalTimeBoundaryTupleFamily_iff
    {grid N : ℕ} {eta : ℝ}
    {k : AnnularGridIndex grid → ℕ}
    {e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k}
    {t : Fin (MixedOccurrenceCount k) → ℕ} :
    t ∈ annularCanonicalTimeBoundaryTupleFamily N eta k e ↔
      t ∈ expandedCanonicalAnnularGridTupleFamily N eta k e ∧
        t ∉ contractedCanonicalAnnularGridTupleFamily N eta k e := by
  simp only [annularCanonicalTimeBoundaryTupleFamily, Finset.mem_sdiff]

theorem annularCanonicalTimeBoundaryTupleFamily_chronological
    {grid N : ℕ} {eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ annularCanonicalTimeBoundaryTupleFamily N eta k e) :
    IsChronologicalNatTuple t := by
  exact canonicalMixedOrderParityBoxTimes_chronological e
    (fun z ↦ expandedAnnularTimeDepthBox N eta z.1)
    (annularOccurrenceParity k) t
    (mem_annularCanonicalTimeBoundaryTupleFamily_iff.mp ht).1

theorem annularCanonicalTimeBoundaryTupleFamily_parity
    {grid N : ℕ} {eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ annularCanonicalTimeBoundaryTupleFamily N eta k e)
    (j : Fin (MixedOccurrenceCount k)) :
    t j % 2 = (flattenedAnnularParity e j).1 := by
  exact canonicalMixedOrderParityBoxTimes_parity e
    (fun z ↦ expandedAnnularTimeDepthBox N eta z.1)
    (annularOccurrenceParity k) t
    (mem_annularCanonicalTimeBoundaryTupleFamily_iff.mp ht).1 j

/-! ## Positive canonical torus-box masses for arbitrary tagged families -/

def uniformAnnularSignedTorusTupleMassSum
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (tuples : Finset (Fin (MixedOccurrenceCount k) → ℕ)) : ℝ :=
  ∑ times ∈ tuples,
    uniform01Measure.real
      (canonicalAnnularSignedTorusTupleEvent ε A N e times)

def aggregateUniformAnnularSignedTorusTupleMassSum
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (tuples :
      (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k) →
      Finset (Fin (MixedOccurrenceCount k) → ℕ)) : ℝ :=
  ∑ e, uniformAnnularSignedTorusTupleMassSum ε A N e (tuples e)

/-- Source-coordinate form of the contracted canonical mass.  The
injectivity side condition is the exact finite statement that chronological
reindexing does not lose multiplicity. -/
theorem uniformAnnularSignedTorusTupleMassSum_contracted_eq_source
    (ε A : ℝ) (N : ℕ) (eta : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    uniformAnnularSignedTorusTupleMassSum ε A N e
        (contractedCanonicalAnnularGridTupleFamily N eta k e) =
      ∑ F ∈ contractedAnnularCanonicalOrderSource N eta k e,
        uniform01Measure.real
          (canonicalAnnularSignedTorusTupleEvent ε A N e
            (fixedOrderMixedTimes N k e F)) := by
  rw [contractedCanonicalAnnularGridTupleFamily_eq_image_source]
  unfold uniformAnnularSignedTorusTupleMassSum
  rw [Finset.sum_image]
  intro F _hF G _hG hFG
  exact fixedOrderMixedTimes_injective N k e hFG

/-- Source-coordinate form of the expanded canonical mass. -/
theorem uniformAnnularSignedTorusTupleMassSum_expanded_eq_source
    (ε A : ℝ) (N : ℕ) (eta : ℝ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    uniformAnnularSignedTorusTupleMassSum ε A N e
        (expandedCanonicalAnnularGridTupleFamily N eta k e) =
      ∑ F ∈ expandedAnnularCanonicalOrderSource N eta k e,
        uniform01Measure.real
          (canonicalAnnularSignedTorusTupleEvent ε A N e
            (fixedOrderMixedTimes N k e F)) := by
  rw [expandedCanonicalAnnularGridTupleFamily_eq_image_source]
  unfold uniformAnnularSignedTorusTupleMassSum
  rw [Finset.sum_image]
  intro F _hF G _hG hFG
  exact fixedOrderMixedTimes_injective N k e hFG

/-- Source-coordinate form of the unshifted canonical mass. -/
theorem uniformAnnularSignedTorusTupleMassSum_canonical_eq_source
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    uniformAnnularSignedTorusTupleMassSum ε A N e
        (canonicalAnnularGridTupleFamily N k e) =
      ∑ F ∈ annularCanonicalOrderSource N k e,
        uniform01Measure.real
          (canonicalAnnularSignedTorusTupleEvent ε A N e
            (fixedOrderMixedTimes N k e F)) := by
  rw [canonicalAnnularGridTupleFamily_eq_image_source]
  unfold uniformAnnularSignedTorusTupleMassSum
  rw [Finset.sum_image]
  intro F _hF G _hG hFG
  exact fixedOrderMixedTimes_injective N k e hFG

theorem uniformAnnularSignedTorusTupleMassSum_le_signed_mass
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (tuples : Finset (Fin (MixedOccurrenceCount k) → ℕ)) :
    uniformAnnularSignedTorusTupleMassSum ε A N e tuples ≤
      movingSignedApproximationTupleMassSum
        uniform01Measure (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) tuples := by
  unfold uniformAnnularSignedTorusTupleMassSum
    movingSignedApproximationTupleMassSum
  apply Finset.sum_le_sum
  intro times _htimes
  apply measureReal_mono
    (h₂ := ne_of_lt
      (measure_lt_top uniform01Measure
        (gaussSignedApproximationTupleEvent
          (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e) times)))
  intro x hx
  exact hx.2

theorem aggregateUniformAnnularSignedTorusTupleMassSum_le_signed_mass
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (tuples :
      (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k) →
      Finset (Fin (MixedOccurrenceCount k) → ℕ)) :
    aggregateUniformAnnularSignedTorusTupleMassSum
        ε A N k tuples ≤
      aggregateUniformMovingSignedApproximationTupleMassSum
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        tuples := by
  unfold aggregateUniformAnnularSignedTorusTupleMassSum
    aggregateUniformMovingSignedApproximationTupleMassSum
    aggregateMovingSignedApproximationTupleMassSum
  apply Finset.sum_le_sum
  intro e _he
  exact uniformAnnularSignedTorusTupleMassSum_le_signed_mass
    ε A N e (tuples e)

theorem aggregateUniformAnnularSignedTorus_boundary_eq_sub
    (ε A : ℝ) (N : ℕ) {grid : ℕ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ) :
    aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
        (fun e ↦ annularCanonicalTimeBoundaryTupleFamily N eta k e) =
      aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
          (fun e ↦ expandedCanonicalAnnularGridTupleFamily N eta k e) -
        aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
          (fun e ↦ contractedCanonicalAnnularGridTupleFamily N eta k e) := by
  unfold aggregateUniformAnnularSignedTorusTupleMassSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  unfold uniformAnnularSignedTorusTupleMassSum
  exact Finset.sum_sdiff_eq_sub
    (contractedCanonicalAnnularGridTupleFamily_subset_expanded
      heta k e)

theorem
    canonical_torusBox_mass_sub_contracted_le_timeBoundary_mass
    {ε A : ℝ} {grid N : ℕ} (hgrid : 0 < grid)
    {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    (reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀ :
        Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
          (unitTorusHalfOpenBox
            (flattenedAnnularTorusLower e₀)
            (flattenedAnnularTorusUpper e₀)) -
        aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
          (fun e ↦
            contractedCanonicalAnnularGridTupleFamily N eta k e) ≤
      aggregateUniformMovingSignedApproximationTupleMassSum
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        (fun e ↦
          annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
  rw [reindexedAnnularUniformMarkedTupleFiniteMeasure_real_flattenedTorusBox
    hgrid N k htorus e₀]
  change
    aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
          (fun e ↦ canonicalAnnularGridTupleFamily N k e) -
        aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
          (fun e ↦
            contractedCanonicalAnnularGridTupleFamily N eta k e) ≤ _
  calc
    _ ≤ aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
      rw [aggregateUniformAnnularSignedTorus_boundary_eq_sub
        ε A N heta k]
      apply sub_le_sub_right
      unfold aggregateUniformAnnularSignedTorusTupleMassSum
      apply Finset.sum_le_sum
      intro e _he
      unfold uniformAnnularSignedTorusTupleMassSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact canonicalAnnularGridTupleFamily_subset_expanded
          heta k e
      · intro _t _ht _hnot
        exact measureReal_nonneg
    _ ≤ _ :=
      aggregateUniformAnnularSignedTorusTupleMassSum_le_signed_mass
        ε A N k
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e)

theorem contracted_torusBox_mass_le_canonical_torusBox_mass
    {ε A : ℝ} {grid N : ℕ} (hgrid : 0 < grid)
    {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
        (fun e ↦
          contractedCanonicalAnnularGridTupleFamily N eta k e) ≤
      (reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀ :
        Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
          (unitTorusHalfOpenBox
            (flattenedAnnularTorusLower e₀)
            (flattenedAnnularTorusUpper e₀)) := by
  rw [reindexedAnnularUniformMarkedTupleFiniteMeasure_real_flattenedTorusBox
    hgrid N k htorus e₀]
  unfold aggregateUniformAnnularSignedTorusTupleMassSum
  apply Finset.sum_le_sum
  intro e _he
  unfold uniformAnnularSignedTorusTupleMassSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact contractedCanonicalAnnularGridTupleFamily_subset_canonical
      heta k e
  · intro _t _ht _hnot
    exact measureReal_nonneg

theorem canonical_torusBox_mass_le_expanded_torusBox_mass
    {ε A : ℝ} {grid N : ℕ} (hgrid : 0 < grid)
    {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    (reindexedAnnularUniformMarkedTupleFiniteMeasure
          (ε := ε) (A := A) N k e₀ :
        Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
          (unitTorusHalfOpenBox
            (flattenedAnnularTorusLower e₀)
            (flattenedAnnularTorusUpper e₀)) ≤
      aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
        (fun e ↦
          expandedCanonicalAnnularGridTupleFamily N eta k e) := by
  rw [reindexedAnnularUniformMarkedTupleFiniteMeasure_real_flattenedTorusBox
    hgrid N k htorus e₀]
  unfold aggregateUniformAnnularSignedTorusTupleMassSum
  apply Finset.sum_le_sum
  intro e _he
  unfold uniformAnnularSignedTorusTupleMassSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact canonicalAnnularGridTupleFamily_subset_expanded heta k e
  · intro _t _ht _hnot
    exact measureReal_nonneg

theorem
    expanded_torusBox_mass_sub_canonical_le_timeBoundary_mass
    {ε A : ℝ} {grid N : ℕ} (hgrid : 0 < grid)
    {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e₀ : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k) :
    aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
          (fun e ↦
            expandedCanonicalAnnularGridTupleFamily N eta k e) -
        (reindexedAnnularUniformMarkedTupleFiniteMeasure
            (ε := ε) (A := A) N k e₀ :
          Measure (UnitAddTorus (Fin (MixedOccurrenceCount k)))).real
            (unitTorusHalfOpenBox
              (flattenedAnnularTorusLower e₀)
              (flattenedAnnularTorusUpper e₀)) ≤
      aggregateUniformMovingSignedApproximationTupleMassSum
        (Real.log (N : ℝ))
        (fun e ↦ flattenedAnnularSignedLower ε A e)
        (fun e ↦ flattenedAnnularSignedUpper ε A e)
        (fun e ↦
          annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
  have hcontractedCanonical :=
    contracted_torusBox_mass_le_canonical_torusBox_mass
      (ε := ε) (A := A) (N := N) hgrid heta k htorus e₀
  calc
    _ ≤
        aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
            (fun e ↦
              expandedCanonicalAnnularGridTupleFamily N eta k e) -
          aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
            (fun e ↦
              contractedCanonicalAnnularGridTupleFamily N eta k e) :=
      sub_le_sub_left hcontractedCanonical _
    _ =
        aggregateUniformAnnularSignedTorusTupleMassSum ε A N k
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
      rw [aggregateUniformAnnularSignedTorus_boundary_eq_sub
        ε A N heta k]
    _ ≤ _ :=
      aggregateUniformAnnularSignedTorusTupleMassSum_le_signed_mass
        ε A N k
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e)

/-! ## Endpoint and parity-box densities, including the time-zero cell -/

/-- The natural ceiling truncates a negative deterministic time to depth
zero.  This clipped formula is essential for expanded boxes meeting the
left endpoint of the time interval. -/
theorem tendsto_gaussLogDepthEndpoint_div_log_clipped (time : ℝ) :
    Tendsto
      (fun N : ℕ ↦
        (gaussLogDepthEndpoint N time : ℝ) / Real.log (N : ℝ))
      atTop (nhds (max time 0 / gaussRoofMean)) := by
  by_cases htime : 0 ≤ time
  · simpa only [gaussLogDepthEndpoint, max_eq_left htime] using!
      tendsto_natCeil_const_mul_scale_div
        (fun N : ℕ ↦ Real.log (N : ℝ))
        tendsto_log_natCast_atTop htime gaussRoofMean_pos
  · have htimeNeg : time < 0 := lt_of_not_ge htime
    have heq :
        ∀ᶠ N : ℕ in atTop, gaussLogDepthEndpoint N time = 0 := by
      filter_upwards
        [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
      unfold gaussLogDepthEndpoint
      apply Nat.ceil_eq_zero.mpr
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg htimeNeg.le hlog.le)
        gaussRoofMean_pos.le
    have hzero :
        Tendsto (fun _N : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    have htarget :
        Tendsto
          (fun N : ℕ ↦
            (gaussLogDepthEndpoint N time : ℝ) /
              Real.log (N : ℝ))
          atTop (nhds 0) := by
      apply hzero.congr'
      filter_upwards [heq] with N hN
      simp only [hN, Nat.cast_zero, zero_div]
    simpa only [max_eq_right htimeNeg.le, zero_div] using! htarget

/-- Parity-filtered contracted time box. -/
def contractedAnnularTimeParityDepthBox
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (i : AnnularGridIndex grid) : Finset ℕ :=
  parityIco
    (gaussLogDepthEndpoint N
      (intervalGridPoint 0 1 grid i.time.1 + eta))
    (gaussLogDepthEndpoint N
      (intervalGridPoint 0 1 grid (i.time.1 + 1) - eta))
    (annularGridDepthParity i)

/-- Parity-filtered expanded time box. -/
def expandedAnnularTimeParityDepthBox
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (i : AnnularGridIndex grid) : Finset ℕ :=
  parityIco
    (gaussLogDepthEndpoint N
      (intervalGridPoint 0 1 grid i.time.1 - eta))
    (gaussLogDepthEndpoint N
      (intervalGridPoint 0 1 grid (i.time.1 + 1) + eta))
    (annularGridDepthParity i)

theorem contractedAnnularTimeParityDepthBox_eq_filter
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (i : AnnularGridIndex grid) :
    contractedAnnularTimeParityDepthBox N eta i =
      (contractedAnnularTimeDepthBox N eta i).filter
        (fun n ↦ n % 2 = (annularGridDepthParity i).1) := by
  rfl

theorem expandedAnnularTimeParityDepthBox_eq_filter
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (i : AnnularGridIndex grid) :
    expandedAnnularTimeParityDepthBox N eta i =
      (expandedAnnularTimeDepthBox N eta i).filter
        (fun n ↦ n % 2 = (annularGridDepthParity i).1) := by
  rfl

/-- The asymptotic parity density of one contracted time box.  The `max`
terms record the literal truncation of natural depths at zero. -/
theorem tendsto_contractedAnnularTimeParityDepthBox_card_div_log
    {grid : ℕ} (i : AnnularGridIndex grid) {eta : ℝ}
    (hwidth :
      intervalGridPoint 0 1 grid i.time.1 + eta ≤
        intervalGridPoint 0 1 grid (i.time.1 + 1) - eta) :
    Tendsto
      (fun N : ℕ ↦
        ((contractedAnnularTimeParityDepthBox N eta i).card : ℝ) /
          Real.log (N : ℝ))
      atTop
      (nhds
        ((max
              (intervalGridPoint 0 1 grid (i.time.1 + 1) - eta) 0 -
            max
              (intervalGridPoint 0 1 grid i.time.1 + eta) 0) /
          (2 * gaussRoofMean))) := by
  have hab :
      ∀ᶠ N : ℕ in atTop,
        gaussLogDepthEndpoint N
            (intervalGridPoint 0 1 grid i.time.1 + eta) ≤
          gaussLogDepthEndpoint N
            (intervalGridPoint 0 1 grid (i.time.1 + 1) - eta) := by
    exact Eventually.of_forall fun N ↦ Nat.ceil_mono <| by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hwidth
          (Real.log_natCast_nonneg N))
        gaussRoofMean_pos.le
  have hraw :=
    tendsto_card_parityIco_div_scale
      (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (fun N ↦ gaussLogDepthEndpoint N
        (intervalGridPoint 0 1 grid i.time.1 + eta))
      (fun N ↦ gaussLogDepthEndpoint N
        (intervalGridPoint 0 1 grid (i.time.1 + 1) - eta))
      (annularGridDepthParity i) hab
      (tendsto_gaussLogDepthEndpoint_div_log_clipped
        (intervalGridPoint 0 1 grid i.time.1 + eta))
      (tendsto_gaussLogDepthEndpoint_div_log_clipped
        (intervalGridPoint 0 1 grid (i.time.1 + 1) - eta))
  convert! hraw using 1
  field_simp [ne_of_gt gaussRoofMean_pos]

/-- The corresponding expanded density. -/
theorem tendsto_expandedAnnularTimeParityDepthBox_card_div_log
    {grid : ℕ} (i : AnnularGridIndex grid) {eta : ℝ}
    (hwidth :
      intervalGridPoint 0 1 grid i.time.1 - eta ≤
        intervalGridPoint 0 1 grid (i.time.1 + 1) + eta) :
    Tendsto
      (fun N : ℕ ↦
        ((expandedAnnularTimeParityDepthBox N eta i).card : ℝ) /
          Real.log (N : ℝ))
      atTop
      (nhds
        ((max
              (intervalGridPoint 0 1 grid (i.time.1 + 1) + eta) 0 -
            max
              (intervalGridPoint 0 1 grid i.time.1 - eta) 0) /
          (2 * gaussRoofMean))) := by
  have hab :
      ∀ᶠ N : ℕ in atTop,
        gaussLogDepthEndpoint N
            (intervalGridPoint 0 1 grid i.time.1 - eta) ≤
          gaussLogDepthEndpoint N
            (intervalGridPoint 0 1 grid (i.time.1 + 1) + eta) := by
    exact Eventually.of_forall fun N ↦ Nat.ceil_mono <| by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hwidth
          (Real.log_natCast_nonneg N))
        gaussRoofMean_pos.le
  have hraw :=
    tendsto_card_parityIco_div_scale
      (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (fun N ↦ gaussLogDepthEndpoint N
        (intervalGridPoint 0 1 grid i.time.1 - eta))
      (fun N ↦ gaussLogDepthEndpoint N
        (intervalGridPoint 0 1 grid (i.time.1 + 1) + eta))
      (annularGridDepthParity i) hab
      (tendsto_gaussLogDepthEndpoint_div_log_clipped
        (intervalGridPoint 0 1 grid i.time.1 - eta))
      (tendsto_gaussLogDepthEndpoint_div_log_clipped
        (intervalGridPoint 0 1 grid (i.time.1 + 1) + eta))
  convert! hraw using 1
  field_simp [ne_of_gt gaussRoofMean_pos]

/-! ## Generic tagged-cardinality bridge for shifted boxes -/

/-- Coordinatewise parity restriction of arbitrary labeled natural boxes. -/
def mixedOccurrenceParityBox
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (z : GaussPrefixMixedOccurrence k) : Finset ℕ :=
  (boxes z).filter (fun n ↦ n % 2 = (parity z).1)

/-- Full labeled assignment box with the parity restrictions inserted. -/
def mixedOccurrenceParityAssignmentBox
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :
    Finset (GaussPrefixMixedOccurrence k → ℕ) :=
  Fintype.piFinset (mixedOccurrenceParityBox boxes parity)

/-- Injective part of the preceding labeled assignment box. -/
def injectiveMixedOccurrenceParityAssignmentBox
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :
    Finset (GaussPrefixMixedOccurrence k → ℕ) :=
  (mixedOccurrenceParityAssignmentBox boxes parity).filter
    Function.Injective

/-- Noninjective part of the same finite assignment box. -/
def noninjectiveMixedOccurrenceParityAssignmentBox
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :
    Finset (GaussPrefixMixedOccurrence k → ℕ) :=
  (mixedOccurrenceParityAssignmentBox boxes parity).filter
    (fun f ↦ ¬ Function.Injective f)

/-- Globally injective literal tuples satisfying arbitrary labeled boxes
and parity restrictions. -/
def eligibleMixedOccurrenceParityBoxTuples
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :
    Finset (GloballyInjectiveMixedDepthTuple N k) := by
  classical
  exact Finset.univ.filter fun F ↦
    ∀ j,
      fixedOrderMixedTimes N k
          (canonicalMixedOccurrenceOrder N k F) F j ∈
        boxes (canonicalMixedOccurrenceOrder N k F j) ∧
      fixedOrderMixedTimes N k
          (canonicalMixedOccurrenceOrder N k F) F j % 2 =
        (parity (canonicalMixedOccurrenceOrder N k F j)).1

/-- Summing cardinalities over all chronological order tags counts the
eligible globally injective literal tuples exactly once. -/
theorem aggregate_card_canonicalMixedOrderParityBoxTimes_eq_eligible
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :
    aggregateTupleFamilyCard
        (fun e ↦
          canonicalMixedOrderParityBoxTimes N k e boxes parity) =
      (eligibleMixedOccurrenceParityBoxTuples
        N k boxes parity).card := by
  classical
  let eligible :=
    eligibleMixedOccurrenceParityBoxTuples N k boxes parity
  let order :
      GloballyInjectiveMixedDepthTuple N k →
        (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :=
    canonicalMixedOccurrenceOrder N k
  have hfiber :
      eligible.card =
        ∑ e :
            Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
          (eligible.filter (fun F ↦ order F = e)).card := by
    have hraw := Finset.card_eq_sum_card_fiberwise
      (s := eligible)
      (t := (Finset.univ :
        Finset (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k)))
      (f := order) (by
        intro F _hF
        exact Finset.mem_univ _)
    simpa only [Finset.sum_filter, Finset.sum_const_zero,
      Finset.sum_add_distrib, Finset.mem_univ, if_true,
      Finset.filter_filter, and_self] using! hraw
  rw [hfiber]
  unfold aggregateTupleFamilyCard
  apply Finset.sum_congr rfl
  intro e _he
  rw [card_canonicalMixedOrderParityBoxTimes]
  congr 1
  ext F
  simp only [eligible, eligibleMixedOccurrenceParityBoxTuples,
    canonicalMixedOrderClass, Finset.mem_filter, Finset.mem_univ,
    true_and, order]
  constructor
  · rintro ⟨horder, hbox⟩
    refine ⟨?_, horder⟩
    simpa only [horder] using! hbox
  · rintro ⟨hbox, horder⟩
    refine ⟨horder, ?_⟩
    simpa only [horder] using! hbox

abbrev EligibleMixedOccurrenceParityBoxTupleSubtype
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :=
  {F // F ∈ eligibleMixedOccurrenceParityBoxTuples N k boxes parity}

abbrev InjectiveMixedOccurrenceParityAssignmentSubtype
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :=
  {f // f ∈ injectiveMixedOccurrenceParityAssignmentBox boxes parity}

/-- Forgetting the embedding wrappers gives the labeled depth
assignment of an eligible tuple. -/
noncomputable def eligibleMixedOccurrenceDepthAssignment
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (F : EligibleMixedOccurrenceParityBoxTupleSubtype
      N k boxes parity) :
    InjectiveMixedOccurrenceParityAssignmentSubtype boxes parity := by
  let f : GaussPrefixMixedOccurrence k → ℕ :=
    fun z ↦ (F.1.1 z.1 z.2 : ℕ)
  refine ⟨f, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro z
    have hEligible := (Finset.mem_filter.mp F.2).2
    let e := canonicalMixedOccurrenceOrder N k F.1
    let j : Fin (MixedOccurrenceCount k) := e.symm z
    have hj := hEligible j
    have hej : e j = z := e.apply_symm_apply z
    have hdepth :
        fixedOrderMixedTimes N k e F.1 j = f z := by
      change (F.1.1 (e j).1 (e j).2 : ℕ) =
        (F.1.1 z.1 z.2 : ℕ)
      rw [hej]
    have hbox : f z ∈ boxes z := by
      rw [← hdepth, ← hej]
      exact hj.1
    have hparity : f z % 2 = (parity z).1 := by
      rw [← hdepth, ← hej]
      exact hj.2
    exact Finset.mem_filter.mpr ⟨hbox, hparity⟩
  · exact F.1.2

theorem eligibleMixedOccurrenceDepthAssignment_injective
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2) :
    Function.Injective
      (eligibleMixedOccurrenceDepthAssignment N k boxes parity) := by
  intro F G hFG
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Function.Embedding.ext
  intro j
  apply Subtype.ext
  have h :=
    congrFun (congrArg Subtype.val hFG)
      (⟨i, j⟩ : GaussPrefixMixedOccurrence k)
  exact h

/-- Reconstruct a globally injective mixed tuple from an injective labeled
assignment whose depths lie below the literal cutoff. -/
noncomputable def globallyInjectiveTupleOfMixedOccurrenceAssignment
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    {boxes : GaussPrefixMixedOccurrence k → Finset ℕ}
    {parity : GaussPrefixMixedOccurrence k → Fin 2}
    (G : InjectiveMixedOccurrenceParityAssignmentSubtype boxes parity)
    (hbound : ∀ z, G.1 z ≤ N) :
    GloballyInjectiveMixedDepthTuple N k := by
  let F : GaussPrefixMixedDepthTuple N k := fun i ↦
    { toFun := fun j ↦ ⟨G.1 ⟨i, j⟩, by
        simp only [Finset.mem_Icc]
        exact ⟨Nat.zero_le _, hbound ⟨i, j⟩⟩⟩
      inj' := by
        intro a b hab
        have hGinj := (Finset.mem_filter.mp G.2).2
        have hsigma :
            (⟨i, a⟩ : GaussPrefixMixedOccurrence k) = ⟨i, b⟩ :=
          hGinj (congrArg Subtype.val hab)
        exact ((Sigma.mk.inj_iff.mp hsigma).2).eq }
  refine ⟨F, ?_⟩
  intro z z' hzz
  exact (Finset.mem_filter.mp G.2).2 hzz

theorem globallyInjectiveTupleOfMixedOccurrenceAssignment_depth
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    {boxes : GaussPrefixMixedOccurrence k → Finset ℕ}
    {parity : GaussPrefixMixedOccurrence k → Fin 2}
    (G : InjectiveMixedOccurrenceParityAssignmentSubtype boxes parity)
    (hbound : ∀ z, G.1 z ≤ N)
    (z : GaussPrefixMixedOccurrence k) :
    ((globallyInjectiveTupleOfMixedOccurrenceAssignment
        N k G hbound).1 z.1 z.2 : ℕ) = G.1 z := by
  rfl

theorem globallyInjectiveTupleOfMixedOccurrenceAssignment_eligible
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    {boxes : GaussPrefixMixedOccurrence k → Finset ℕ}
    {parity : GaussPrefixMixedOccurrence k → Fin 2}
    (G : InjectiveMixedOccurrenceParityAssignmentSubtype boxes parity)
    (hbound : ∀ z, G.1 z ≤ N) :
    globallyInjectiveTupleOfMixedOccurrenceAssignment N k G hbound ∈
      eligibleMixedOccurrenceParityBoxTuples N k boxes parity := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro j
  let F :=
    globallyInjectiveTupleOfMixedOccurrenceAssignment N k G hbound
  let e := canonicalMixedOccurrenceOrder N k F
  have hmemAll :
      ∀ z, G.1 z ∈ mixedOccurrenceParityBox boxes parity z :=
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp G.2).1
  have hz := hmemAll (e j)
  have hz' :
      G.1 (e j) ∈ boxes (e j) ∧
        G.1 (e j) % 2 = (parity (e j)).1 :=
    Finset.mem_filter.mp hz
  simpa only [fixedOrderMixedTimes,
    globallyInjectiveTupleOfMixedOccurrenceAssignment_depth] using! hz'

theorem eligibleMixedOccurrenceDepthAssignment_surjective_of_bound
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (hbound : ∀ z q,
      q ∈ mixedOccurrenceParityBox boxes parity z → q ≤ N) :
    Function.Surjective
      (eligibleMixedOccurrenceDepthAssignment N k boxes parity) := by
  intro G
  have hGall :
      ∀ z, G.1 z ∈ mixedOccurrenceParityBox boxes parity z :=
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp G.2).1
  have hGN : ∀ z, G.1 z ≤ N :=
    fun z ↦ hbound z (G.1 z) (hGall z)
  let F := globallyInjectiveTupleOfMixedOccurrenceAssignment N k G hGN
  have hFelig :
      F ∈ eligibleMixedOccurrenceParityBoxTuples N k boxes parity :=
    globallyInjectiveTupleOfMixedOccurrenceAssignment_eligible
      N k G hGN
  refine ⟨⟨F, hFelig⟩, ?_⟩
  apply Subtype.ext
  funext z
  exact globallyInjectiveTupleOfMixedOccurrenceAssignment_depth
    N k G hGN z

/-- Exact aggregate tagged-cardinality formula for arbitrary boxes once
all selected natural depths lie in the literal cutoff. -/
theorem aggregate_card_canonicalMixedOrderParityBoxTimes_eq_injective
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (boxes : GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (hbound : ∀ z q,
      q ∈ mixedOccurrenceParityBox boxes parity z → q ≤ N) :
    aggregateTupleFamilyCard
        (fun e ↦
          canonicalMixedOrderParityBoxTimes N k e boxes parity) =
      (injectiveMixedOccurrenceParityAssignmentBox boxes parity).card := by
  rw [aggregate_card_canonicalMixedOrderParityBoxTimes_eq_eligible]
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.ofBijective
    (eligibleMixedOccurrenceDepthAssignment N k boxes parity)
    ⟨eligibleMixedOccurrenceDepthAssignment_injective
        N k boxes parity,
      eligibleMixedOccurrenceDepthAssignment_surjective_of_bound
        N k boxes parity hbound⟩)

/-! ## Generic product, collision, and tagged densities -/

theorem tendsto_mixedOccurrenceParityAssignmentBox_card_div_log_pow
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (boxes :
      ℕ → GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (factor : GaussPrefixMixedOccurrence k → ℝ)
    (hcoordinate : ∀ z,
      Tendsto
        (fun N ↦
          ((mixedOccurrenceParityBox (boxes N) parity z).card : ℝ) /
            Real.log (N : ℝ))
        atTop (nhds (factor z))) :
    Tendsto
      (fun N ↦
        ((mixedOccurrenceParityAssignmentBox
            (boxes N) parity).card : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds (∏ z, factor z)) := by
  have hprod :
      Tendsto
        (fun N ↦ ∏ z : GaussPrefixMixedOccurrence k,
          ((mixedOccurrenceParityBox
              (boxes N) parity z).card : ℝ) /
            Real.log (N : ℝ))
        atTop (nhds (∏ z, factor z)) := by
    apply tendsto_finset_prod Finset.univ
    intro z _hz
    exact hcoordinate z
  apply hprod.congr'
  filter_upwards with N
  rw [mixedOccurrenceParityAssignmentBox,
    Fintype.card_piFinset]
  symm
  change
    ((∏ z : GaussPrefixMixedOccurrence k,
        (mixedOccurrenceParityBox
          (boxes N) parity z).card : ℕ) : ℝ) /
        Real.log (N : ℝ) ^ MixedOccurrenceCount k =
      ∏ z : GaussPrefixMixedOccurrence k,
        ((mixedOccurrenceParityBox
          (boxes N) parity z).card : ℝ) /
          Real.log (N : ℝ)
  push_cast
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

/-- A one-power collision loss is negligible for any logarithmic family
of coordinate boxes. -/
theorem
    tendsto_noninjectiveMixedOccurrenceParityAssignmentBox_density_zero
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (hr : 0 < MixedOccurrenceCount k)
    (boxes :
      ℕ → GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (H : ℕ → ℕ) {ambientLimit : ℝ}
    (hH :
      Tendsto
        (fun N ↦ (H N : ℝ) / Real.log (N : ℝ))
        atTop (nhds ambientLimit))
    (hbound : ∀ᶠ N : ℕ in atTop, ∀ z q,
      q ∈ mixedOccurrenceParityBox (boxes N) parity z → q < H N) :
    Tendsto
      (fun N ↦
        ((noninjectiveMixedOccurrenceParityAssignmentBox
            (boxes N) parity).card : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
  let r := MixedOccurrenceCount k
  let upper : ℕ → ℝ := fun N ↦
    ((r * r : ℕ) : ℝ) *
      ((H N : ℝ) / Real.log (N : ℝ)) ^ (r - 1) *
        (1 / Real.log (N : ℝ))
  have hrecip :
      Tendsto
        (fun N : ℕ ↦ (1 : ℝ) / Real.log (N : ℝ))
        atTop (nhds 0) :=
    (tendsto_const_nhds : Tendsto
      (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).div_atTop
        tendsto_log_natCast_atTop
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hraw :=
      ((tendsto_const_nhds : Tendsto
        (fun _N : ℕ ↦ ((r * r : ℕ) : ℝ))
          atTop (nhds ((r * r : ℕ) : ℝ))).mul
        (hH.pow (r - 1))).mul hrecip
    simpa only [upper, mul_zero] using! hraw
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by positivity
  · filter_upwards
      [hbound,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
        N hboundN hlog
    have hcardNat :
        (noninjectiveMixedOccurrenceParityAssignmentBox
          (boxes N) parity).card ≤
            r * r * H N ^ (r - 1) := by
      have hgeneric :=
        card_filter_not_injective_piFinset_le
          (σ := GaussPrefixMixedOccurrence k)
          (boxes := mixedOccurrenceParityBox (boxes N) parity)
          (H := H N) hboundN
      simpa only [noninjectiveMixedOccurrenceParityAssignmentBox,
        mixedOccurrenceParityAssignmentBox, r] using! hgeneric
    have hcardReal :
        ((noninjectiveMixedOccurrenceParityAssignmentBox
            (boxes N) parity).card : ℝ) ≤
          ((r * r * H N ^ (r - 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcardNat
    have hdiv := div_le_div_of_nonneg_right hcardReal
      (pow_nonneg hlog.le r)
    calc
      ((noninjectiveMixedOccurrenceParityAssignmentBox
            (boxes N) parity).card : ℝ) /
          Real.log (N : ℝ) ^ r ≤
        ((r * r * H N ^ (r - 1) : ℕ) : ℝ) /
          Real.log (N : ℝ) ^ r := hdiv
      _ = upper N := by
        dsimp only [upper]
        rw [show r = (r - 1) + 1 by omega, pow_succ]
        push_cast
        rw [div_pow]
        field_simp [ne_of_gt hlog]
  · exact hupper

/-- Removing collisions preserves an arbitrary product density. -/
theorem tendsto_injectiveMixedOccurrenceParityAssignmentBox_density
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (hr : 0 < MixedOccurrenceCount k)
    (boxes :
      ℕ → GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (density : ℝ)
    (hall :
      Tendsto
        (fun N ↦
          ((mixedOccurrenceParityAssignmentBox
              (boxes N) parity).card : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
        atTop (nhds density))
    (H : ℕ → ℕ) {ambientLimit : ℝ}
    (hH :
      Tendsto
        (fun N ↦ (H N : ℝ) / Real.log (N : ℝ))
        atTop (nhds ambientLimit))
    (hbound : ∀ᶠ N : ℕ in atTop, ∀ z q,
      q ∈ mixedOccurrenceParityBox (boxes N) parity z → q < H N) :
    Tendsto
      (fun N ↦
        ((injectiveMixedOccurrenceParityAssignmentBox
            (boxes N) parity).card : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds density) := by
  have hbad :=
    tendsto_noninjectiveMixedOccurrenceParityAssignmentBox_density_zero
      hr boxes parity H hH hbound
  have hsub := hall.sub hbad
  have hsub' :
      Tendsto
        (fun N ↦
          ((mixedOccurrenceParityAssignmentBox
              (boxes N) parity).card : ℝ) /
              Real.log (N : ℝ) ^ MixedOccurrenceCount k -
            ((noninjectiveMixedOccurrenceParityAssignmentBox
              (boxes N) parity).card : ℝ) /
              Real.log (N : ℝ) ^ MixedOccurrenceCount k)
        atTop (nhds density) := by
    simpa only [sub_zero] using! hsub
  apply hsub'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  have hcard :=
    Finset.card_filter_add_card_filter_not
      (s := mixedOccurrenceParityAssignmentBox (boxes N) parity)
      (p := Function.Injective)
  have hcardReal :
      ((injectiveMixedOccurrenceParityAssignmentBox
          (boxes N) parity).card : ℝ) +
        ((noninjectiveMixedOccurrenceParityAssignmentBox
          (boxes N) parity).card : ℝ) =
        ((mixedOccurrenceParityAssignmentBox
          (boxes N) parity).card : ℝ) := by
    exact_mod_cast hcard
  rw [← hcardReal]
  ring

/-- Generic asymptotic tagged-cardinality transfer from labeled product
boxes. -/
theorem tendsto_aggregate_card_canonicalMixedOrderParityBoxTimes
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (hr : 0 < MixedOccurrenceCount k)
    (boxes :
      ℕ → GaussPrefixMixedOccurrence k → Finset ℕ)
    (parity : GaussPrefixMixedOccurrence k → Fin 2)
    (density : ℝ)
    (hall :
      Tendsto
        (fun N ↦
          ((mixedOccurrenceParityAssignmentBox
              (boxes N) parity).card : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
        atTop (nhds density))
    (H : ℕ → ℕ) {ambientLimit : ℝ}
    (hH :
      Tendsto
        (fun N ↦ (H N : ℝ) / Real.log (N : ℝ))
        atTop (nhds ambientLimit))
    (hbound : ∀ᶠ N : ℕ in atTop, ∀ z q,
      q ∈ mixedOccurrenceParityBox (boxes N) parity z → q < H N)
    (hcutoff : ∀ᶠ N : ℕ in atTop, ∀ z q,
      q ∈ mixedOccurrenceParityBox (boxes N) parity z → q ≤ N) :
    Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦ canonicalMixedOrderParityBoxTimes
            N k e (boxes N) parity) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds density) := by
  have hinjective :=
    tendsto_injectiveMixedOccurrenceParityAssignmentBox_density
      hr boxes parity density hall H hH hbound
  apply hinjective.congr'
  filter_upwards [hcutoff] with N hcutoffN
  rw [aggregate_card_canonicalMixedOrderParityBoxTimes_eq_injective
    N k (boxes N) parity hcutoffN]

/-! ## Shifted annular product densities -/

def contractedAnnularTimeDensityFactor
    (eta : ℝ) {grid : ℕ} (i : AnnularGridIndex grid) : ℝ :=
  (max (intervalGridPoint 0 1 grid (i.time.1 + 1) - eta) 0 -
      max (intervalGridPoint 0 1 grid i.time.1 + eta) 0) /
    (2 * gaussRoofMean)

def expandedAnnularTimeDensityFactor
    (eta : ℝ) {grid : ℕ} (i : AnnularGridIndex grid) : ℝ :=
  (max (intervalGridPoint 0 1 grid (i.time.1 + 1) + eta) 0 -
      max (intervalGridPoint 0 1 grid i.time.1 - eta) 0) /
    (2 * gaussRoofMean)

def contractedAnnularOccurrenceTimeDensity
    (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℝ :=
  ∏ z : GaussPrefixMixedOccurrence k,
    contractedAnnularTimeDensityFactor eta z.1

def expandedAnnularOccurrenceTimeDensity
    (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℝ :=
  ∏ z : GaussPrefixMixedOccurrence k,
    expandedAnnularTimeDensityFactor eta z.1

def contractedAnnularOccurrenceDepthBoxes
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    GaussPrefixMixedOccurrence k → Finset ℕ :=
  fun z ↦ contractedAnnularTimeDepthBox N eta z.1

def expandedAnnularOccurrenceDepthBoxes
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    GaussPrefixMixedOccurrence k → Finset ℕ :=
  fun z ↦ expandedAnnularTimeDepthBox N eta z.1

theorem mixedOccurrenceParityBox_contracted_eq
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (z : GaussPrefixMixedOccurrence k) :
    mixedOccurrenceParityBox
        (contractedAnnularOccurrenceDepthBoxes N eta k)
        (annularOccurrenceParity k) z =
      contractedAnnularTimeParityDepthBox N eta z.1 := by
  rfl

theorem mixedOccurrenceParityBox_expanded_eq
    (N : ℕ) (eta : ℝ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (z : GaussPrefixMixedOccurrence k) :
    mixedOccurrenceParityBox
        (expandedAnnularOccurrenceDepthBoxes N eta k)
        (annularOccurrenceParity k) z =
      expandedAnnularTimeParityDepthBox N eta z.1 := by
  rfl

theorem contracted_time_width_of_eta
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (hetaWidth : 2 * eta ≤ 1 / (grid : ℝ))
    (i : AnnularGridIndex grid) :
    intervalGridPoint 0 1 grid i.time.1 + eta ≤
      intervalGridPoint 0 1 grid (i.time.1 + 1) - eta := by
  have hstep :=
    intervalGridPoint_succ_sub
      (a := (0 : ℝ)) (b := 1) (k := i.time.1) hgrid
  norm_num at hstep
  have hetaWidth' : 2 * eta ≤ (grid : ℝ)⁻¹ := by
    simpa only [one_div] using! hetaWidth
  linarith

theorem expanded_time_width_of_nonneg_eta
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta) (i : AnnularGridIndex grid) :
    intervalGridPoint 0 1 grid i.time.1 - eta ≤
      intervalGridPoint 0 1 grid (i.time.1 + 1) + eta := by
  have hstep :=
    intervalGridPoint_strictMono_step
      (a := (0 : ℝ)) (b := 1) zero_lt_one hgrid
      (k := i.time.1)
  linarith

theorem
    tendsto_contractedAnnularOccurrenceParityAssignmentBox_density
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (hetaWidth : 2 * eta ≤ 1 / (grid : ℝ))
    (k : AnnularGridIndex grid → ℕ) :
    Tendsto
      (fun N ↦
        ((mixedOccurrenceParityAssignmentBox
            (contractedAnnularOccurrenceDepthBoxes N eta k)
            (annularOccurrenceParity k)).card : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop
      (nhds (contractedAnnularOccurrenceTimeDensity eta k)) := by
  simpa only [contractedAnnularOccurrenceTimeDensity] using!
    tendsto_mixedOccurrenceParityAssignmentBox_card_div_log_pow
      (fun N ↦ contractedAnnularOccurrenceDepthBoxes N eta k)
      (annularOccurrenceParity k)
      (fun z ↦ contractedAnnularTimeDensityFactor eta z.1)
      (fun z ↦ by
        change Tendsto
          (fun N ↦
            ((contractedAnnularTimeParityDepthBox
                N eta z.1).card : ℝ) /
              Real.log (N : ℝ))
          atTop
          (nhds (contractedAnnularTimeDensityFactor eta z.1))
        simpa only [contractedAnnularTimeDensityFactor] using!
          tendsto_contractedAnnularTimeParityDepthBox_card_div_log
            z.1 (contracted_time_width_of_eta hgrid hetaWidth z.1))

theorem
    tendsto_expandedAnnularOccurrenceParityAssignmentBox_density
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ) :
    Tendsto
      (fun N ↦
        ((mixedOccurrenceParityAssignmentBox
            (expandedAnnularOccurrenceDepthBoxes N eta k)
            (annularOccurrenceParity k)).card : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop
      (nhds (expandedAnnularOccurrenceTimeDensity eta k)) := by
  simpa only [expandedAnnularOccurrenceTimeDensity] using!
    tendsto_mixedOccurrenceParityAssignmentBox_card_div_log_pow
      (fun N ↦ expandedAnnularOccurrenceDepthBoxes N eta k)
      (annularOccurrenceParity k)
      (fun z ↦ expandedAnnularTimeDensityFactor eta z.1)
      (fun z ↦ by
        change Tendsto
          (fun N ↦
            ((expandedAnnularTimeParityDepthBox
                N eta z.1).card : ℝ) /
              Real.log (N : ℝ))
          atTop
          (nhds (expandedAnnularTimeDensityFactor eta z.1))
        simpa only [expandedAnnularTimeDensityFactor] using!
          tendsto_expandedAnnularTimeParityDepthBox_card_div_log
            z.1 (expanded_time_width_of_nonneg_eta hgrid heta z.1))

/-- A common logarithmic ambient size for all expanded shifted boxes. -/
def expandedAnnularDepthAmbientSize (N : ℕ) (eta : ℝ) : ℕ :=
  gaussLogDepthEndpoint N (1 + eta) + 1

theorem tendsto_expandedAnnularDepthAmbientSize_div_log
    {eta : ℝ} (heta : 0 ≤ eta) :
    Tendsto
      (fun N ↦ (expandedAnnularDepthAmbientSize N eta : ℝ) /
        Real.log (N : ℝ))
      atTop (nhds ((1 + eta) / gaussRoofMean)) := by
  have hmain :=
    tendsto_gaussLogDepthEndpoint_div_log_clipped (1 + eta)
  have hone :
      Tendsto
        (fun N : ℕ ↦ (1 : ℝ) / Real.log (N : ℝ))
        atTop (nhds 0) :=
    (tendsto_const_nhds : Tendsto
      (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).div_atTop
        tendsto_log_natCast_atTop
  have hsum := hmain.add hone
  have hsum' :
      Tendsto
        (fun N : ℕ ↦
          (gaussLogDepthEndpoint N (1 + eta) : ℝ) /
              Real.log (N : ℝ) +
            1 / Real.log (N : ℝ))
        atTop (nhds ((1 + eta) / gaussRoofMean)) := by
    simpa only [max_eq_left (by linarith : 0 ≤ 1 + eta),
      add_zero] using! hsum
  apply hsum'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  unfold expandedAnnularDepthAmbientSize
  push_cast
  field_simp [ne_of_gt hlog]

theorem tendsto_expandedAnnularDepthAmbientSize_div_natCast_zero
    {eta : ℝ} (heta : 0 ≤ eta) :
    Tendsto
      (fun N ↦
        (expandedAnnularDepthAmbientSize N eta : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    (tendsto_expandedAnnularDepthAmbientSize_div_log heta).mul
      tendsto_log_natCast_div_natCast_zero
  have hmul' :
      Tendsto
        (fun N ↦
          (expandedAnnularDepthAmbientSize N eta : ℝ) /
              Real.log (N : ℝ) *
            (Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using! hmul
  apply hmul'.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  field_simp [hlog]

theorem eventually_expandedAnnularDepthAmbientSize_le_nat
    {eta : ℝ} (heta : 0 ≤ eta) :
    ∀ᶠ N : ℕ in atTop,
      expandedAnnularDepthAmbientSize N eta ≤ N := by
  have hlt : ∀ᶠ N : ℕ in atTop,
      (expandedAnnularDepthAmbientSize N eta : ℝ) / (N : ℝ) < 1 :=
    (tendsto_expandedAnnularDepthAmbientSize_div_natCast_zero
      heta).eventually
      (Iio_mem_nhds zero_lt_one)
  filter_upwards [hlt, eventually_ge_atTop 1] with N hratio hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hreal :
      (expandedAnnularDepthAmbientSize N eta : ℝ) < (N : ℝ) :=
    (div_lt_one hNpos).mp hratio
  exact (by exact_mod_cast hreal : expandedAnnularDepthAmbientSize N eta < N).le

theorem tendsto_expandedAnnularDepthAmbientSize_atTop
    {eta : ℝ} (heta : 0 ≤ eta) :
    Tendsto
      (fun N ↦ expandedAnnularDepthAmbientSize N eta)
      atTop atTop := by
  have hcore :
      Tendsto
        (fun N : ℕ ↦ gaussLogDepthEndpoint N (1 + eta))
        atTop atTop := by
    unfold gaussLogDepthEndpoint
    apply tendsto_nat_ceil_atTop.comp
    have htime : 0 < 1 + eta := by linarith
    exact
      ((tendsto_log_natCast_atTop.const_mul_atTop htime).atTop_div_const
        gaussRoofMean_pos)
  exact Filter.tendsto_atTop_mono
    (fun N ↦ Nat.le_add_right
      (gaussLogDepthEndpoint N (1 + eta)) 1) hcore

/-- Fixed tolerance used with the denominator maximal law at a fixed
positive boundary width. -/
def annularBoundaryDenominatorTolerance (eta : ℝ) : ℝ :=
  eta * gaussRoofMean / (2 * (1 + eta))

theorem annularBoundaryDenominatorTolerance_pos
    {eta : ℝ} (heta : 0 < eta) :
    0 < annularBoundaryDenominatorTolerance eta := by
  unfold annularBoundaryDenominatorTolerance
  exact div_pos (mul_pos heta gaussRoofMean_pos)
    (mul_pos (by norm_num) (by linarith))

theorem eventually_annularBoundaryDenominator_margin
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      annularBoundaryDenominatorTolerance eta *
          (expandedAnnularDepthAmbientSize N eta : ℝ) ≤
        eta * Real.log (N : ℝ) := by
  have hetaNonneg : 0 ≤ eta := heta.le
  have hscaled :=
    (tendsto_expandedAnnularDepthAmbientSize_div_log
      hetaNonneg).const_mul
        (annularBoundaryDenominatorTolerance eta)
  have hlimit :
      annularBoundaryDenominatorTolerance eta *
          ((1 + eta) / gaussRoofMean) =
        eta / 2 := by
    unfold annularBoundaryDenominatorTolerance
    field_simp [ne_of_gt gaussRoofMean_pos,
      show (1 + eta) ≠ 0 by positivity]
  rw [hlimit] at hscaled
  have hlt :
      ∀ᶠ N : ℕ in atTop,
        annularBoundaryDenominatorTolerance eta *
            ((expandedAnnularDepthAmbientSize N eta : ℝ) /
              Real.log (N : ℝ)) < eta :=
    hscaled.eventually_lt_const (by linarith)
  filter_upwards
    [hlt,
      tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hN hlog
  have hmul := mul_le_mul_of_nonneg_right hN.le hlog.le
  calc
    annularBoundaryDenominatorTolerance eta *
        (expandedAnnularDepthAmbientSize N eta : ℝ) =
      (annularBoundaryDenominatorTolerance eta *
          ((expandedAnnularDepthAmbientSize N eta : ℝ) /
            Real.log (N : ℝ))) *
        Real.log (N : ℝ) := by
          field_simp [ne_of_gt hlog]
    _ ≤ eta * Real.log (N : ℝ) := hmul

theorem expandedAnnularOccurrenceParityBox_lt_ambient
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (_heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    (N : ℕ) (z : GaussPrefixMixedOccurrence k) (q : ℕ)
    (hq : q ∈ mixedOccurrenceParityBox
      (expandedAnnularOccurrenceDepthBoxes N eta k)
      (annularOccurrenceParity k) z) :
    q < expandedAnnularDepthAmbientSize N eta := by
  have hqRaw :
      q ∈ expandedAnnularTimeDepthBox N eta z.1 :=
    (Finset.mem_filter.mp hq).1
  have hqUpper :
      q < gaussLogDepthEndpoint N
        (intervalGridPoint 0 1 grid (z.1.time.1 + 1) + eta) :=
    (Finset.mem_Ico.mp hqRaw).2
  have hzActive : 0 < k z.1 := by
    have hz := z.2.isLt
    omega
  have hindex : z.1.time.1 + 1 ≤ grid :=
    Nat.succ_le_iff.mpr (htime z.1 hzActive)
  have hpoint :
      intervalGridPoint 0 1 grid (z.1.time.1 + 1) ≤ 1 :=
    (intervalGridPoint_mem_Icc zero_le_one hgrid hindex).2
  have hrounded :
      gaussLogDepthEndpoint N
          (intervalGridPoint 0 1 grid (z.1.time.1 + 1) + eta) ≤
        gaussLogDepthEndpoint N (1 + eta) := by
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith)
        (Real.log_natCast_nonneg N))
      gaussRoofMean_pos.le
  unfold expandedAnnularDepthAmbientSize
  omega

theorem contractedAnnularOccurrenceParityBox_lt_ambient
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    (N : ℕ) (z : GaussPrefixMixedOccurrence k) (q : ℕ)
    (hq : q ∈ mixedOccurrenceParityBox
      (contractedAnnularOccurrenceDepthBoxes N eta k)
      (annularOccurrenceParity k) z) :
    q < expandedAnnularDepthAmbientSize N eta := by
  have hqRaw :
      q ∈ contractedAnnularTimeDepthBox N eta z.1 :=
    (Finset.mem_filter.mp hq).1
  have hqExpanded :
      q ∈ expandedAnnularTimeDepthBox N eta z.1 :=
    annularOccurrenceDepthBoxes_subset_expanded
      heta z
      (contractedAnnularTimeDepthBox_subset_annularOccurrenceDepthBoxes
        heta z hqRaw)
  have hqParity :
      q % 2 = (annularOccurrenceParity k z).1 :=
    (Finset.mem_filter.mp hq).2
  exact expandedAnnularOccurrenceParityBox_lt_ambient
    hgrid heta k htime N z q
    (Finset.mem_filter.mpr ⟨hqExpanded, hqParity⟩)

theorem tendsto_aggregate_expandedCanonicalAnnularGridTupleFamily_density
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦
            expandedCanonicalAnnularGridTupleFamily N eta k e) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop
      (nhds (expandedAnnularOccurrenceTimeDensity eta k)) := by
  let boxes :
      ℕ → GaussPrefixMixedOccurrence k → Finset ℕ :=
    fun N ↦ expandedAnnularOccurrenceDepthBoxes N eta k
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ z q,
      q ∈ mixedOccurrenceParityBox (boxes N)
          (annularOccurrenceParity k) z →
        q < expandedAnnularDepthAmbientSize N eta :=
    Eventually.of_forall fun N z q hq ↦
      expandedAnnularOccurrenceParityBox_lt_ambient
        hgrid heta k htime N z q hq
  have hcutoff : ∀ᶠ N : ℕ in atTop, ∀ z q,
      q ∈ mixedOccurrenceParityBox (boxes N)
          (annularOccurrenceParity k) z → q ≤ N := by
    filter_upwards
      [eventually_expandedAnnularDepthAmbientSize_le_nat heta] with
      N hHN
    intro z q hq
    exact (expandedAnnularOccurrenceParityBox_lt_ambient
      hgrid heta k htime N z q hq).le.trans hHN
  simpa only [boxes, expandedCanonicalAnnularGridTupleFamily,
    expandedAnnularOccurrenceDepthBoxes] using!
    tendsto_aggregate_card_canonicalMixedOrderParityBoxTimes
      hr boxes (annularOccurrenceParity k)
      (expandedAnnularOccurrenceTimeDensity eta k)
      (tendsto_expandedAnnularOccurrenceParityAssignmentBox_density
        hgrid heta k)
      (fun N ↦ expandedAnnularDepthAmbientSize N eta)
      (tendsto_expandedAnnularDepthAmbientSize_div_log heta)
      hbound hcutoff

theorem tendsto_aggregate_contractedCanonicalAnnularGridTupleFamily_density
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (hetaWidth : 2 * eta ≤ 1 / (grid : ℝ))
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦
            contractedCanonicalAnnularGridTupleFamily N eta k e) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop
      (nhds (contractedAnnularOccurrenceTimeDensity eta k)) := by
  let boxes :
      ℕ → GaussPrefixMixedOccurrence k → Finset ℕ :=
    fun N ↦ contractedAnnularOccurrenceDepthBoxes N eta k
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ z q,
      q ∈ mixedOccurrenceParityBox (boxes N)
          (annularOccurrenceParity k) z →
        q < expandedAnnularDepthAmbientSize N eta :=
    Eventually.of_forall fun N z q hq ↦
      contractedAnnularOccurrenceParityBox_lt_ambient
        hgrid heta k htime N z q hq
  have hcutoff : ∀ᶠ N : ℕ in atTop, ∀ z q,
      q ∈ mixedOccurrenceParityBox (boxes N)
          (annularOccurrenceParity k) z → q ≤ N := by
    filter_upwards
      [eventually_expandedAnnularDepthAmbientSize_le_nat heta] with
      N hHN
    intro z q hq
    exact (contractedAnnularOccurrenceParityBox_lt_ambient
      hgrid heta k htime N z q hq).le.trans hHN
  simpa only [boxes, contractedCanonicalAnnularGridTupleFamily,
    contractedAnnularOccurrenceDepthBoxes] using!
    tendsto_aggregate_card_canonicalMixedOrderParityBoxTimes
      hr boxes (annularOccurrenceParity k)
      (contractedAnnularOccurrenceTimeDensity eta k)
      (tendsto_contractedAnnularOccurrenceParityAssignmentBox_density
        hgrid hetaWidth k)
      (fun N ↦ expandedAnnularDepthAmbientSize N eta)
      (tendsto_expandedAnnularDepthAmbientSize_div_log heta)
      hbound hcutoff

theorem aggregate_timeBoundary_add_contracted_card_eq_expanded
    {grid N : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ) :
    aggregateTupleFamilyCard
        (fun e ↦ annularCanonicalTimeBoundaryTupleFamily N eta k e) +
      aggregateTupleFamilyCard
        (fun e ↦ contractedCanonicalAnnularGridTupleFamily N eta k e) =
      aggregateTupleFamilyCard
        (fun e ↦ expandedCanonicalAnnularGridTupleFamily N eta k e) := by
  unfold aggregateTupleFamilyCard
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  exact Finset.card_sdiff_add_card_eq_card
    (contractedCanonicalAnnularGridTupleFamily_subset_expanded
      heta k e)

theorem tendsto_aggregate_annularCanonicalTimeBoundaryTupleFamily_density
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (hetaWidth : 2 * eta ≤ 1 / (grid : ℝ))
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateTupleFamilyCard
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop
      (nhds
        (expandedAnnularOccurrenceTimeDensity eta k -
          contractedAnnularOccurrenceTimeDensity eta k)) := by
  have hexpanded :=
    tendsto_aggregate_expandedCanonicalAnnularGridTupleFamily_density
      hgrid heta k hr htime
  have hcontracted :=
    tendsto_aggregate_contractedCanonicalAnnularGridTupleFamily_density
      hgrid heta hetaWidth k hr htime
  have hsub := hexpanded.sub hcontracted
  apply hsub.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  have hcardNat :=
    aggregate_timeBoundary_add_contracted_card_eq_expanded
      (N := N) heta k
  have hcardReal :
      (aggregateTupleFamilyCard
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e) : ℝ) +
        (aggregateTupleFamilyCard
          (fun e ↦
            contractedCanonicalAnnularGridTupleFamily N eta k e) : ℝ) =
        (aggregateTupleFamilyCard
          (fun e ↦
            expandedCanonicalAnnularGridTupleFamily N eta k e) : ℝ) := by
    exact_mod_cast hcardNat
  rw [← hcardReal]
  field_simp [ne_of_gt hlog]
  ring

/-! ## Short-gap density for the shifted boundary family -/

theorem tendsto_aggregateShortTupleFamilyCard_density_zero_of_bounded
    {r : ℕ} (hr : 0 < r)
    {β : Type*} [Fintype β]
    (gap : ℕ → ℕ)
    (hgapRatio :
      Tendsto
        (fun N ↦ (gap N : ℝ) / Real.log (N : ℝ))
        atTop (nhds 0))
    (tuples : ℕ → β → Finset (Fin r → ℕ))
    (H : ℕ → ℕ) {ambientLimit : ℝ}
    (hH :
      Tendsto
        (fun N ↦ (H N : ℝ) / Real.log (N : ℝ))
        atTop (nhds ambientLimit))
    (hchronological : ∀ N b, ∀ t ∈ tuples N b,
      IsChronologicalNatTuple t)
    (hbound : ∀ N b, ∀ t ∈ tuples N b, ∀ i, t i < H N) :
    Tendsto
      (fun N ↦
        (aggregateShortTupleFamilyCard
          (gap := gap N) (tuples N) : ℝ) /
            Real.log (N : ℝ) ^ r)
      atTop (nhds 0) := by
  let C : ℕ := Fintype.card β * r * r
  let upper : ℕ → ℝ := fun N ↦
    (C : ℝ) *
      ((gap N : ℝ) / Real.log (N : ℝ)) *
      (((H N : ℝ) / Real.log (N : ℝ)) ^ (r - 1))
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hraw :=
      ((tendsto_const_nhds : Tendsto
        (fun _N : ℕ ↦ (C : ℝ)) atTop (nhds (C : ℝ))).mul
          hgapRatio).mul (hH.pow (r - 1))
    simpa only [upper, mul_zero, zero_mul] using! hraw
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by positivity
  · filter_upwards
      [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
    have hcardNat :
        aggregateShortTupleFamilyCard
            (gap := gap N) (tuples N) ≤
          Fintype.card β *
            (r * r * (gap N * H N ^ (r - 1))) := by
      unfold aggregateShortTupleFamilyCard
      calc
        ∑ b : β, (shortNatTupleFamily
            (gap N) (tuples N b)).card ≤
          ∑ _b : β, r * r * (gap N * H N ^ (r - 1)) := by
            apply Finset.sum_le_sum
            intro b _hb
            exact card_shortNatTupleFamily_le_of_bounded
              (hchronological N b)
              (hbound N b)
        _ = _ := by simp
    have hcardReal :
        (aggregateShortTupleFamilyCard
            (gap := gap N) (tuples N) : ℝ) ≤
          (C : ℝ) * (gap N : ℝ) *
            (H N : ℝ) ^ (r - 1) := by
      have hcast :
          (aggregateShortTupleFamilyCard
              (gap := gap N) (tuples N) : ℝ) ≤
            ((Fintype.card β *
              (r * r * (gap N * H N ^ (r - 1))) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcardNat
      simpa only [C, Nat.cast_mul, Nat.cast_pow, mul_assoc] using! hcast
    have hdiv := div_le_div_of_nonneg_right hcardReal
      (pow_nonneg hlog.le r)
    calc
      (aggregateShortTupleFamilyCard
          (gap := gap N) (tuples N) : ℝ) /
          Real.log (N : ℝ) ^ r ≤
        ((C : ℝ) * (gap N : ℝ) *
            (H N : ℝ) ^ (r - 1)) /
          Real.log (N : ℝ) ^ r := hdiv
      _ = upper N := by
        have hpow :
            Real.log (N : ℝ) ^ r =
              Real.log (N : ℝ) ^ (r - 1) *
                Real.log (N : ℝ) := by
          conv_lhs => rw [show r = (r - 1) + 1 by omega]
          exact pow_succ _ _
        dsimp only [upper]
        rw [hpow, div_pow]
        field_simp [ne_of_gt hlog]
  · exact hupper

theorem annularCanonicalTimeBoundaryTupleFamily_lt_ambient
    {grid N : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ annularCanonicalTimeBoundaryTupleFamily N eta k e)
    (j : Fin (MixedOccurrenceCount k)) :
    t j < expandedAnnularDepthAmbientSize N eta := by
  have htExpanded :=
    (mem_annularCanonicalTimeBoundaryTupleFamily_iff.mp ht).1
  obtain ⟨F, _horder, hbox, hFt⟩ :=
    mem_canonicalMixedOrderParityBoxTimes_iff.mp htExpanded
  have hj :
      t j ∈ mixedOccurrenceParityBox
        (expandedAnnularOccurrenceDepthBoxes N eta k)
        (annularOccurrenceParity k) (e j) := by
    rw [← hFt]
    exact Finset.mem_filter.mpr ⟨(hbox j).1, (hbox j).2⟩
  exact expandedAnnularOccurrenceParityBox_lt_ambient
    hgrid heta k htime N (e j) (t j) hj

theorem
    tendsto_aggregateShort_annularCanonicalTimeBoundaryTupleFamily_density_zero
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (aggregateShortTupleFamilyCard
          (gap := annularSeparationGap N)
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e) : ℝ) /
          Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
  exact
    tendsto_aggregateShortTupleFamilyCard_density_zero_of_bounded
      hr annularSeparationGap
      tendsto_annularSeparationGap_div_log_zero
      (fun N e ↦
        annularCanonicalTimeBoundaryTupleFamily N eta k e)
      (fun N ↦ expandedAnnularDepthAmbientSize N eta)
      (tendsto_expandedAnnularDepthAmbientSize_div_log heta)
      (fun N e t ht ↦
        annularCanonicalTimeBoundaryTupleFamily_chronological
          k e t ht)
      (fun N e t ht j ↦
        annularCanonicalTimeBoundaryTupleFamily_lt_ambient
          hgrid heta k htime e t ht j)

/-! ## Boundary mass and the explicit order of limits -/

theorem
    tendsto_aggregateGauss_annularCanonicalTimeBoundaryTupleFamily_mass
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid) {eta : ℝ}
    (heta : 0 ≤ eta)
    (hetaWidth : 2 * eta ≤ 1 / (grid : ℝ))
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        aggregateGaussMovingSignedApproximationTupleSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily N eta k e))
      atTop
      (nhds
        ((expandedAnnularOccurrenceTimeDensity eta k -
            contractedAnnularOccurrenceTimeDensity eta k) *
          annularOccurrenceSignedDensity ε A k)) := by
  exact
    tendsto_aggregateGaussMovingSignedApproximationTupleSum
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (A := A)
      (density :=
        expandedAnnularOccurrenceTimeDensity eta k -
          contractedAnnularOccurrenceTimeDensity eta k)
      (common := annularOccurrenceSignedDensity ε A k)
      hr (fun N ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦ flattenedAnnularParity e)
      (hε.le.trans hεA.le)
      (fun e j ↦
        flattenedAnnular_oriented_lower_pos
          hε hεA hgrid hsigned e j)
      (fun e j ↦
        flattenedAnnular_oriented_lower_lt_upper
          hεA hgrid e j)
      (fun e j ↦
        flattenedAnnular_oriented_upper_le
          hεA hgrid hsigned e j)
      (flattenedAnnular_oriented_product_eq ε A)
      annularSeparationGap
      tendsto_annularSeparationGap_atTop
      (tendsto_annularSeparationGap_atTop.eventually_gt_atTop 0)
      (fun N e ↦
        annularCanonicalTimeBoundaryTupleFamily N eta k e)
      (fun N e t ht ↦
        annularCanonicalTimeBoundaryTupleFamily_chronological
          k e t ht)
      (fun N e t ht j ↦
        annularCanonicalTimeBoundaryTupleFamily_parity
          k e t ht j)
      (tendsto_aggregate_annularCanonicalTimeBoundaryTupleFamily_density
        hgrid heta hetaWidth k hr htime)
      (tendsto_aggregateShort_annularCanonicalTimeBoundaryTupleFamily_density_zero
        hgrid heta k hr htime)

theorem tendsto_annularTimeBoundaryDensity_zero
    {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    Tendsto
      (fun eta ↦
        expandedAnnularOccurrenceTimeDensity eta k -
          contractedAnnularOccurrenceTimeDensity eta k)
      (nhds 0) (nhds 0) := by
  have hexpanded :
      Continuous
        (fun eta ↦ expandedAnnularOccurrenceTimeDensity eta k) := by
    unfold expandedAnnularOccurrenceTimeDensity
      expandedAnnularTimeDensityFactor
    fun_prop
  have hcontracted :
      Continuous
        (fun eta ↦ contractedAnnularOccurrenceTimeDensity eta k) := by
    unfold contractedAnnularOccurrenceTimeDensity
      contractedAnnularTimeDensityFactor
    fun_prop
  have hsub :
      ContinuousAt
        (fun eta ↦
          expandedAnnularOccurrenceTimeDensity eta k -
            contractedAnnularOccurrenceTimeDensity eta k) 0 :=
    hexpanded.continuousAt.sub hcontracted.continuousAt
  have hzero :
      expandedAnnularOccurrenceTimeDensity 0 k -
          contractedAnnularOccurrenceTimeDensity 0 k = 0 := by
    simp only [expandedAnnularOccurrenceTimeDensity,
      contractedAnnularOccurrenceTimeDensity,
      expandedAnnularTimeDensityFactor,
      contractedAnnularTimeDensityFactor, add_zero, sub_zero,
      sub_self]
  change
    Tendsto
      (fun eta ↦
        expandedAnnularOccurrenceTimeDensity eta k -
          contractedAnnularOccurrenceTimeDensity eta k)
      (nhds 0)
      (nhds
        (expandedAnnularOccurrenceTimeDensity 0 k -
          contractedAnnularOccurrenceTimeDensity 0 k)) at hsub
  rw [hzero] at hsub
  exact hsub

/-- Explicit iterated removal of the time-boundary strip: first
`N → ∞` for the fixed width `eta_m = 1/(m+1)`, and only then
`m → ∞` (equivalently `eta_m ↓ 0`). -/
theorem
    eventually_eventually_aggregateUniform_annularTimeBoundary_mass_lt
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      ∀ᶠ N : ℕ in atTop,
        aggregateUniformMovingSignedApproximationTupleMassSum
          (β := Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k)
          (Real.log (N : ℝ))
          (fun e ↦ flattenedAnnularSignedLower ε A e)
          (fun e ↦ flattenedAnnularSignedUpper ε A e)
          (fun e ↦
            annularCanonicalTimeBoundaryTupleFamily
              N (1 / ((m : ℝ) + 1)) k e) < delta := by
  let eta : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  let density : ℝ → ℝ := fun u ↦
    expandedAnnularOccurrenceTimeDensity u k -
      contractedAnnularOccurrenceTimeDensity u k
  let signedDensity := annularOccurrenceSignedDensity ε A k
  let K : ℝ := 2 * Real.log 2
  have hetaZero : Tendsto eta atTop (nhds 0) := by
    simpa only [eta] using!
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlimit :
      Tendsto
        (fun m ↦ K * (density (eta m) * signedDensity))
        atTop (nhds 0) := by
    have hdensity :
        Tendsto (fun m ↦ density (eta m)) atTop (nhds 0) :=
      (tendsto_annularTimeBoundaryDensity_zero k).comp hetaZero
    have hmul :=
      ((tendsto_const_nhds : Tendsto
        (fun _m : ℕ ↦ K) atTop (nhds K)).mul
        (hdensity.mul_const signedDensity))
    simpa only [zero_mul, mul_zero] using! hmul
  have hwidth :
      ∀ᶠ m : ℕ in atTop,
        2 * eta m ≤ 1 / (grid : ℝ) := by
    have htwo :
        Tendsto (fun m ↦ 2 * eta m) atTop (nhds 0) := by
      simpa only [mul_zero] using! hetaZero.const_mul 2
    have hright : 0 < 1 / (grid : ℝ) := by positivity
    filter_upwards [htwo.eventually_lt_const hright] with m hm
    exact hm.le
  filter_upwards
    [hwidth, hlimit.eventually_lt_const hdelta] with
      m hmWidth hmLimit
  have hetaNonneg : 0 ≤ eta m := by
    dsimp only [eta]
    positivity
  have hgauss :=
    tendsto_aggregateGauss_annularCanonicalTimeBoundaryTupleFamily_mass
      hε hεA hgrid hetaNonneg hmWidth k hr htime hsigned
  have hgaussScaled :
      Tendsto
        (fun N : ℕ ↦ K *
          aggregateGaussMovingSignedApproximationTupleSum
            (β := Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k)
            (Real.log (N : ℝ))
            (fun e ↦ flattenedAnnularSignedLower ε A e)
            (fun e ↦ flattenedAnnularSignedUpper ε A e)
            (fun e ↦
              annularCanonicalTimeBoundaryTupleFamily
                N (eta m) k e))
        atTop
        (nhds (K * (density (eta m) * signedDensity))) := by
    simpa only [K, density, signedDensity] using! hgauss.const_mul K
  filter_upwards
    [hgaussScaled.eventually_lt_const hmLimit] with N hN
  exact lt_of_le_of_lt
    (aggregateUniformMovingSignedApproximationTupleMassSum_le_gauss
      (Real.log (N : ℝ))
      (fun e ↦ flattenedAnnularSignedLower ε A e)
      (fun e ↦ flattenedAnnularSignedUpper ε A e)
      (fun e ↦
        annularCanonicalTimeBoundaryTupleFamily
          N (eta m) k e))
    (by simpa only [K, eta] using! hN)

/-! ## Exact finite coefficient control by positive boundary mass -/

/-! ## Exact scalar expansion of the literal factorial moment -/

/-- The simultaneous literal annular event attached to one globally
injective labeled depth tuple.  Keeping this event in the original labeled
coordinates avoids any implicit identification of logarithmic denominator
time with deterministic continued-fraction depth. -/
def gaussPrefixAnnularLiteralMixedTupleEvent
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (F : GloballyInjectiveMixedDepthTuple N k) : Set ℝ :=
  mixedTupleEvent
    (fun i ↦ gaussPrefixMarkedEvent N (annularGridCell ε A grid i))
    F.1

theorem measurableSet_gaussPrefixAnnularLiteralMixedTupleEvent
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (F : GloballyInjectiveMixedDepthTuple N k) :
    MeasurableSet
      (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F) := by
  apply measurableSet_mixedTupleEvent
  intro i q _hq
  exact measurableSet_gaussPrefixMarkedEvent N q
    (measurableSet_annularGridCell ε A grid i)

/-- The mixed factorial moment is exactly the finite sum of literal tuple
masses, partitioned by the unique chronological order of every globally
injective labeled tuple.  This is an identity at finite `N`. -/
theorem mixedFactorialMoment_gaussPrefixAnnular_eq_orderedLiteralMass
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (N : ℕ) (k : AnnularGridIndex grid → ℕ) :
    mixedFactorialMoment
        (gaussPrefixMarkedCountVectorLaw N
          (annularGridCell ε A grid)
          (fun i ↦ measurableSet_annularGridCell ε A grid i))
        k =
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        ∑ F ∈ canonicalMixedOrderClass N k e,
          uniform01Measure.real
            (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F) := by
  classical
  apply Complex.ofReal_injective
  rw [← gaussPrefixMarkedMixedFourierCoefficient_zero
    N (annularGridCell ε A grid)
      (fun i ↦ measurableSet_annularGridCell ε A grid i) k]
  rw [gaussPrefixMarkedMixedFourierCoefficient_annularGrid_eq_orders
    hε hεA hgrid N k (fun _i _j ↦ 0)]
  push_cast
  apply Finset.sum_congr rfl
  intro e _he
  apply Finset.sum_congr rfl
  intro F _hF
  rw [show
      gaussPrefixMarkedMixedTupleCharacter
          N (annularGridCell ε A grid) k (fun _i _j ↦ 0) F.1 =
        (gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F).indicator
          (fun _x ↦ (1 : ℂ)) by
      funext x
      exact gaussPrefixMarkedMixedTupleCharacter_zero
        N (annularGridCell ε A grid) k F.1 x]
  rw [MeasureTheory.integral_indicator_const (1 : ℂ)
    (measurableSet_gaussPrefixAnnularLiteralMixedTupleEvent
      ε A N k F)]
  simp

/-! ## Coordinatewise literal/canonical event bridge -/

/-- On the nonterminating full-measure set, a literal labeled tuple event
exposes all of the coordinates needed by the canonical chronological
description.  In particular this theorem records the selected-denominator
carrier and derives, rather than assumes, the parity restriction. -/
theorem coordinates_of_mem_gaussPrefixAnnularLiteralMixedTupleEvent
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    {N : ℕ} (hlog : 0 < Real.log (N : ℝ))
    (k : AnnularGridIndex grid → ℕ)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx :
      x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F) :
    gaussPrefixAnnularLiteralTimeCondition
        (N := N) e (fixedOrderMixedTimes N k e F) x ∧
      x ∈ gaussSignedApproximationTupleEventIco
        (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (fixedOrderMixedTimes N k e F) ∧
      (∀ j : Fin (MixedOccurrenceCount k),
        gaussSelectedPrefixTorusMark N
            (fixedOrderMixedTimes N k e F j) x ∈
          intervalGridCell 0 1 grid (e j).1.torus) ∧
      (∀ j : Fin (MixedOccurrenceCount k),
        cfTerminalDenominator
              (selectedGaussPrefixWord
                (fixedOrderMixedTimes N k e F j) x).1 ≤ N ∧
          gaussApproximationCoordinate
              (fixedOrderMixedTimes N k e F j) x < (1 : ℝ) / 2) ∧
      (∀ j : Fin (MixedOccurrenceCount k),
        fixedOrderMixedTimes N k e F j % 2 =
          (annularGridDepthParity (e j).1).1) := by
  have hall :
      ∀ z : GaussPrefixMixedOccurrence k,
        x ∈ gaussPrefixMarkedEvent N
          (annularGridCell ε A grid z.1)
          (F.1 z.1 z.2) := by
    intro z
    have hi :=
      Set.mem_iInter.mp
        (show x ∈ mixedTupleEvent
          (fun i ↦ gaussPrefixMarkedEvent N
            (annularGridCell ε A grid i)) F.1 from hx) z.1
    exact Set.mem_iInter.mp hi z.2
  have hdata (j : Fin (MixedOccurrenceCount k)) :=
    selectedGaussPrefixWord_data_of_mem (hall (e j))
  have hactive (j : Fin (MixedOccurrenceCount k)) :
      0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have hpoint (j : Fin (MixedOccurrenceCount k)) :
      gaussPrefixMarkedPoint N
          (fixedOrderMixedTimes N k e F j)
          (selectedGaussPrefixWord
            (fixedOrderMixedTimes N k e F j) x) x ∈
        annularGridCell ε A grid (e j).1 := by
    simpa only [fixedOrderMixedTimes] using! (hdata j).2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hj := (hpoint j).1
    simpa only [gaussPrefixLogDenominatorTime,
      gaussPrefixDenominator, gaussPrefixMarkedPoint] using! hj
  · unfold gaussSignedApproximationTupleEventIco
    rw [mem_orderedEventIntersection_ofFn_iff]
    intro j
    constructor
    · exact ⟨hxUnit.1, hxUnit.2.le⟩
    · have hj := (hpoint j).2.1
      unfold annularGridCell at hj
      unfold intervalGridCell at hj
      rw [if_pos (hsigned (e j).1 (hactive j))] at hj
      rw [gaussPrefixMarkedPoint_value_eq_signedScaledApproximation] at hj
      simpa only [Set.mem_preimage, flattenedAnnularSignedLower,
        flattenedAnnularSignedUpper] using! hj
  · intro j
    have hj := (hpoint j).2.2
    simpa only [gaussSelectedPrefixTorusMark,
      fixedOrderMixedTimes] using! hj
  · intro j
    have hj := hdata j
    simpa only [fixedOrderMixedTimes] using!
      And.intro hj.2.1 hj.2.2.1
  · intro j
    have hj := (hpoint j).2.1
    unfold annularGridCell at hj
    rw [gaussPrefixMarkedPoint_value_eq_signedScaledApproximation] at hj
    exact depth_parity_eq_annularGridDepthParity_of_signed_mem
      hε hεA hgrid (e j).1
      (hsigned (e j).1 (hactive j)) hlog hxUnit hxNonterm
      (by simpa only [fixedOrderMixedTimes] using! hj)

/-- On the denominator good event, a literal tuple belongs to the expanded
canonical source and its point belongs to the corresponding canonical
closed signed-and-torus event.  This is the upper half of the finite
sandwich, stated before integration. -/
theorem
    expandedSource_and_canonicalEvent_of_literalEvent_on_good
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid N L C : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    {Delta eta : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (htorus : ∀ i, 0 < k i → i.torus.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (hForder : F ∈ canonicalMixedOrderClass N k e)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hbound : ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hxLiteral :
      x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F) :
    F ∈ expandedAnnularCanonicalOrderSource N eta k e ∧
      x ∈ canonicalAnnularSignedTorusTupleEvent ε A N e
        (fixedOrderMixedTimes N k e F) := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hcoord :=
    coordinates_of_mem_gaussPrefixAnnularLiteralMixedTupleEvent
      hε hεA hgrid hlog k hsigned e F hxUnit hxNonterm hxLiteral
  have hExpandedTime :
      gaussPrefixAnnularExpandedTimeCondition
        (N := N) eta e (fixedOrderMixedTimes N k e F) :=
    expandedTimeCondition_of_literal_on_good
      e (fixedOrderMixedTimes N k e F) htime hlog hxGood
      hbound hmargin hcoord.1
  have hsignedClosed :
      x ∈ gaussSignedApproximationTupleEvent
        (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (fixedOrderMixedTimes N k e F) := by
    have hsignedIco := hcoord.2.1
    unfold gaussSignedApproximationTupleEventIco at hsignedIco
    unfold gaussSignedApproximationTupleEvent
    rw [mem_orderedEventIntersection_ofFn_iff] at hsignedIco ⊢
    intro j
    have hj := hsignedIco j
    exact ⟨hj.1, hj.2.1, hj.2.2.le⟩
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨hForder, ?_⟩
    intro j
    exact ⟨hExpandedTime j, hcoord.2.2.2.2 j⟩
  · exact
      (mem_canonicalAnnularSignedTorusTupleEvent_iff_real_cells
        hgrid htorus e (fixedOrderMixedTimes N k e F) x).mpr
        ⟨hsignedClosed, hcoord.2.2.1⟩

/-- Removing a subfamily changes a marked Fourier coefficient by at most
the positive unmarked mass of the finset difference.  This elementary
finite lemma is the safe replacement for an unjustified equality of
complex coefficients. -/
theorem norm_movingSignedMarkedFourierTupleSum_sub_le_sdiff_mass
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (mode : Fin r → ℤ)
    (small large : Finset (Fin r → ℕ))
    (hsubset : small ⊆ large) :
    ‖movingSignedMarkedFourierTupleSum
          mu N scale lower upper mode large -
        movingSignedMarkedFourierTupleSum
          mu N scale lower upper mode small‖ ≤
      movingSignedApproximationTupleMassSum
        mu scale lower upper (large \ small) := by
  have hdifference :
      movingSignedMarkedFourierTupleSum
          mu N scale lower upper mode large -
        movingSignedMarkedFourierTupleSum
          mu N scale lower upper mode small =
        movingSignedMarkedFourierTupleSum
          mu N scale lower upper mode (large \ small) := by
    unfold movingSignedMarkedFourierTupleSum
    exact (Finset.sum_sdiff_eq_sub hsubset).symm
  rw [hdifference]
  exact norm_movingSignedMarkedFourierTupleSum_le_mass
    mu N scale lower upper mode (large \ small)

set_option maxHeartbeats 4000000

/-- The canonical coefficient and its contracted version differ by no
more than the explicit expanded-minus-contracted boundary mass. -/
theorem norm_canonical_sub_contracted_le_timeBoundary_mass
    {ε A : ℝ} {grid N : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ) :
    ‖uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode (canonicalAnnularGridTupleFamily N k e) -
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (contractedCanonicalAnnularGridTupleFamily N eta k e)‖ ≤
      movingSignedApproximationTupleMassSum
        uniform01Measure (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
  have hcontracted :
      contractedCanonicalAnnularGridTupleFamily N eta k e ⊆
        canonicalAnnularGridTupleFamily N k e :=
    contractedCanonicalAnnularGridTupleFamily_subset_canonical
      heta k e
  have hcanonical :
      canonicalAnnularGridTupleFamily N k e ⊆
        expandedCanonicalAnnularGridTupleFamily N eta k e :=
    canonicalAnnularGridTupleFamily_subset_expanded heta k e
  calc
    _ ≤ movingSignedApproximationTupleMassSum
          uniform01Measure (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (canonicalAnnularGridTupleFamily N k e \
            contractedCanonicalAnnularGridTupleFamily N eta k e) :=
      norm_movingSignedMarkedFourierTupleSum_sub_le_sdiff_mass
        uniform01Measure N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e) mode
        (contractedCanonicalAnnularGridTupleFamily N eta k e)
        (canonicalAnnularGridTupleFamily N k e) hcontracted
    _ ≤ movingSignedApproximationTupleMassSum
          uniform01Measure (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          (annularCanonicalTimeBoundaryTupleFamily N eta k e) := by
      unfold movingSignedApproximationTupleMassSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        rw [Finset.mem_sdiff] at ht
        exact mem_annularCanonicalTimeBoundaryTupleFamily_iff.mpr
          ⟨hcanonical ht.1, fun hcontra ↦ ht.2
            hcontra⟩
      · intro _t _ht _hnot
        positivity

end

end Erdos1002
