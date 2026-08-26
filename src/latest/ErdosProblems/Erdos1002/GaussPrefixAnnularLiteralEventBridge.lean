import ErdosProblems.Erdos1002.GaussPrefixAnnularLiteralTransfer
import ErdosProblems.Erdos1002.GaussPrefixAnnularSignedEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Coordinatewise form of the literal annular prefix event

This file makes explicit the event identification used in the
literal-to-canonical comparison.  On the full-measure set of nonterminating
Gauss orbits, the existential positive word in each literal marked event is
the selected word.  Thus the literal mixed event is exactly the conjunction
of its denominator cutoff, Legendre cutoff, logarithmic-time cell, half-open
signed cell, and real torus cell.

We also prove, rather than infer informally from the sign, that membership
of a signed annular cell forces the prescribed parity of the prefix depth.
-/

open MeasureTheory Set

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularLiteralEventBridgePropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

/-- The signed coordinate of a nonterminating prefix has the parity sign
prescribed by its positive or negative annular cell. -/
theorem depth_mod_two_eq_annularGridDepthParity_of_signedCell
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid)
    {scale : ℝ} (hscale : 0 < scale)
    {n : ℕ} {theta : ℝ} (htheta : 0 < theta)
    (hcell :
      (-1 : ℝ) ^ n * (scale * theta) ∈
        intervalGridCell
          (signedGridLower ε A i.sign)
          (signedGridUpper ε A i.sign)
          grid i.signed) :
    n % 2 = (annularGridDepthParity i).1 := by
  have hbounds :=
    intervalGridCell_subset_Icc
      (signedGridLower_lt_upper hεA i.sign) hgrid i.signed hcell
  have hprod : 0 < scale * theta := mul_pos hscale htheta
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · have hpow : (-1 : ℝ) ^ n = 1 := hnEven.neg_one_pow
    cases hi : i.sign with
    | false =>
        have hnegative :
            (-1 : ℝ) ^ n * (scale * theta) ≤ -ε := by
          simpa only [signedGridUpper, hi, Bool.false_eq_true, if_false]
            using! hbounds.2
        rw [hpow, one_mul] at hnegative
        exfalso
        linarith
    | true =>
        simp [annularGridDepthParity, hi,
          Nat.even_iff.mp hnEven]
  · have hpow : (-1 : ℝ) ^ n = -1 := hnOdd.neg_one_pow
    cases hi : i.sign with
    | false =>
        simp [annularGridDepthParity, hi,
          Nat.odd_iff.mp hnOdd]
    | true =>
        have hpositive :
            ε ≤ (-1 : ℝ) ^ n * (scale * theta) := by
          simpa only [signedGridLower, hi, ↓reduceIte] using! hbounds.1
        rw [hpow, neg_one_mul] at hpositive
        exfalso
        linarith

/-- On a nonterminating point, the literal mixed tuple event is exactly its
five coordinatewise conditions in chronological order.

The signed and torus conditions use the original half-open real grid cells.
No quotient-circle or closed-endpoint replacement occurs in this theorem. -/
theorem
    mem_gaussPrefixAnnularLiteralMixedTupleEvent_iff_coordinates
    {ε A : ℝ} {N grid : ℕ}
    {k : AnnularGridIndex grid → ℕ}
    (F : GloballyInjectiveMixedDepthTuple N k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    {x : ℝ}
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0) :
    x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F ↔
      ∀ j : Fin (MixedOccurrenceCount k),
        cfTerminalDenominator
            (selectedGaussPrefixWord
              (fixedOrderMixedTimes N k e F j) x).1 ≤ N ∧
          gaussApproximationCoordinate
              (fixedOrderMixedTimes N k e F j) x < (1 : ℝ) / 2 ∧
          Real.log
                (cfTerminalDenominator
                  (selectedGaussPrefixWord
                    (fixedOrderMixedTimes N k e F j) x).1 : ℝ) /
              Real.log (N : ℝ) ∈
            intervalGridCell 0 1 grid (e j).1.time ∧
          gaussSignedScaledApproximationCoordinate
              (Real.log (N : ℝ))
              (fixedOrderMixedTimes N k e F j) x ∈
            intervalGridCell
              (signedGridLower ε A (e j).1.sign)
              (signedGridUpper ε A (e j).1.sign)
              grid (e j).1.signed ∧
          gaussSelectedPrefixTorusMark N
              (fixedOrderMixedTimes N k e F j) x ∈
            intervalGridCell 0 1 grid (e j).1.torus := by
  constructor
  · intro hxEvent j
    have hxLabeled :
        x ∈ gaussPrefixMarkedEvent N
            (annularGridCell ε A grid (e j).1)
            (fixedOrderMixedTimes N k e F j) := by
      have hlabel :=
        Set.mem_iInter.mp
          (Set.mem_iInter.mp hxEvent (e j).1) (e j).2
      simpa only [gaussPrefixAnnularLiteralMixedTupleEvent,
        mixedTupleEvent, tupleEvent, fixedOrderMixedTimes] using! hlabel
    rcases selectedGaussPrefixWord_data_of_mem hxLabeled with
      ⟨_hcylinder, hden, htheta, hpoint⟩
    change
      (gaussPrefixMarkedPoint N
          (fixedOrderMixedTimes N k e F j)
          (selectedGaussPrefixWord
            (fixedOrderMixedTimes N k e F j) x) x).1 ∈
          intervalGridCell 0 1 grid (e j).1.time ∧
        (gaussPrefixMarkedPoint N
          (fixedOrderMixedTimes N k e F j)
          (selectedGaussPrefixWord
            (fixedOrderMixedTimes N k e F j) x) x).2.1 ∈
          intervalGridCell
            (signedGridLower ε A (e j).1.sign)
            (signedGridUpper ε A (e j).1.sign)
            grid (e j).1.signed ∧
        (gaussPrefixMarkedPoint N
          (fixedOrderMixedTimes N k e F j)
          (selectedGaussPrefixWord
            (fixedOrderMixedTimes N k e F j) x) x).2.2 ∈
          intervalGridCell 0 1 grid (e j).1.torus at hpoint
    refine ⟨hden, htheta, ?_, ?_, ?_⟩
    · simpa only [gaussPrefixMarkedPoint] using! hpoint.1
    · simpa only
        [gaussPrefixMarkedPoint_value_eq_signedScaledApproximation] using!
          hpoint.2.1
    · simpa only [gaussSelectedPrefixTorusMark] using! hpoint.2.2
  · intro hall
    change
      x ∈ ⋂ i,
        ⋂ j,
          gaussPrefixMarkedEvent N
            (annularGridCell ε A grid i) (F.1 i j)
    apply Set.mem_iInter.mpr
    intro i
    apply Set.mem_iInter.mpr
    intro a
    let j : Fin (MixedOccurrenceCount k) :=
      e.symm ⟨i, a⟩
    have hj := hall j
    have heq : e j = (⟨i, a⟩ : GaussPrefixMixedOccurrence k) :=
      e.apply_symm_apply ⟨i, a⟩
    have htime :
        fixedOrderMixedTimes N k e F j = (F.1 i a : ℕ) := by
      unfold fixedOrderMixedTimes
      rw [heq]
    rw [htime] at hj
    let w : PositiveDigitWord (F.1 i a : ℕ) :=
      selectedGaussPrefixWord (F.1 i a : ℕ) x
    have hdomain :
        x ∈ positivePrefixDomain (F.1 i a : ℕ) :=
      mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
    have hw : x ∈ positivePrefixCylinder (F.1 i a : ℕ) w :=
      selectedGaussPrefixWord_mem hdomain
    apply mem_gaussPrefixMarkedEvent_iff.mpr
    refine ⟨w, hw, hj.1, hj.2.1, ?_⟩
    change
      (gaussPrefixMarkedPoint N (F.1 i a : ℕ) w x).1 ∈
          intervalGridCell 0 1 grid i.time ∧
        (gaussPrefixMarkedPoint N (F.1 i a : ℕ) w x).2.1 ∈
          intervalGridCell
            (signedGridLower ε A i.sign)
            (signedGridUpper ε A i.sign)
            grid i.signed ∧
        (gaussPrefixMarkedPoint N (F.1 i a : ℕ) w x).2.2 ∈
          intervalGridCell 0 1 grid i.torus
    have heqi : (e j).1 = i := by
      simp only [heq]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [w, gaussPrefixMarkedPoint, heqi] using! hj.2.2.1
    · simpa only [w, heqi,
        gaussPrefixMarkedPoint_value_eq_signedScaledApproximation] using!
          hj.2.2.2.1
    · simpa only [w, heqi, gaussSelectedPrefixTorusMark] using!
        hj.2.2.2.2

/-- The literal annular event forces the parity restriction used by every
canonical chronological depth box. -/
theorem
    literalMixedTupleEvent_depth_parity
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {N grid : ℕ} (hN : 2 ≤ N) (hgrid : 0 < grid)
    {k : AnnularGridIndex grid → ℕ}
    (F : GloballyInjectiveMixedDepthTuple N k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    {x : ℝ}
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0)
    (hxEvent :
      x ∈ gaussPrefixAnnularLiteralMixedTupleEvent ε A N k F)
    (j : Fin (MixedOccurrenceCount k)) :
    fixedOrderMixedTimes N k e F j % 2 =
      (annularGridDepthParity (e j).1).1 := by
  have hcoord :=
    (mem_gaussPrefixAnnularLiteralMixedTupleEvent_iff_coordinates
      F e hxUnit hxNonterm).mp hxEvent j
  let n := fixedOrderMixedTimes N k e F j
  let w : PositiveDigitWord n := selectedGaussPrefixWord n x
  have hdomain : x ∈ positivePrefixDomain n :=
    mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
  have hw : x ∈ positivePrefixCylinder n w :=
    selectedGaussPrefixWord_mem hdomain
  have hex : x ∉ gaussPrefixExceptional (n + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating
      hxUnit hxNonterm (n + 1)
  have htheta :
      0 < gaussApproximationCoordinate n x :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix
      w hxUnit hex hw
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  apply depth_mod_two_eq_annularGridDepthParity_of_signedCell
    hε hεA hgrid (e j).1 hlog htheta
  simpa only [n, gaussSignedScaledApproximationCoordinate] using!
    hcoord.2.2.2.1

end

end Erdos1002
