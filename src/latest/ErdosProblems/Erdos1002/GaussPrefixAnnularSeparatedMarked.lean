import ErdosProblems.Erdos1002.GaussPrefixAnnularNonzeroPreparation
import ErdosProblems.Erdos1002.GaussPrefixAnnularShortMarked
import ErdosProblems.Erdos1002.GaussPrefixAnnularBoundaryCells
import ErdosProblems.Erdos1002.GaussPrefixAnnularTimeZeroMode
import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Early-cylinder bounds for a last nonzero annular Fourier mode

The deepest selected occurrence need not carry a nonzero Fourier
coefficient.  In the early part of the marked-Poisson argument the last
nonzero carrier can occur strictly before several zero-mode value
constraints.  This file supplies the missing literal estimate in that
form.

The key point is that the denominator at the last nonzero occurrence,
not the denominator at the deepest occurrence, dominates the complete
signed carrier.  All statements below retain the finite tuple sum and the
cylinder sum in their correct order.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators Topology symmDiff

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularSeparatedMarkedPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι]

/-! ## Thin moving-midpoint bands -/

/-- The union of the midpoint bands belonging to coordinates strictly
after a distinguished chronological coordinate.  The center itself is
allowed to move with the tuple. -/
def laterMidpointBandNatTupleFamily
    {r : ℕ} (centerIndex : Fin r) (H W : ℕ)
    (tuples : Finset (Fin r → ℕ)) :
    Finset (Fin r → ℕ) :=
  Finset.univ.biUnion fun bandIndex : Fin r ↦
    if centerIndex < bandIndex then
      midpointBandNatTupleFamily centerIndex bandIndex H W tuples
    else ∅

@[simp] theorem mem_laterMidpointBandNatTupleFamily_iff
    {r H W : ℕ} {centerIndex : Fin r}
    {tuples : Finset (Fin r → ℕ)} {t : Fin r → ℕ} :
    t ∈ laterMidpointBandNatTupleFamily centerIndex H W tuples ↔
      t ∈ tuples ∧
        ∃ bandIndex : Fin r, centerIndex < bandIndex ∧
          Nat.dist (2 * t bandIndex) (H + t centerIndex) < W := by
  classical
  simp only [laterMidpointBandNatTupleFamily, Finset.mem_biUnion,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨bandIndex, hband⟩
    by_cases hlt : centerIndex < bandIndex
    · rw [if_pos hlt] at hband
      exact ⟨
        (mem_midpointBandNatTupleFamily_iff.mp hband).1,
        bandIndex, hlt,
        (mem_midpointBandNatTupleFamily_iff.mp hband).2⟩
    · simp [if_neg hlt] at hband
  · rintro ⟨ht, bandIndex, hlt, hdist⟩
    refine ⟨bandIndex, ?_⟩
    rw [if_pos hlt]
    exact mem_midpointBandNatTupleFamily_iff.mpr ⟨ht, hdist⟩

/-- A union over all coordinates after the center still loses only one
ambient power.  This is the exact finite count behind the `O(ρ)`
midpoint-band deletion. -/
theorem card_laterMidpointBandNatTupleFamily_le_of_bounded
    {r H W : ℕ} (centerIndex : Fin r)
    (tuples : Finset (Fin r → ℕ))
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H) :
    (laterMidpointBandNatTupleFamily
        centerIndex H W tuples).card ≤
      r * ((2 * W) * H ^ (r - 1)) := by
  classical
  unfold laterMidpointBandNatTupleFamily
  calc
    (Finset.univ.biUnion (fun bandIndex : Fin r ↦
        if centerIndex < bandIndex then
          midpointBandNatTupleFamily centerIndex bandIndex H W tuples
        else ∅)).card ≤
        ∑ bandIndex : Fin r,
          (if centerIndex < bandIndex then
            midpointBandNatTupleFamily centerIndex bandIndex H W tuples
          else ∅).card := Finset.card_biUnion_le
    _ ≤ ∑ _bandIndex : Fin r,
          (2 * W) * H ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro bandIndex _hmem
      by_cases hlt : centerIndex < bandIndex
      · rw [if_pos hlt]
        exact card_midpointBandNatTupleFamily_le_of_bounded
          centerIndex bandIndex (ne_of_gt hlt) tuples hbound
      · simp only [if_neg hlt, Finset.card_empty, Nat.zero_le]
    _ = r * ((2 * W) * H ^ (r - 1)) := by
      simp

/-- The gap-one quasi-Bernoulli bound summed over an arbitrary
chronological finite family. -/
theorem gaussMovingHeterogeneousDigitTupleSum_le_card_mul
    {r : ℕ} (hr : 0 < r) {scale : ℝ}
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ))
    (hchronological : ∀ t ∈ tuples, IsChronologicalNatTuple t) :
    gaussMovingHeterogeneousDigitTupleSum scale lower upper tuples ≤
      (tuples.card : ℝ) *
        (7 ^ (r - 1) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow scale (lower i) (upper i))) := by
  classical
  unfold gaussMovingHeterogeneousDigitTupleSum
  calc
    (∑ t ∈ tuples,
        gaussMeasure.real
          (gaussHeterogeneousDigitWindowTupleEvent
            scale lower upper t)) ≤
        ∑ _t ∈ tuples,
          (7 ^ (r - 1) *
            ∏ i, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                scale (lower i) (upper i))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact gaussMeasure_real_heterogeneousDigitTupleEvent_le
        hr lower upper t (hchronological t ht)
    _ = (tuples.card : ℝ) *
        (7 ^ (r - 1) *
          ∏ i, gaussMeasure.real
            (scaledGaussFirstDigitWindow scale (lower i) (upper i))) := by
      simp

/-- A tag-dependent uniform marked Fourier sum is bounded directly by
twice-log-two times its aggregate Gauss signed mass. -/
theorem norm_sum_uniformMovingSignedMarkedFourierTupleSum_le_gaussMass
    {β : Type*} [Fintype β] {r : ℕ}
    (N : ℕ) (scale : ℝ)
    (lower upper : β → Fin r → ℝ)
    (mode : β → Fin r → ℤ)
    (tuples : β → Finset (Fin r → ℕ)) :
    ‖∑ b, uniformMovingSignedMarkedFourierTupleSum
        N scale (lower b) (upper b) (mode b) (tuples b)‖ ≤
      (2 * Real.log 2) *
        ∑ b, gaussMovingSignedApproximationTupleSum
          scale (lower b) (upper b) (tuples b) := by
  calc
    ‖∑ b, uniformMovingSignedMarkedFourierTupleSum
        N scale (lower b) (upper b) (mode b) (tuples b)‖ ≤
      ∑ b, ‖uniformMovingSignedMarkedFourierTupleSum
        N scale (lower b) (upper b) (mode b) (tuples b)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b, movingSignedApproximationTupleMassSum
        uniform01Measure scale (lower b) (upper b) (tuples b) := by
      apply Finset.sum_le_sum
      intro b _hb
      exact norm_movingSignedMarkedFourierTupleSum_le_mass
        uniform01Measure N scale
        (lower b) (upper b) (mode b) (tuples b)
    _ ≤ ∑ b, (2 * Real.log 2) *
        gaussMovingSignedApproximationTupleSum
          scale (lower b) (upper b) (tuples b) := by
      apply Finset.sum_le_sum
      intro b _hb
      exact movingSignedApproximationTupleMassSum_uniform_le_gauss
        scale (lower b) (upper b) (tuples b)
    _ = (2 * Real.log 2) *
        ∑ b, gaussMovingSignedApproximationTupleSum
          scale (lower b) (upper b) (tuples b) := by
      rw [Finset.mul_sum]

/-! ## Exact moving-integrand to labeled-character bridge -/

/-- On a nonterminating unit-state point where every selected denominator
is at most `N`, the chronological signed moving integrand is literally the
labeled compact-value mixed character.

The equivalence `e` is used only to reindex the occurrences.  No
probabilistic replacement and no canonical-order hypothesis is hidden in
this identity. -/
theorem gaussMovingSignedMarkedTupleIntegrand_fixedOrder_eq_mixedCharacter
    (N : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (lower upper : ι → ℝ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GloballyInjectiveMixedDepthTuple N k)
    {A x : ℝ}
    (hlower : ∀ z : GaussPrefixMixedOccurrence k, |lower z.1| ≤ A)
    (hupper : ∀ z : GaussPrefixMixedOccurrence k, |upper z.1| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hden : ∀ z : GaussPrefixMixedOccurrence k,
      cfTerminalDenominator
        (selectedGaussPrefixWord (F.1 z.1 z.2) x).1 ≤ N) :
    gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (fun j ↦ lower (e j).1)
        (fun j ↦ upper (e j).1)
        (fun j ↦ h (e j).1 (e j).2)
        (fixedOrderMixedTimes N k e F) x =
      gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
        k h F.1 x := by
  classical
  have hxIoc : x ∈ Ioc (0 : ℝ) 1 :=
    ⟨hxUnit.1, hxUnit.2.le⟩
  have hxIco : x ∈ Ico (0 : ℝ) 1 :=
    ⟨hxUnit.1.le, hxUnit.2⟩
  have hoccurrence (z : GaussPrefixMixedOccurrence k) :
      x ∈ gaussPrefixMarkedEvent N
          (compactValueMarkedRegion (lower z.1) (upper z.1))
          (F.1 z.1 z.2) ↔
        gaussSignedScaledApproximationCoordinate
            (Real.log (N : ℝ)) (F.1 z.1 z.2) x ∈
          Icc (lower z.1) (upper z.1) := by
    let w : PositiveDigitWord (F.1 z.1 z.2 : ℕ) :=
      selectedGaussPrefixWord (F.1 z.1 z.2) x
    have hdomain :
        x ∈ positivePrefixDomain (F.1 z.1 z.2 : ℕ) :=
      mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
    have hxCell :
        x ∈ positivePrefixCylinder (F.1 z.1 z.2 : ℕ) w :=
      selectedGaussPrefixWord_mem hdomain
    have hbase :=
      mem_gaussPrefixMarkedEvent_compactValue_iff_on_deeperCylinder
        hN (le_refl (F.1 z.1 z.2 : ℕ)) w
        (hlower z) (hupper z) hsmall
        (by simpa only [w] using! hden z)
        hxUnit hxNonterm hxCell
    simpa only
      [gaussPrefixMarkedPoint_value_eq_signedScaledApproximation]
      using! hbase
  have hwindow (j : Fin (MixedOccurrenceCount k)) :
      x ∈ gaussSignedApproximationWindow
          (Real.log (N : ℝ)) (fixedOrderMixedTimes N k e F j)
          (lower (e j).1) (upper (e j).1) ↔
        x ∈ gaussPrefixMarkedEvent N
          (compactValueMarkedRegion (lower (e j).1) (upper (e j).1))
          (F.1 (e j).1 (e j).2) := by
    rw [gaussSignedApproximationWindow]
    simp only [Set.mem_inter_iff, hxIoc, Set.mem_preimage,
      true_and, fixedOrderMixedTimes]
    exact (hoccurrence (e j)).symm
  by_cases htuple :
      x ∈ gaussSignedApproximationTupleEvent
        (Real.log (N : ℝ))
        (fun j ↦ lower (e j).1)
        (fun j ↦ upper (e j).1)
        (fixedOrderMixedTimes N k e F)
  · rw [gaussMovingSignedMarkedTupleIntegrand,
      Set.indicator_of_mem htuple]
    have hallWindow :
        ∀ j : Fin (MixedOccurrenceCount k),
          x ∈ gaussSignedApproximationWindow
            (Real.log (N : ℝ)) (fixedOrderMixedTimes N k e F j)
            (lower (e j).1) (upper (e j).1) := by
      exact mem_orderedEventIntersection_ofFn_iff.mp htuple
    have hallEvent :
        ∀ z : GaussPrefixMixedOccurrence k,
          x ∈ gaussPrefixMarkedEvent N
            (compactValueMarkedRegion (lower z.1) (upper z.1))
            (F.1 z.1 z.2) := by
      intro z
      have hj :=
        (hwindow (e.symm z)).mp (hallWindow (e.symm z))
      have heq : e (e.symm z) = z := e.apply_symm_apply z
      rw [heq] at hj
      exact hj
    unfold gaussPrefixMarkedMixedTupleCharacter
    rw [← Fintype.prod_sigma']
    simp_rw [gaussPrefixMarkedDepthCharacter, if_pos (hallEvent _)]
    unfold gaussMovingMarkedTupleCharacter fixedOrderMixedTimes
    exact Fintype.prod_equiv e _ _ (fun _j ↦ rfl)
  · rw [gaussMovingSignedMarkedTupleIntegrand,
      Set.indicator_of_notMem htuple]
    have hnotAll :
        ¬ ∀ j : Fin (MixedOccurrenceCount k),
          x ∈ gaussSignedApproximationWindow
            (Real.log (N : ℝ)) (fixedOrderMixedTimes N k e F j)
            (lower (e j).1) (upper (e j).1) := by
      intro hall
      exact htuple (mem_orderedEventIntersection_ofFn_iff.mpr hall)
    push_neg at hnotAll
    obtain ⟨j, hj⟩ := hnotAll
    have hnotEvent :
        x ∉ gaussPrefixMarkedEvent N
          (compactValueMarkedRegion (lower (e j).1) (upper (e j).1))
          (F.1 (e j).1 (e j).2) := by
      exact fun hevent ↦ hj ((hwindow j).mpr hevent)
    symm
    unfold gaussPrefixMarkedMixedTupleCharacter
    apply Finset.prod_eq_zero (Finset.mem_univ (e j).1)
    apply Finset.prod_eq_zero (Finset.mem_univ (e j).2)
    unfold gaussPrefixMarkedDepthCharacter
    rw [if_neg hnotEvent]

/-! ## Annular specialization on the denominator good event -/

/-- Labeled signed-cell lower endpoint, before chronological reindexing. -/
def annularOccurrenceSignedLower
    (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid) : ℝ :=
  intervalGridPoint
    (signedGridLower ε A i.sign)
    (signedGridUpper ε A i.sign)
    grid i.signed.1

/-- Labeled signed-cell upper endpoint, before chronological reindexing. -/
def annularOccurrenceSignedUpper
    (ε A : ℝ) {grid : ℕ} (i : AnnularGridIndex grid) : ℝ :=
  intervalGridPoint
    (signedGridLower ε A i.sign)
    (signedGridUpper ε A i.sign)
    grid (i.signed.1 + 1)

/-- Both endpoints of an active labeled signed cell lie in `[-A,A]`. -/
theorem abs_annularOccurrenceSignedLower_le
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid) (hi : i.signed.1 < grid) :
    |annularOccurrenceSignedLower ε A i| ≤ A := by
  have hmem :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA i.sign).le hgrid hi.le
  have hleft : -A ≤ signedGridLower ε A i.sign := by
    cases i.sign
    · simp [signedGridLower]
    · simp [signedGridLower]
      linarith
  have hright : signedGridUpper ε A i.sign ≤ A := by
    cases i.sign
    · simp [signedGridUpper]
      linarith
    · simp [signedGridUpper]
  apply abs_le.mpr
  unfold annularOccurrenceSignedLower
  exact ⟨hleft.trans hmem.1, hmem.2.trans hright⟩

theorem abs_annularOccurrenceSignedUpper_le
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (i : AnnularGridIndex grid) (hi : i.signed.1 < grid) :
    |annularOccurrenceSignedUpper ε A i| ≤ A := by
  have hidx : i.signed.1 + 1 ≤ grid := by omega
  have hmem :=
    intervalGridPoint_mem_Icc
      (signedGridLower_lt_upper hεA i.sign).le hgrid hidx
  have hleft : -A ≤ signedGridLower ε A i.sign := by
    cases i.sign
    · simp [signedGridLower]
    · simp [signedGridLower]
      linarith
  have hright : signedGridUpper ε A i.sign ≤ A := by
    cases i.sign
    · simp [signedGridUpper]
      linarith
    · simp [signedGridUpper]
  apply abs_le.mpr
  unfold annularOccurrenceSignedUpper
  exact ⟨hleft.trans hmem.1, hmem.2.trans hright⟩

@[simp] theorem annularOccurrenceSignedLower_flattened
    (ε A : ℝ) {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) :
    annularOccurrenceSignedLower ε A (e j).1 =
      flattenedAnnularSignedLower ε A e j := rfl

@[simp] theorem annularOccurrenceSignedUpper_flattened
    (ε A : ℝ) {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (j : Fin (MixedOccurrenceCount k)) :
    annularOccurrenceSignedUpper ε A (e j).1 =
      flattenedAnnularSignedUpper ε A e j := rfl

/-- Every point in a contracted nonterminal time-depth box lies below the
common contracted time-one depth. -/
theorem lt_gaussLogDepthEndpoint_one_sub_of_mem_contractedAnnularTimeDepthBox
    {N grid : ℕ} {eta : ℝ} (hgrid : 0 < grid)
    (hlog : 0 < Real.log (N : ℝ))
    (i : AnnularGridIndex grid) (htime : i.time.1 < grid)
    {n : ℕ} (hn : n ∈ contractedAnnularTimeDepthBox N eta i) :
    n < gaussLogDepthEndpoint N (1 - eta) := by
  have hnUpper := (Finset.mem_Ico.mp hn).2
  refine hnUpper.trans_le ?_
  unfold gaussLogDepthEndpoint
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right
    · have hpoint :=
        (intervalGridPoint_mem_Icc (a := (0 : ℝ)) (b := 1)
          zero_le_one hgrid (show i.time.1 + 1 ≤ grid by omega)).2
      linarith
    · exact hlog.le
  · exact gaussRoofMean_pos.le

/-- Under the global denominator good event, contracted annular boxes
make every selected prefix denominator admissible for the literal marked
event. -/
theorem forall_selectedDenominator_le_of_contractedAnnularBoxes
    {N L C grid : ℕ} {Delta eta x : ℝ}
    (hgrid : 0 < grid) (hlog : 0 < Real.log (N : ℝ))
    {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hbound : ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hboxes : ∀ j, fixedOrderMixedTimes N k e F j ∈
      contractedAnnularTimeDepthBox N eta (e j).1) :
    ∀ z : GaussPrefixMixedOccurrence k,
      cfTerminalDenominator
        (selectedGaussPrefixWord (F.1 z.1 z.2) x).1 ≤ N := by
  intro z
  let j : Fin (MixedOccurrenceCount k) := e.symm z
  have hej : e j = z := e.apply_symm_apply z
  have hactive : 0 < k (e j).1 := by
    have hj := (e j).2.isLt
    omega
  have hupper :
      fixedOrderMixedTimes N k e F j <
        gaussLogDepthEndpoint N (1 - eta) :=
    lt_gaussLogDepthEndpoint_one_sub_of_mem_contractedAnnularTimeDepthBox
      hgrid hlog (e j).1 (htime (e j).1 hactive) (hboxes j)
  have hlt :=
    gaussPrefixDenominator_lt_of_depth_lt_contracted_one
      hlog hxGood (hbound j) hmargin hupper
  change
    cfTerminalDenominator
      (selectedGaussPrefixWord (F.1 z.1 z.2) x).1 ≤ N
  have htimeEq :
      fixedOrderMixedTimes N k e F j = (F.1 z.1 z.2 : ℕ) := by
    unfold fixedOrderMixedTimes
    rw [hej]
  rw [← htimeEq]
  exact hlt.le

/-- Fully specialized pointwise bridge for a contracted annular tuple on
the denominator good event. -/
theorem
    gaussMovingAnnularMarkedTupleIntegrand_eq_mixedCharacter_of_good_contracted
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid N L C : ℕ} (hgrid : 0 < grid) (hN : 2 ≤ N)
    {Delta eta x : ℝ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hbound : ∀ j, fixedOrderMixedTimes N k e F j ≤ C * L)
    (hmargin : Delta * (L : ℝ) ≤ eta * Real.log (N : ℝ))
    (hboxes : ∀ j, fixedOrderMixedTimes N k e F j ∈
      contractedAnnularTimeDepthBox N eta (e j).1) :
    gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        (flattenedAnnularFourierMode e h)
        (fixedOrderMixedTimes N k e F) x =
      gaussPrefixMarkedMixedTupleCharacter N
        (fun i ↦ compactValueMarkedRegion
          (annularOccurrenceSignedLower ε A i)
          (annularOccurrenceSignedUpper ε A i))
        k h F.1 x := by
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hden :=
    forall_selectedDenominator_le_of_contractedAnnularBoxes
      hgrid hlog e F htime hxGood hbound hmargin hboxes
  simpa only [annularOccurrenceSignedLower_flattened,
    annularOccurrenceSignedUpper_flattened,
    flattenedAnnularFourierMode] using!
    gaussMovingSignedMarkedTupleIntegrand_fixedOrder_eq_mixedCharacter
      N hN k e
      (annularOccurrenceSignedLower ε A)
      (annularOccurrenceSignedUpper ε A)
      h F
      (fun z ↦ by
        exact abs_annularOccurrenceSignedLower_le
          hε hεA hgrid z.1 (hsigned z.1 (by
            have hi := z.2.isLt
            omega)))
      (fun z ↦ by
        exact abs_annularOccurrenceSignedUpper_le
          hε hεA hgrid z.1 (hsigned z.1 (by
            have hi := z.2.isLt
            omega)))
      hsmall hxUnit hxNonterm hden

/-! ## A carrier floor when the last nonzero mode is not deepest -/

/-- On a deepest cylinder, the denominator belonging to the last nonzero
Fourier occurrence dominates the complete carrier.  Later occurrences are
allowed, but their Fourier coefficients must be zero through `hgap`.

This is the deterministic estimate needed in the early case; in
particular, no false assumption that the last nonzero occurrence is the
deepest selected occurrence is made. -/
theorem
    half_lastNonzeroDenominator_le_abs_exactDepthCylinderMixedCarrier_of_gap
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m gap : ℕ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ)) :
    (cfTerminalDenominator
        (positiveDigitWordTake (F z₀.1 z₀.2 : ℕ)
          (hF z₀.1 z₀.2) w.toPositive).1 : ℝ) / 2 ≤
      |exactDepthCylinderMixedCarrier N k h F w| := by
  classical
  let representative : ℝ := gaussPrefixRepresentative w.1.1
  let w₀ : PositiveDigitWord (F z₀.1 z₀.2 : ℕ) :=
    positiveDigitWordTake (F z₀.1 z₀.2 : ℕ)
      (hF z₀.1 z₀.2) w.toPositive
  let q : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (cfTerminalDenominator
      (selectedGaussPrefixWord (F z.1 z.2) representative).1 : ℝ)
  let weight : GaussPrefixMixedOccurrence k → ℝ :=
    fun z ↦ |(h z.1 z.2 : ℝ)|
  let term : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (h z.1 z.2 : ℝ) * q z
  let P : ℝ := ((2 ^ (gap / 2) : ℕ) : ℝ)
  let Q : ℝ := (cfTerminalDenominator w₀.1 : ℝ)
  have hrepMem : representative ∈
      positivePrefixCylinder m w.toPositive := by
    exact gaussPrefixRepresentative_mem w.1.2.2.1
  have hrepUnit : representative ∈ Ico (0 : ℝ) 1 := by
    have hrepIoo : representative ∈ Ioo (0 : ℝ) 1 := by
      dsimp only [representative]
      unfold gaussPrefixRepresentative
      exact gaussInverseWord_mem_Ioo w.1.2.2.1 (by norm_num)
    exact ⟨hrepIoo.1.le, hrepIoo.2⟩
  have hrepMem₀ : representative ∈
      positivePrefixCylinder (F z₀.1 z₀.2 : ℕ) w₀ := by
    exact mem_positivePrefixCylinder_positiveDigitWordTake
      (hF z₀.1 z₀.2) w.toPositive hrepUnit hrepMem
  have hselected₀ :
      selectedGaussPrefixWord (F z₀.1 z₀.2 : ℕ) representative = w₀ :=
    selectedGaussPrefixWord_eq_of_mem w₀ hrepMem₀
  have habsCoeff : (1 : ℝ) ≤ |(h z₀.1 z₀.2 : ℝ)| := by
    have hnat : 1 ≤ (h z₀.1 z₀.2).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hcoeff)
    calc
      (1 : ℝ) ≤ ((h z₀.1 z₀.2).natAbs : ℝ) := by
        exact_mod_cast hnat
      _ = |(h z₀.1 z₀.2 : ℝ)| := by simp
  have hmain : Q ≤ |term z₀| := by
    dsimp only [term, q, Q]
    rw [hselected₀, abs_mul,
      abs_of_nonneg (show 0 ≤ (cfTerminalDenominator w₀.1 : ℝ) by
        positivity)]
    simpa only [one_mul] using!
      (mul_le_mul_of_nonneg_right habsCoeff
        (show 0 ≤ (cfTerminalDenominator w₀.1 : ℝ) by positivity))
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hscale :
      ∀ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        weight z = 0 ∨ P * q z ≤ Q := by
    intro z hz
    have hzNe : z ≠ z₀ := (Finset.mem_erase.mp hz).1
    by_cases hzero : h z.1 z.2 = 0
    · left
      dsimp only [weight]
      simp only [hzero, Int.cast_zero, abs_zero]
    right
    have hgapz := hgap z hzNe hzero
    have hzle₀ : (F z.1 z.2 : ℕ) ≤ (F z₀.1 z₀.2 : ℕ) := by
      omega
    have hexponent :
        gap / 2 ≤
          ((F z₀.1 z₀.2 : ℕ) - (F z.1 z.2 : ℕ)) / 2 := by
      omega
    have hpow : 2 ^ (gap / 2) ≤
        2 ^ (((F z₀.1 z₀.2 : ℕ) - (F z.1 z.2 : ℕ)) / 2) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    have hselected :
        selectedGaussPrefixWord (F z.1 z.2 : ℕ) representative =
          positiveDigitWordTake (F z.1 z.2 : ℕ) hzle₀ w₀ :=
      selectedGaussPrefixWord_eq_positiveDigitWordTake
        hzle₀ w₀ hrepUnit hrepMem₀
    have hgrowth :=
      pow_two_depthGap_mul_cfTerminalDenominator_take_le
        (F z.1 z.2 : ℕ) hzle₀ w₀
    have hmul :
        2 ^ (gap / 2) *
            cfTerminalDenominator
              (selectedGaussPrefixWord
                (F z.1 z.2) representative).1 ≤
          cfTerminalDenominator w₀.1 := by
      rw [hselected]
      exact (Nat.mul_le_mul_right _ hpow).trans hgrowth
    dsimp only [P, q, Q]
    exact_mod_cast hmul
  have htwo :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        weight z * q z) ≤ Q :=
    two_mul_sum_weight_mul_le_of_common_scale
      ((Finset.univ :
        Finset (GaussPrefixMixedOccurrence k)).erase z₀)
      weight q hP hQ (fun z _hz ↦ abs_nonneg _) hscale (by
        simpa only [weight, P] using! hweightBudget)
  have hrest :
      (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |term z|) ≤ Q / 2 := by
    have hrewrite :
        (∑ z ∈ (Finset.univ :
            Finset (GaussPrefixMixedOccurrence k)).erase z₀,
          |term z|) =
          ∑ z ∈ (Finset.univ :
              Finset (GaussPrefixMixedOccurrence k)).erase z₀,
            weight z * q z := by
      apply Finset.sum_congr rfl
      intro z _hz
      dsimp only [term, weight]
      rw [abs_mul, abs_of_nonneg (show 0 ≤ q z by
        dsimp only [q]
        positivity)]
    rw [hrewrite]
    linarith
  have hcarrier :
      exactDepthCylinderMixedCarrier N k h F w = ∑ z, term z := by
    unfold exactDepthCylinderMixedCarrier
      gaussPrefixMarkedMixedCarrier
    rw [← Fintype.sum_sigma']
  rw [hcarrier]
  change Q / 2 ≤ |∑ z, term z|
  exact half_le_abs_sum_of_dominant_occurrence
    k term z₀ hmain hrest

/-- The preceding relative dominance estimate with the absolute
exponential denominator floor supplied by one point of the global good
event. -/
theorem
    exp_half_le_abs_exactDepthCylinderMixedCarrier_of_lastNonzero_gap_goodPoint
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ x : ℝ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (hz₀Bound : (F z₀.1 z₀.2 : ℕ) ≤ C * L)
    (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hxCell : x ∈ exactDepthBoundedCylinder w) :
    Real.exp
        (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
          Δ * (L : ℝ)) / 2 ≤
      |exactDepthCylinderMixedCarrier N k h F w| := by
  have hselected :
      selectedGaussPrefixWord (F z₀.1 z₀.2 : ℕ) x =
        positiveDigitWordTake (F z₀.1 z₀.2 : ℕ)
          (hF z₀.1 z₀.2) w.toPositive :=
    selectedGaussPrefixWord_eq_positiveDigitWordTake
      (hF z₀.1 z₀.2) w.toPositive hxUnit hxCell
  have hQ :=
    (gaussPrefixDenominator_exp_bounds_of_mem_linearGoodEvent
      hxGood hz₀Bound).1
  rw [hselected] at hQ
  exact (div_le_div_of_nonneg_right hQ (by norm_num)).trans
    (half_lastNonzeroDenominator_le_abs_exactDepthCylinderMixedCarrier_of_gap
      N k h F hF w z₀ hcoeff hgap hweightBudget)

/-- Word-local version of the absolute carrier floor.  This is the form
used in an exact prefix-cylinder partition: the good condition is a
literal predicate on the complete depth-`m` word, hence it is constant on
the whole cylinder and has no future dependence. -/
theorem
    exp_half_le_abs_exactDepthCylinderMixedCarrier_of_lastNonzero_gap_prefixGoodWord
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {L m gap : ℕ} {Delta : ℝ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (hwGood :
      w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ))
    (hweightBudget :
      2 * (∑ z ∈ (Finset.univ :
          Finset (GaussPrefixMixedOccurrence k)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ)) :
    Real.exp
        (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
          Delta * (L : ℝ)) / 2 ≤
      |exactDepthCylinderMixedCarrier N k h F w| := by
  have hQ :=
    (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
      w.toPositive hwGood (hF z₀.1 z₀.2)).1
  exact (div_le_div_of_nonneg_right hQ (by norm_num)).trans
    (half_lastNonzeroDenominator_le_abs_exactDepthCylinderMixedCarrier_of_gap
      N k h F hF w z₀ hcoeff hgap hweightBudget)

/-! ## Literal early one-cylinder and summed-cell estimates -/

/-- Complete one-cylinder oscillatory estimate in the early case.  The
deepest depth is `m`, while the carrier floor is taken at the (possibly
earlier) last nonzero occurrence `z₀`. -/
theorem
    norm_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_goodPoint
    (N : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ x A : ℝ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
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
    (hz₀Bound : (F z₀.1 z₀.2 : ℕ) ≤ C * L)
    (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Δ)
    (hxCell : x ∈ exactDepthBoundedCylinder w) :
    ‖∫ y in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F y ∂uniform01Measure‖ ≤
      2 / (Real.pi * (N : ℝ) *
        Real.exp
          (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
            Δ * (L : ℝ))) := by
  obtain ⟨left, right, _hlr, hinterval⟩ :=
    exists_intervalIntegral_eq_setIntegral_mixedTupleCharacter_compactValue
      N hN k h F hF w lower upper hlower hupper hsmall
  rw [hinterval]
  let E : ℝ :=
    Real.exp
      (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
        Δ * (L : ℝ))
  let D : ℝ := exactDepthCylinderMixedCarrier N k h F w
  have hDfloor : E / 2 ≤ |D| := by
    exact
      exp_half_le_abs_exactDepthCylinderMixedCarrier_of_lastNonzero_gap_goodPoint
        N k h F hF w z₀ hcoeff hgap hweightBudget hz₀Bound
          hxUnit hxGood hxCell
  have hD : D ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hDfloor
    have hE : 0 < E := by
      dsimp only [E]
      positivity
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

/-- Summed version of the early estimate.  The norm is outside the sum
over all retained deepest cylinders for one tuple; the proved quadratic
terminal-word bound supplies the cylinder count. -/
theorem
    norm_sum_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_goodCells
    (N R : ℕ) (hN : 2 ≤ N) (hRN : R ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Δ A : ℝ}
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
    (hz₀Bound : (F z₀.1 z₀.2 : ℕ) ≤ C * L)
    (cells : Finset (ExactDepthBoundedPositiveWord R m))
    (hGoodCell : ∀ w ∈ cells, ∃ x : ℝ,
      x ∈ Ico (0 : ℝ) 1 ∧
      x ∈ gaussDenominatorLinearGoodEvent C L Δ ∧
        x ∈ exactDepthBoundedCylinder w) :
    ‖∑ w ∈ cells,
        ∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤
      ((2 * (R + 1) ^ 2 : ℕ) : ℝ) *
        (2 / (Real.pi * (N : ℝ) *
          Real.exp
            (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Δ * (L : ℝ)))) := by
  let cellBound : ℝ :=
    2 / (Real.pi * (N : ℝ) *
      Real.exp
        (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
          Δ * (L : ℝ)))
  have hcellBound : 0 ≤ cellBound := by
    dsimp only [cellBound]
    positivity
  have hOne (w : ExactDepthBoundedPositiveWord R m) (hw : w ∈ cells) :
      ‖∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤ cellBound := by
    obtain ⟨x, hxUnit, hxGood, hxCell⟩ := hGoodCell w hw
    have hxCell' :
        x ∈ exactDepthBoundedCylinder (w.mono hRN) := by
      simpa only [exactDepthBoundedCylinder_mono] using! hxCell
    simpa only [cellBound] using!
      norm_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_goodPoint
        N hN k h F hF (w.mono hRN) z₀ hcoeff hgap
          hweightBudget lower upper hlower hupper hsmall hz₀Bound
          hxUnit hxGood hxCell'
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
          Real.exp
            (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Δ * (L : ℝ)))) := rfl

/-- Prefix-good-word version of the early one-cylinder estimate. -/
theorem
    norm_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_prefixGoodWord
    (N : ℕ) (hN : 2 ≤ N)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {L m gap : ℕ} {Delta A : ℝ}
    (hF : ∀ i j, (F i j : ℕ) ≤ m)
    (w : ExactDepthBoundedPositiveWord N m)
    (hwGood :
      w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta)
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
    ‖∫ y in exactDepthBoundedCylinder w,
        gaussPrefixMarkedMixedTupleCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F y ∂uniform01Measure‖ ≤
      2 / (Real.pi * (N : ℝ) *
        Real.exp
          (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
            Delta * (L : ℝ))) := by
  obtain ⟨left, right, _hlr, hinterval⟩ :=
    exists_intervalIntegral_eq_setIntegral_mixedTupleCharacter_compactValue
      N hN k h F hF w lower upper hlower hupper hsmall
  rw [hinterval]
  let E : ℝ :=
    Real.exp
      (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
        Delta * (L : ℝ))
  let D : ℝ := exactDepthCylinderMixedCarrier N k h F w
  have hDfloor : E / 2 ≤ |D| :=
    exp_half_le_abs_exactDepthCylinderMixedCarrier_of_lastNonzero_gap_prefixGoodWord
      N k h F hF w hwGood z₀ hcoeff hgap hweightBudget
  have hD : D ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hDfloor
    have hE : 0 < E := by
      dsimp only [E]
      positivity
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

/-- Prefix-measurable summed early-cylinder estimate.  The hypothesis on
`cells` is word-local, so every integral is over an entire cylinder and
there is no illegitimate replacement of `∫_{good ∩ C}` by `∫_C`. -/
theorem
    norm_sum_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_prefixGoodCells
    (N R : ℕ) (hN : 2 ≤ N) (hRN : R ≤ N)
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
    (cells : Finset (ExactDepthBoundedPositiveWord R m))
    (hGoodCell : ∀ w ∈ cells,
      w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta) :
    ‖∑ w ∈ cells,
        ∫ y in exactDepthBoundedCylinder (w.mono hRN),
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
  have hOne (w : ExactDepthBoundedPositiveWord R m) (hw : w ∈ cells) :
      ‖∫ y in exactDepthBoundedCylinder (w.mono hRN),
          gaussPrefixMarkedMixedTupleCharacter N
            (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
            k h F y ∂uniform01Measure‖ ≤ cellBound := by
    have hwGood := hGoodCell w hw
    have hwGood' :
        (w.mono hRN).toPositive ∈
          gaussDenominatorPrefixGoodWords m L Delta := by
      exact hwGood
    simpa only [cellBound] using!
      norm_setIntegral_mixedTupleCharacter_compactValue_le_of_lastNonzero_gap_prefixGoodWord
        N hN k h F hF (w.mono hRN) hwGood' z₀ hcoeff hgap
          hweightBudget lower upper hlower hupper hsmall
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
          Real.exp
            (((F z₀.1 z₀.2 : ℕ) : ℝ) * gaussRoofMean -
              Delta * (L : ℝ)))) := rfl

/-! ## Unconditional deletion of the initial-depth layer -/

/-- Separated tuples whose first chronological depth is still below the
square-root scale. -/
def initialSeparatedCanonicalAnnularGridTupleFamily
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  earlyFirstNatTupleFamily hr (annularSeparationGap N)
    (separatedCanonicalAnnularGridTupleFamily N k e)

/-- The complementary separated family, whose first depth is already at
least the square-root scale. -/
def interiorSeparatedCanonicalAnnularGridTupleFamily
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  lateFirstNatTupleFamily hr (annularSeparationGap N)
    (separatedCanonicalAnnularGridTupleFamily N k e)

/-- A midpoint band of relative doubled width `rho`.  The use of a natural
ceiling makes the finite family literal while retaining the exact
`rho · H` asymptotic scale. -/
def annularMidpointBandWidth (rho : ℝ) (N : ℕ) : ℕ :=
  ⌈rho * (annularDepthAmbientSize N : ℝ)⌉₊

/-- The natural midpoint-band width has its claimed logarithmic
asymptotic, including the ceiling error. -/
theorem tendsto_annularMidpointBandWidth_div_log
    {rho : ℝ} (hrho : 0 ≤ rho) :
    Tendsto
      (fun N : ℕ ↦ (annularMidpointBandWidth rho N : ℝ) /
        Real.log (N : ℝ))
      atTop (nhds (rho / gaussRoofMean)) := by
  have hHtop : Tendsto
      (fun N : ℕ ↦ (annularDepthAmbientSize N : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      tendsto_annularDepthAmbientSize_atTop
  have hwidthOverH :=
    tendsto_natCeil_const_mul_scale_div
      (fun N : ℕ ↦ (annularDepthAmbientSize N : ℝ))
      hHtop hrho (show (0 : ℝ) < 1 by norm_num)
  have hproduct :=
    hwidthOverH.mul tendsto_annularDepthAmbientSize_div_log
  have hproduct' :
      Tendsto
        (fun N : ℕ ↦
          ((annularMidpointBandWidth rho N : ℝ) /
              (annularDepthAmbientSize N : ℝ)) *
            ((annularDepthAmbientSize N : ℝ) /
              Real.log (N : ℝ)))
        atTop (nhds (rho / gaussRoofMean)) := by
    simpa only [annularMidpointBandWidth, div_one, inv_one, mul_one,
      one_mul, div_eq_mul_inv]
      using! hproduct
  apply hproduct'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0,
      tendsto_annularDepthAmbientSize_atTop.eventually_gt_atTop 0] with
      N hlog hH
  have hHne : (annularDepthAmbientSize N : ℝ) ≠ 0 := by
    exact_mod_cast hH.ne'
  unfold annularMidpointBandWidth
  field_simp [hHne, ne_of_gt hlog]

/-- The explicit one-tag cardinal majorant has an exact limiting
logarithmic density linear in `rho`. -/
theorem tendsto_annularMidpointBandCardMajorant_div_log_pow
    (r : ℕ) {rho : ℝ} (hrho : 0 ≤ rho) :
    Tendsto
      (fun N : ℕ ↦
        ((r * ((2 * annularMidpointBandWidth rho N) *
            annularDepthAmbientSize N ^ (r - 1)) : ℕ) : ℝ) /
          Real.log (N : ℝ) ^ r)
      atTop
      (nhds ((r : ℝ) * 2 *
        (rho / gaussRoofMean) *
        (1 / gaussRoofMean) ^ (r - 1))) := by
  cases r with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, Nat.zero_sub, pow_zero,
        mul_one, zero_div]
      exact (tendsto_const_nhds :
        Tendsto (fun _N : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
  | succ r =>
      have hwidth := tendsto_annularMidpointBandWidth_div_log hrho
      have hambientPow :=
        tendsto_annularDepthAmbientSize_div_log.pow r
      have hproduct :=
        ((tendsto_const_nhds :
            Tendsto (fun _N : ℕ ↦ ((Nat.succ r : ℕ) : ℝ) * 2)
              atTop (nhds (((Nat.succ r : ℕ) : ℝ) * 2))).mul
          hwidth).mul hambientPow
      apply hproduct.congr'
      filter_upwards
        [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlogPos
      have hlog : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogPos
      push_cast
      rw [pow_succ, div_pow]
      field_simp [hlog]

/-- For one chronological tag and one nonzero mode, retain those interior
separated tuples having a later zero-mode coordinate in the moving
midpoint band centered between the last nonzero depth and the ambient
horizon. -/
def annularCanonicalLaterMidpointBandTupleFamily
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  laterMidpointBandNatTupleFamily
    (annularLastNonzeroIndex mode hmode)
    (annularDepthAmbientSize N)
    (annularMidpointBandWidth rho N)
    (interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e)

/-- The tagged midpoint family for a mode which may depend on the
canonical chronological-order tag. -/
def annularCanonicalLaterMidpointBandTaggedTupleFamily
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
  annularCanonicalLaterMidpointBandTupleFamily
    rho N k hr e (mode e) (hmode e)

/-- The moving-band family is still contained in the canonical family. -/
theorem annularCanonicalLaterMidpointBandTupleFamily_subset_canonical
    (rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    annularCanonicalLaterMidpointBandTupleFamily
        rho N k hr e mode hmode ⊆
      canonicalAnnularGridTupleFamily N k e := by
  intro t ht
  have htInterior :=
    (mem_laterMidpointBandNatTupleFamily_iff.mp ht).1
  have htSeparated :=
    (mem_lateFirstNatTupleFamily_iff.mp htInterior).1
  exact (mem_separatedNatTupleFamily_iff.mp htSeparated).1

/-- Exact cardinal bound for one tag's moving midpoint band. -/
theorem card_annularCanonicalLaterMidpointBandTupleFamily_le
    {rho : ℝ} {N : ℕ} (hN : 1 < N)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    (annularCanonicalLaterMidpointBandTupleFamily
        rho N k hr e mode hmode).card ≤
      MixedOccurrenceCount k *
        ((2 * annularMidpointBandWidth rho N) *
          annularDepthAmbientSize N ^
            (MixedOccurrenceCount k - 1)) := by
  apply card_laterMidpointBandNatTupleFamily_le_of_bounded
  intro t ht j
  have htSeparated :=
    (mem_lateFirstNatTupleFamily_iff.mp ht).1
  have htCanonical :=
    (mem_separatedNatTupleFamily_iff.mp htSeparated).1
  exact canonicalAnnularGridTupleFamily_lt_ambient
    hgrid k htime hN e t htCanonical j

/-- A mode-independent deterministic upper envelope for the uniform
one-digit mass of all midpoint-band tuples. -/
def annularCanonicalMidpointBandDigitMassUpper
    (ε A rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℝ :=
  (2 * Real.log 2) *
    ((MixedOccurrenceCount k *
      ((2 * annularMidpointBandWidth rho N) *
        annularDepthAmbientSize N ^
          (MixedOccurrenceCount k - 1)) : ℕ) : ℝ) *
    (7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
    ∑ e : Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k,
      ∏ j,
        gaussMeasure.real
          (scaledGaussFirstDigitWindow
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e) j)
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e) j))

/-- The explicit midpoint-band digit envelope has a limit proportional to
`rho`.  This is the analytic form needed for the final order of limits:
first `N → ∞`, then `rho ↓ 0`. -/
theorem tendsto_annularCanonicalMidpointBandDigitMassUpper
    {ε A rho : ℝ} (hε : 0 < ε) (hεA : ε < A)
    (hrho : 0 ≤ rho)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        annularCanonicalMidpointBandDigitMassUpper
          ε A rho N k)
      atTop
      (nhds (
        (2 * Real.log 2) *
          ((MixedOccurrenceCount k : ℝ) * 2 *
            (rho / gaussRoofMean) *
            (1 / gaussRoofMean) ^
              (MixedOccurrenceCount k - 1)) *
          (7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
          (Fintype.card
              (Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k) : ℝ) *
          annularOccurrenceSignedDensity ε A k)) := by
  let lower :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℝ :=
    fun e ↦ gaussPrescribedParityOrientedLower
      (flattenedAnnularParity e)
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
  let upper :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℝ :=
    fun e ↦ gaussPrescribedParityOrientedUpper
      (flattenedAnnularParity e)
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
  have hscaled (e :
      Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
      Tendsto
        (fun N : ℕ ↦
          ∏ j, Real.log (N : ℝ) *
            gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (Real.log (N : ℝ)) (lower e j) (upper e j)))
        atTop
        (nhds (annularOccurrenceSignedDensity ε A k)) := by
    have h :=
      tendsto_movingGaussHeterogeneousRareDigitProduct
        (fun N : ℕ ↦ Real.log (N : ℝ))
        tendsto_log_natCast_atTop
        (lower e) (upper e)
        (fun j ↦ flattenedAnnular_oriented_lower_pos
          hε hεA hgrid hsigned e j)
        (fun j ↦ flattenedAnnular_oriented_lower_lt_upper
          hεA hgrid e j)
    simpa only [lower, upper,
      flattenedAnnular_oriented_product_eq ε A] using! h
  have hscaledSum :
      Tendsto
        (fun N : ℕ ↦
          ∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            ∏ j, Real.log (N : ℝ) *
              gaussMeasure.real
                (scaledGaussFirstDigitWindow
                  (Real.log (N : ℝ)) (lower e j) (upper e j)))
        atTop
        (nhds ((Fintype.card
            (Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k) : ℝ) *
          annularOccurrenceSignedDensity ε A k)) := by
    have hsum := tendsto_finset_sum Finset.univ
      (fun e _he ↦ hscaled e)
    simpa using! hsum
  have hmajorant :=
    tendsto_annularMidpointBandCardMajorant_div_log_pow
      (MixedOccurrenceCount k) hrho
  have hproduct :=
    (((tendsto_const_nhds :
        Tendsto (fun _N : ℕ ↦ 2 * Real.log 2)
          atTop (nhds (2 * Real.log 2))).mul hmajorant).mul
      (tendsto_const_nhds :
        Tendsto
          (fun _N : ℕ ↦ (7 : ℝ) ^ (MixedOccurrenceCount k - 1))
          atTop
          (nhds ((7 : ℝ) ^ (MixedOccurrenceCount k - 1))))).mul
        hscaledSum
  have hproduct' :
      Tendsto
        (fun N : ℕ ↦
          (2 * Real.log 2) *
            (((MixedOccurrenceCount k *
                ((2 * annularMidpointBandWidth rho N) *
                  annularDepthAmbientSize N ^
                    (MixedOccurrenceCount k - 1)) : ℕ) : ℝ) /
              Real.log (N : ℝ) ^ (MixedOccurrenceCount k)) *
            (7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
            (∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              ∏ j, Real.log (N : ℝ) *
                gaussMeasure.real
                  (scaledGaussFirstDigitWindow
                    (Real.log (N : ℝ)) (lower e j) (upper e j))))
        atTop
        (nhds (
          (2 * Real.log 2) *
            ((MixedOccurrenceCount k : ℝ) * 2 *
              (rho / gaussRoofMean) *
              (1 / gaussRoofMean) ^
                (MixedOccurrenceCount k - 1)) *
            (7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
            (Fintype.card
                (Fin (MixedOccurrenceCount k) ≃
                  GaussPrefixMixedOccurrence k) : ℝ) *
            annularOccurrenceSignedDensity ε A k)) := by
    convert! hproduct using 1
    all_goals ring
  apply hproduct'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  unfold annularCanonicalMidpointBandDigitMassUpper
  dsimp only [lower, upper]
  simp_rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hlogNe : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlog
  rw [← Finset.mul_sum]
  field_simp [hlogNe]

/-- The complete canonical family controls every exact-to-one-digit
replacement error which can occur in a midpoint subfamily.  Keeping this
as an explicitly nonnegative sum lets us dominate arbitrary
mode-dependent midpoint bands without requiring those bands themselves
to have a limiting density. -/
def annularCanonicalGaussOrientedReplacementError
    (ε A : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    ∑ t ∈ canonicalAnnularGridTupleFamily N k e,
      gaussMeasure.real
        ((gaussHeterogeneousApproximationTupleEvent
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)) t) ∆
          (gaussHeterogeneousDigitWindowTupleEvent
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)) t))

/-- Exact-to-digit replacement errors for the complete canonical
annular family are absolutely summable.  This is the full-family
majorant used for every moving midpoint subfamily. -/
theorem
    tendsto_annularCanonicalGaussOrientedReplacementError_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid) :
    Tendsto
      (fun N : ℕ ↦
        annularCanonicalGaussOrientedReplacementError ε A N k)
      atTop (nhds 0) := by
  let lower :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℝ :=
    fun e ↦ gaussPrescribedParityOrientedLower
      (flattenedAnnularParity e)
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
  let upper :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℝ :=
    fun e ↦ gaussPrescribedParityOrientedUpper
      (flattenedAnnularParity e)
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
  have htotal :
      Tendsto
        (fun N : ℕ ↦
          (aggregateTupleFamilyCard
              (fun e ↦ canonicalAnnularGridTupleFamily N k e) : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
        atTop (nhds (annularOccurrenceTimeDensity k)) := by
    simpa only [aggregateTupleFamilyCard,
      totalCanonicalAnnularGridTupleCard] using!
      tendsto_totalCanonicalAnnularGridTupleCard_density
        hgrid k hr htime
  have hreplacement :=
    tendsto_aggregateGaussHeterogeneousApproximationDigitSymmDiff_zero
      (β := Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k)
      (A := A) (density := annularOccurrenceTimeDensity k)
      hr (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop lower upper
      (hε.le.trans hεA.le)
      (fun e j ↦ flattenedAnnular_oriented_lower_pos
        hε hεA hgrid hsigned e j)
      (fun e j ↦ flattenedAnnular_oriented_lower_lt_upper
        hεA hgrid e j)
      (fun e j ↦ flattenedAnnular_oriented_upper_le
        hεA hgrid hsigned e j)
      (fun N e ↦ canonicalAnnularGridTupleFamily N k e)
      (fun N e t ht ↦
        canonicalAnnularGridTupleFamily_chronological N k e t ht)
      htotal
  simpa only [annularCanonicalGaussOrientedReplacementError,
    lower, upper] using! hreplacement

/-- Aggregate Gauss exact mass of the tagged moving midpoint families,
after orienting signed windows by their canonical parity. -/
def annularCanonicalGaussOrientedMidpointBandApproximationMass
    (ε A rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    gaussMovingHeterogeneousApproximationTupleSum
      (Real.log (N : ℝ))
      (gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e))
      (gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e))
      (annularCanonicalLaterMidpointBandTaggedTupleFamily
        rho N k hr mode hmode e)

/-- Aggregate Gauss one-digit mass of the same tagged moving midpoint
families. -/
def annularCanonicalGaussOrientedMidpointBandDigitMass
    (ε A rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℝ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    gaussMovingHeterogeneousDigitTupleSum
      (Real.log (N : ℝ))
      (gaussPrescribedParityOrientedLower
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e))
      (gaussPrescribedParityOrientedUpper
        (flattenedAnnularParity e)
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e))
      (annularCanonicalLaterMidpointBandTaggedTupleFamily
        rho N k hr mode hmode e)

/-- The actual tag-dependent uniform marked Fourier coefficient carried
by the moving midpoint bands. -/
def annularCanonicalUniformMidpointBandMarkedFourierSum
    (ε A rho : ℝ) (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) : ℂ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k,
    uniformMovingSignedMarkedFourierTupleSum
      N (Real.log (N : ℝ))
      (flattenedAnnularSignedLower ε A e)
      (flattenedAnnularSignedUpper ε A e)
      (mode e)
      (annularCanonicalLaterMidpointBandTaggedTupleFamily
        rho N k hr mode hmode e)

set_option maxHeartbeats 800000
/-- The exact Gauss mass on a moving midpoint family is at most its
one-digit mass plus the complete-canonical replacement error. -/
theorem
    annularCanonicalGaussOrientedMidpointBandApproximationMass_le
    {ε A rho : ℝ} {N : ℕ} {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    annularCanonicalGaussOrientedMidpointBandApproximationMass
        ε A rho N k hr mode hmode ≤
      annularCanonicalGaussOrientedMidpointBandDigitMass
          ε A rho N k hr mode hmode +
        annularCanonicalGaussOrientedReplacementError ε A N k := by
  unfold annularCanonicalGaussOrientedMidpointBandApproximationMass
    annularCanonicalGaussOrientedMidpointBandDigitMass
    annularCanonicalGaussOrientedReplacementError
  calc
    (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        gaussMovingHeterogeneousApproximationTupleSum
          (Real.log (N : ℝ))
          (gaussPrescribedParityOrientedLower
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e))
          (gaussPrescribedParityOrientedUpper
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e))
          (annularCanonicalLaterMidpointBandTaggedTupleFamily
            rho N k hr mode hmode e)) ≤
      ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        (gaussMovingHeterogeneousDigitTupleSum
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (annularCanonicalLaterMidpointBandTaggedTupleFamily
              rho N k hr mode hmode e) +
          ∑ t ∈
              annularCanonicalLaterMidpointBandTaggedTupleFamily
                rho N k hr mode hmode e,
            gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                  (Real.log (N : ℝ))
                  (gaussPrescribedParityOrientedLower
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e))
                  (gaussPrescribedParityOrientedUpper
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e)) t ∆
                gaussHeterogeneousDigitWindowTupleEvent
                  (Real.log (N : ℝ))
                  (gaussPrescribedParityOrientedLower
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e))
                  (gaussPrescribedParityOrientedUpper
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e)) t)) := by
      apply Finset.sum_le_sum
      intro e _he
      have habs :=
        abs_gaussMovingHeterogeneousApproximationTupleSum_sub_digit_le
          (Real.log (N : ℝ))
          (gaussPrescribedParityOrientedLower
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e))
          (gaussPrescribedParityOrientedUpper
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e))
          (annularCanonicalLaterMidpointBandTaggedTupleFamily
            rho N k hr mode hmode e)
      have hdiff := (le_abs_self
        (gaussMovingHeterogeneousApproximationTupleSum
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (annularCanonicalLaterMidpointBandTaggedTupleFamily
              rho N k hr mode hmode e) -
          gaussMovingHeterogeneousDigitTupleSum
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (annularCanonicalLaterMidpointBandTaggedTupleFamily
              rho N k hr mode hmode e))).trans habs
      linarith
    _ =
      (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        gaussMovingHeterogeneousDigitTupleSum
          (Real.log (N : ℝ))
          (gaussPrescribedParityOrientedLower
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e))
          (gaussPrescribedParityOrientedUpper
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e))
          (annularCanonicalLaterMidpointBandTaggedTupleFamily
            rho N k hr mode hmode e)) +
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          ∑ t ∈
              annularCanonicalLaterMidpointBandTaggedTupleFamily
                rho N k hr mode hmode e,
            gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                  (Real.log (N : ℝ))
                  (gaussPrescribedParityOrientedLower
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e))
                  (gaussPrescribedParityOrientedUpper
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e)) t ∆
                gaussHeterogeneousDigitWindowTupleEvent
                  (Real.log (N : ℝ))
                  (gaussPrescribedParityOrientedLower
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e))
                  (gaussPrescribedParityOrientedUpper
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e)) t) := by
      rw [Finset.sum_add_distrib]
    _ ≤
      (∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        gaussMovingHeterogeneousDigitTupleSum
          (Real.log (N : ℝ))
          (gaussPrescribedParityOrientedLower
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e))
          (gaussPrescribedParityOrientedUpper
            (flattenedAnnularParity e)
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e))
          (annularCanonicalLaterMidpointBandTaggedTupleFamily
            rho N k hr mode hmode e)) +
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          ∑ t ∈ canonicalAnnularGridTupleFamily N k e,
            gaussMeasure.real
              (gaussHeterogeneousApproximationTupleEvent
                  (Real.log (N : ℝ))
                  (gaussPrescribedParityOrientedLower
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e))
                  (gaussPrescribedParityOrientedUpper
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e)) t ∆
                gaussHeterogeneousDigitWindowTupleEvent
                  (Real.log (N : ℝ))
                  (gaussPrescribedParityOrientedLower
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e))
                  (gaussPrescribedParityOrientedUpper
                    (flattenedAnnularParity e)
                    (flattenedAnnularSignedLower ε A e)
                    (flattenedAnnularSignedUpper ε A e)) t) := by
      have hband :
          (∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            ∑ t ∈
                annularCanonicalLaterMidpointBandTaggedTupleFamily
                  rho N k hr mode hmode e,
              gaussMeasure.real
                (gaussHeterogeneousApproximationTupleEvent
                    (Real.log (N : ℝ))
                    (gaussPrescribedParityOrientedLower
                      (flattenedAnnularParity e)
                      (flattenedAnnularSignedLower ε A e)
                      (flattenedAnnularSignedUpper ε A e))
                    (gaussPrescribedParityOrientedUpper
                      (flattenedAnnularParity e)
                      (flattenedAnnularSignedLower ε A e)
                      (flattenedAnnularSignedUpper ε A e)) t ∆
                  gaussHeterogeneousDigitWindowTupleEvent
                    (Real.log (N : ℝ))
                    (gaussPrescribedParityOrientedLower
                      (flattenedAnnularParity e)
                      (flattenedAnnularSignedLower ε A e)
                      (flattenedAnnularSignedUpper ε A e))
                    (gaussPrescribedParityOrientedUpper
                      (flattenedAnnularParity e)
                      (flattenedAnnularSignedLower ε A e)
                      (flattenedAnnularSignedUpper ε A e)) t)) ≤
            ∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              ∑ t ∈ canonicalAnnularGridTupleFamily N k e,
                gaussMeasure.real
                  (gaussHeterogeneousApproximationTupleEvent
                      (Real.log (N : ℝ))
                      (gaussPrescribedParityOrientedLower
                        (flattenedAnnularParity e)
                        (flattenedAnnularSignedLower ε A e)
                        (flattenedAnnularSignedUpper ε A e))
                      (gaussPrescribedParityOrientedUpper
                        (flattenedAnnularParity e)
                        (flattenedAnnularSignedLower ε A e)
                        (flattenedAnnularSignedUpper ε A e)) t ∆
                    gaussHeterogeneousDigitWindowTupleEvent
                      (Real.log (N : ℝ))
                      (gaussPrescribedParityOrientedLower
                        (flattenedAnnularParity e)
                        (flattenedAnnularSignedLower ε A e)
                        (flattenedAnnularSignedUpper ε A e))
                      (gaussPrescribedParityOrientedUpper
                        (flattenedAnnularParity e)
                        (flattenedAnnularSignedLower ε A e)
                        (flattenedAnnularSignedUpper ε A e)) t) := by
        apply Finset.sum_le_sum
        intro e _he
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (annularCanonicalLaterMidpointBandTupleFamily_subset_canonical
            rho N k hr e (mode e) (hmode e))
          (fun _t _ht _hnot ↦ measureReal_nonneg)
      simpa only [add_comm] using!
        add_le_add_right hband
          (∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            gaussMovingHeterogeneousDigitTupleSum
              (Real.log (N : ℝ))
              (gaussPrescribedParityOrientedLower
                (flattenedAnnularParity e)
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e))
              (gaussPrescribedParityOrientedUpper
                (flattenedAnnularParity e)
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e))
              (annularCanonicalLaterMidpointBandTaggedTupleFamily
                rho N k hr mode hmode e))

set_option maxHeartbeats 200000

/-- The Gauss one-digit mass of every tagged moving midpoint family is
bounded by the explicit mode-independent envelope.  No limiting density
of the moving family is used: only its literal cardinal bound and the
quasi-Bernoulli one-digit estimate enter. -/
theorem
    annularCanonicalGaussMidpointBandDigitMass_le_upper
    {ε A rho : ℝ} {N : ℕ} (hN : 1 < N)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : ∀ e, mode e ≠ 0) :
    (2 * Real.log 2) *
        annularCanonicalGaussOrientedMidpointBandDigitMass
          ε A rho N k hr mode hmode ≤
      annularCanonicalMidpointBandDigitMassUpper ε A rho N k := by
  unfold annularCanonicalGaussOrientedMidpointBandDigitMass
  have hlogTwo : 0 ≤ 2 * Real.log 2 := by positivity
  calc
    (2 * Real.log 2) *
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          gaussMovingHeterogeneousDigitTupleSum
            (Real.log (N : ℝ))
            (gaussPrescribedParityOrientedLower
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (gaussPrescribedParityOrientedUpper
              (flattenedAnnularParity e)
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e))
            (annularCanonicalLaterMidpointBandTaggedTupleFamily
              rho N k hr mode hmode e) ≤
      (2 * Real.log 2) *
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          ((MixedOccurrenceCount k *
            ((2 * annularMidpointBandWidth rho N) *
              annularDepthAmbientSize N ^
                (MixedOccurrenceCount k - 1)) : ℕ) : ℝ) *
          ((7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
            ∏ j, gaussMeasure.real
              (scaledGaussFirstDigitWindow
                (Real.log (N : ℝ))
                (gaussPrescribedParityOrientedLower
                  (flattenedAnnularParity e)
                  (flattenedAnnularSignedLower ε A e)
                  (flattenedAnnularSignedUpper ε A e) j)
                (gaussPrescribedParityOrientedUpper
                  (flattenedAnnularParity e)
                  (flattenedAnnularSignedLower ε A e)
                  (flattenedAnnularSignedUpper ε A e) j))) := by
      apply mul_le_mul_of_nonneg_left _ hlogTwo
      apply Finset.sum_le_sum
      intro e _he
      let lower : Fin (MixedOccurrenceCount k) → ℝ :=
        gaussPrescribedParityOrientedLower
          (flattenedAnnularParity e)
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
      let upper : Fin (MixedOccurrenceCount k) → ℝ :=
        gaussPrescribedParityOrientedUpper
          (flattenedAnnularParity e)
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
      let tuples : Finset (Fin (MixedOccurrenceCount k) → ℕ) :=
        annularCanonicalLaterMidpointBandTaggedTupleFamily
          rho N k hr mode hmode e
      have hchronological :
          ∀ t ∈ tuples, IsChronologicalNatTuple t := by
        intro t ht
        exact canonicalAnnularGridTupleFamily_chronological N k e t
          (annularCanonicalLaterMidpointBandTupleFamily_subset_canonical
            rho N k hr e (mode e) (hmode e) ht)
      have hcard :
          (tuples.card : ℝ) ≤
            (MixedOccurrenceCount k *
              ((2 * annularMidpointBandWidth rho N) *
                annularDepthAmbientSize N ^
                  (MixedOccurrenceCount k - 1)) : ℕ) := by
        exact_mod_cast
          card_annularCanonicalLaterMidpointBandTupleFamily_le
            hN hgrid k hr htime e (mode e) (hmode e)
      calc
        gaussMovingHeterogeneousDigitTupleSum
            (Real.log (N : ℝ)) lower upper tuples ≤
          (tuples.card : ℝ) *
            ((7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
              ∏ j, gaussMeasure.real
                (scaledGaussFirstDigitWindow
                  (Real.log (N : ℝ)) (lower j) (upper j))) :=
          gaussMovingHeterogeneousDigitTupleSum_le_card_mul
            hr lower upper tuples hchronological
        _ ≤
          (MixedOccurrenceCount k *
            ((2 * annularMidpointBandWidth rho N) *
              annularDepthAmbientSize N ^
                (MixedOccurrenceCount k - 1)) : ℕ) *
            ((7 : ℝ) ^ (MixedOccurrenceCount k - 1) *
              ∏ j, gaussMeasure.real
                (scaledGaussFirstDigitWindow
                  (Real.log (N : ℝ)) (lower j) (upper j))) := by
          exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = annularCanonicalMidpointBandDigitMassUpper ε A rho N k := by
      unfold annularCanonicalMidpointBandDigitMassUpper
      rw [Finset.mul_sum, Finset.mul_sum]
      ring

theorem initialSeparatedCanonicalAnnularGridTupleFamily_subset_early
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :
    initialSeparatedCanonicalAnnularGridTupleFamily N k hr e ⊆
      earlyCanonicalAnnularGridTupleFamily N k hr e := by
  intro t ht
  have ht' := mem_earlyFirstNatTupleFamily_iff.mp ht
  apply mem_earlyFirstNatTupleFamily_iff.mpr
  refine ⟨?_, ht'.2⟩
  exact
    (mem_separatedNatTupleFamily_iff.mp ht'.1).1

/-- The initial-depth part of the separated marked Fourier aggregate
vanishes for arbitrary tag-dependent modes.  This closes the time-zero
edge without invoking any oscillatory cancellation. -/
theorem
    tendsto_annularCanonicalUniformInitialSeparatedMarkedFourier_zero
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ) :
    Tendsto
      (fun N : ℕ ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (initialSeparatedCanonicalAnnularGridTupleFamily N k hr e))
      atTop (nhds 0) := by
  have hmass :=
    tendsto_annularCanonicalUniformEarlyMass_zero
      hε hεA hgrid k hr htime hsigned
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _N ↦ norm_nonneg _
  · exact Eventually.of_forall fun N ↦ by
      calc
        ‖∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (mode e)
              (initialSeparatedCanonicalAnnularGridTupleFamily
                N k hr e)‖ ≤
            ∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              ‖uniformMovingSignedMarkedFourierTupleSum
                N (Real.log (N : ℝ))
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)
                (mode e)
                (initialSeparatedCanonicalAnnularGridTupleFamily
                  N k hr e)‖ :=
          norm_sum_le _ _
        _ ≤ ∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            movingSignedApproximationTupleMassSum
              uniform01Measure (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (initialSeparatedCanonicalAnnularGridTupleFamily
                N k hr e) := by
          apply Finset.sum_le_sum
          intro e _he
          exact norm_movingSignedMarkedFourierTupleSum_le_mass
            uniform01Measure N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (initialSeparatedCanonicalAnnularGridTupleFamily N k hr e)
        _ ≤ aggregateUniformMovingSignedApproximationTupleMassSum
              (β := Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k)
              (Real.log (N : ℝ))
              (fun e ↦ flattenedAnnularSignedLower ε A e)
              (fun e ↦ flattenedAnnularSignedUpper ε A e)
              (fun e ↦ earlyCanonicalAnnularGridTupleFamily N k hr e) := by
          unfold aggregateUniformMovingSignedApproximationTupleMassSum
            aggregateMovingSignedApproximationTupleMassSum
            movingSignedApproximationTupleMassSum
          apply Finset.sum_le_sum
          intro e _he
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (initialSeparatedCanonicalAnnularGridTupleFamily_subset_early
              N k hr e)
            (fun _t _ht _hnot ↦ by positivity)
  · exact hmass

/-- Exact partition of one separated Fourier coefficient into its
initial-depth and interior-depth parts. -/
theorem
    uniformMovingSignedMarkedFourierTupleSum_separated_eq_initial_add_interior
    {ε A : ℝ} {grid N : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ) :
    uniformMovingSignedMarkedFourierTupleSum
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        mode
        (separatedCanonicalAnnularGridTupleFamily N k e) =
      uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (initialSeparatedCanonicalAnnularGridTupleFamily N k hr e) +
        uniformMovingSignedMarkedFourierTupleSum
          N (Real.log (N : ℝ))
          (flattenedAnnularSignedLower ε A e)
          (flattenedAnnularSignedUpper ε A e)
          mode
          (interiorSeparatedCanonicalAnnularGridTupleFamily N k hr e) := by
  classical
  let f : (Fin (MixedOccurrenceCount k) → ℕ) → ℂ :=
    fun times ↦
      ∫ x, gaussMovingSignedMarkedTupleIntegrand
        N (Real.log (N : ℝ))
        (flattenedAnnularSignedLower ε A e)
        (flattenedAnnularSignedUpper ε A e)
        mode times x ∂uniform01Measure
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not
      (separatedCanonicalAnnularGridTupleFamily N k e)
      (fun t ↦ annularSeparationGap N ≤ t ⟨0, hr⟩) f
  simpa only [uniformMovingSignedMarkedFourierTupleSum,
    movingSignedMarkedFourierTupleSum,
    initialSeparatedCanonicalAnnularGridTupleFamily,
    interiorSeparatedCanonicalAnnularGridTupleFamily,
    earlyFirstNatTupleFamily, lateFirstNatTupleFamily,
    not_le, f] using! hpartition.symm.trans (add_comm _ _)

/-- Thus proving cancellation on the interior separated family is enough
for the full separated block. -/
theorem
    tendsto_annularCanonicalUniformSeparatedMarkedFourier_zero_of_interior
    {ε A : ℝ} (hε : 0 < ε) (hεA : ε < A)
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (hsigned : ∀ i, 0 < k i → i.signed.1 < grid)
    (mode :
      (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
        Fin (MixedOccurrenceCount k) → ℤ)
    (hinterior :
      Tendsto
        (fun N : ℕ ↦
          ∑ e : Fin (MixedOccurrenceCount k) ≃
              GaussPrefixMixedOccurrence k,
            uniformMovingSignedMarkedFourierTupleSum
              N (Real.log (N : ℝ))
              (flattenedAnnularSignedLower ε A e)
              (flattenedAnnularSignedUpper ε A e)
              (mode e)
              (interiorSeparatedCanonicalAnnularGridTupleFamily
                N k hr e))
        atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ ↦
        ∑ e : Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k,
          uniformMovingSignedMarkedFourierTupleSum
            N (Real.log (N : ℝ))
            (flattenedAnnularSignedLower ε A e)
            (flattenedAnnularSignedUpper ε A e)
            (mode e)
            (separatedCanonicalAnnularGridTupleFamily N k e))
      atTop (nhds 0) := by
  have hinitial :=
    tendsto_annularCanonicalUniformInitialSeparatedMarkedFourier_zero
      hε hεA hgrid k hr htime hsigned mode
  have hadd := hinitial.add hinterior
  have haddZero :
      Tendsto
        (fun N : ℕ ↦
          (∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              uniformMovingSignedMarkedFourierTupleSum
                N (Real.log (N : ℝ))
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)
                (mode e)
                (initialSeparatedCanonicalAnnularGridTupleFamily
                  N k hr e)) +
            ∑ e : Fin (MixedOccurrenceCount k) ≃
                GaussPrefixMixedOccurrence k,
              uniformMovingSignedMarkedFourierTupleSum
                N (Real.log (N : ℝ))
                (flattenedAnnularSignedLower ε A e)
                (flattenedAnnularSignedUpper ε A e)
                (mode e)
                (interiorSeparatedCanonicalAnnularGridTupleFamily
                  N k hr e))
        atTop (nhds 0) := by
    simpa only [add_zero] using! hadd
  apply haddZero.congr'
  filter_upwards with N
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  exact
    (uniformMovingSignedMarkedFourierTupleSum_separated_eq_initial_add_interior
      (ε := ε) (A := A) k hr e (mode e)).symm

end

end Erdos1002
