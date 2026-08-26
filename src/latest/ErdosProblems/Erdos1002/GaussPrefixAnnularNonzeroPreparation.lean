import ErdosProblems.Erdos1002.GaussPrefixAnnularDepthBoxes
import ErdosProblems.Erdos1002.GaussPrefixAnnularTupleDensity
import ErdosProblems.Erdos1002.GaussPrefixMarkedCarrierGoodEvent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deterministic preparation for annular nonzero Fourier modes

The annular factorial expansion is labeled by grid cells, while the
oscillatory estimates are applied after sorting all selected depths into
one chronological tuple.  This file records the exact changes of
coordinates and proves that separation of the sorted tuple is precisely
the intrinsic separation required by the carrier lemmas.

No probabilistic or Fourier-cancellation assumption is introduced here.
-/

open Filter Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance annularNonzeroPreparationMixedOccurrenceDecidableEq
    {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    DecidableEq (GaussPrefixMixedOccurrence k) :=
  Classical.decEq _

/-! ## Fourier modes before and after chronological sorting -/

/-- Pull a Fourier mode on chronological coordinates back to the labeled
mixed occurrences. -/
def unflattenedAnnularFourierMode
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (i : AnnularGridIndex grid) (j : Fin (k i)) : ℤ :=
  mode (e.symm ⟨i, j⟩)

/-- Pullback and flattening are literal inverses on chronological modes. -/
@[simp] theorem flattenedAnnularFourierMode_unflattened
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ) :
    flattenedAnnularFourierMode e
        (unflattenedAnnularFourierMode e mode) =
      mode := by
  funext j
  simp [flattenedAnnularFourierMode, unflattenedAnnularFourierMode]

/-- Flattening and pullback are literal inverses on labeled modes. -/
@[simp] theorem unflattenedAnnularFourierMode_flattened
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (h : ∀ i, Fin (k i) → ℤ)
    (i : AnnularGridIndex grid) (j : Fin (k i)) :
    unflattenedAnnularFourierMode e
        (flattenedAnnularFourierMode e h) i j =
      h i j := by
  have he :
      e (e.symm (⟨i, j⟩ : GaussPrefixMixedOccurrence k)) =
        (⟨i, j⟩ : GaussPrefixMixedOccurrence k) :=
    e.apply_symm_apply _
  simp only [unflattenedAnnularFourierMode,
    flattenedAnnularFourierMode]
  rw [he]

/-- A nonzero chronological Fourier mode has a nonzero labeled
occurrence after pullback by every occurrence order. -/
theorem exists_unflattenedAnnularFourierMode_ne_zero
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    ∃ z : GaussPrefixMixedOccurrence k,
      unflattenedAnnularFourierMode e mode z.1 z.2 ≠ 0 := by
  classical
  by_cases hex :
      ∃ z : GaussPrefixMixedOccurrence k,
        unflattenedAnnularFourierMode e mode z.1 z.2 ≠ 0
  · exact hex
  · exfalso
    apply hmode
    funext j
    have hz :
        unflattenedAnnularFourierMode e mode
            (e j).1 (e j).2 =
          0 := by
      exact not_ne_iff.mp (not_exists.mp hex (e j))
    simpa [unflattenedAnnularFourierMode] using! hz

/-- Canonical last nonzero chronological index of a fixed nonzero mode.
Unlike the intrinsic occurrence selector below, this index is independent
of the horizon and of the selected depth tuple. -/
noncomputable def annularLastNonzeroIndex
    {r : ℕ} (mode : Fin r → ℤ) (hmode : mode ≠ 0) : Fin r :=
  Classical.choose <| exists_last_nonzero_fin mode <| by
    classical
    by_cases hex : ∃ j, mode j ≠ 0
    · exact hex
    · exfalso
      apply hmode
      funext j
      exact not_ne_iff.mp (not_exists.mp hex j)

theorem annularLastNonzeroIndex_ne_zero
    {r : ℕ} (mode : Fin r → ℤ) (hmode : mode ≠ 0) :
    mode (annularLastNonzeroIndex mode hmode) ≠ 0 :=
  (Classical.choose_spec <| exists_last_nonzero_fin mode <| by
    classical
    by_cases hex : ∃ j, mode j ≠ 0
    · exact hex
    · exfalso
      apply hmode
      funext j
      exact not_ne_iff.mp (not_exists.mp hex j)).1

theorem annularLastNonzeroIndex_zero_after
    {r : ℕ} (mode : Fin r → ℤ) (hmode : mode ≠ 0)
    (j : Fin r) (hj : annularLastNonzeroIndex mode hmode < j) :
    mode j = 0 :=
  (Classical.choose_spec <| exists_last_nonzero_fin mode <| by
    classical
    by_cases hex : ∃ j, mode j ≠ 0
    · exact hex
    · exfalso
      apply hmode
      funext j
      exact not_ne_iff.mp (not_exists.mp hex j)).2 j hj

/-- In every separated chronological tuple, every other nonzero
coordinate lies at least `gap` before the fixed last nonzero index. -/
theorem gap_before_annularLastNonzeroIndex
    {r gap : ℕ} (mode : Fin r → ℤ) (hmode : mode ≠ 0)
    (t : Fin r → ℕ) (hsep : IsSeparatedNatTuple gap t)
    (j : Fin r) (hjNe : j ≠ annularLastNonzeroIndex mode hmode)
    (hjMode : mode j ≠ 0) :
    t j + gap ≤ t (annularLastNonzeroIndex mode hmode) := by
  let s := annularLastNonzeroIndex mode hmode
  have hnot : ¬s < j := by
    intro hsj
    exact hjMode (annularLastNonzeroIndex_zero_after mode hmode j hsj)
  have hjs : j < s :=
    lt_of_le_of_ne (le_of_not_gt hnot) hjNe
  exact hsep j s hjs

/-! ## Chronological separation implies intrinsic separation -/

/-- For a tuple whose canonical occurrence order is `e`, separation of
the flattened times implies separation between every pair of labeled
depths. -/
theorem
    isGloballyGapSeparatedMixedDepthTuple_of_fixedOrder
    {ι : Type*} [Fintype ι]
    (N gap : ℕ) (k : ι → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (F : GloballyInjectiveMixedDepthTuple N k)
    (horder : canonicalMixedOccurrenceOrder N k F = e)
    (hsep : IsSeparatedNatTuple gap
      (fixedOrderMixedTimes N k e F)) :
    IsGloballyGapSeparatedMixedDepthTuple N gap k F.1 := by
  intro z z' hzz'
  let a : Fin (MixedOccurrenceCount k) := e.symm z
  let b : Fin (MixedOccurrenceCount k) := e.symm z'
  have hstrict :
      StrictMono (fixedOrderMixedTimes N k e F) := by
    have hcanonical :=
      strictMono_canonicalMixedOccurrenceOrder N k F
    rw [horder] at hcanonical
    simpa only [fixedOrderMixedTimes] using! hcanonical
  have habDepth :
      fixedOrderMixedTimes N k e F a <
        fixedOrderMixedTimes N k e F b := by
    have hea : e a = z := by
      dsimp only [a]
      exact e.apply_symm_apply z
    have heb : e b = z' := by
      dsimp only [b]
      exact e.apply_symm_apply z'
    change
      (F.1 (e a).1 (e a).2 : ℕ) <
        (F.1 (e b).1 (e b).2 : ℕ)
    rw [hea, heb]
    exact hzz'
  have hab : a < b :=
    hstrict.lt_iff_lt.mp habDepth
  have hgap := hsep a b hab
  have hea : e a = z := by
    dsimp only [a]
    exact e.apply_symm_apply z
  have heb : e b = z' := by
    dsimp only [b]
    exact e.apply_symm_apply z'
  change
    (F.1 (e a).1 (e a).2 : ℕ) + gap ≤
      (F.1 (e b).1 (e b).2 : ℕ) at hgap
  rw [hea, heb] at hgap
  exact hgap

/-- Membership in a separated canonical annular family can be lifted
back to one globally injective labeled tuple satisfying the intrinsic gap
condition used by the oscillatory carrier estimates. -/
theorem exists_gapSeparatedMixedDepthTuple_of_mem_canonicalAnnular
    {grid N gap : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalAnnularGridTupleFamily N k e)
    (hsep : IsSeparatedNatTuple gap t) :
    ∃ F : GloballyInjectiveMixedDepthTuple N k,
      canonicalMixedOccurrenceOrder N k F = e ∧
        fixedOrderMixedTimes N k e F = t ∧
        IsGloballyGapSeparatedMixedDepthTuple N gap k F.1 := by
  rcases mem_canonicalMixedOrderParityBoxTimes_iff.mp ht with
    ⟨F, horder, _hbox, htimes⟩
  refine ⟨F, horder, htimes, ?_⟩
  apply isGloballyGapSeparatedMixedDepthTuple_of_fixedOrder
    N gap k e F horder
  simpa only [htimes] using! hsep

/-! ## The last nonzero carrier and its fixed weight budget -/

/-- A separated canonical annular tuple with a nonzero chronological mode
has a labeled realization and a last nonzero labeled occurrence.  Every
other nonzero carrier is at least `gap` depths earlier. -/
theorem
    exists_lastNonzeroOccurrence_of_mem_separated_canonicalAnnular
    {grid N gap : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalAnnularGridTupleFamily N k e)
    (hsep : IsSeparatedNatTuple gap t) :
    ∃ F : GloballyInjectiveMixedDepthTuple N k,
      canonicalMixedOccurrenceOrder N k F = e ∧
        fixedOrderMixedTimes N k e F = t ∧
        ∃ z₀ : GaussPrefixMixedOccurrence k,
          unflattenedAnnularFourierMode e mode z₀.1 z₀.2 ≠ 0 ∧
            ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
              unflattenedAnnularFourierMode e mode z.1 z.2 ≠ 0 →
                (F.1 z.1 z.2 : ℕ) + gap ≤
                  (F.1 z₀.1 z₀.2 : ℕ) := by
  obtain ⟨F, horder, htimes, hSeparated⟩ :=
    exists_gapSeparatedMixedDepthTuple_of_mem_canonicalAnnular
      k e t ht hsep
  obtain ⟨z₀, hz₀, hgap⟩ :=
    exists_lastNonzeroOccurrence_with_gap
      N gap k (unflattenedAnnularFourierMode e mode) F.1
      F.2 hSeparated
      (exists_unflattenedAnnularFourierMode_ne_zero e mode hmode)
  exact ⟨F, horder, htimes, z₀, hz₀, hgap⟩

/-- The gap conclusion at a last nonzero occurrence implies, in
particular, that every strictly later occurrence has Fourier mode zero.
This is the exact hypothesis required by the prefix/future indicator
factorization. -/
theorem modes_zero_strictly_after_lastNonzeroOccurrence
    {ι : Type*} [Fintype ι]
    {N gap : ℕ} {k : ι → ℕ}
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 →
        (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ)) :
    ∀ z : GaussPrefixMixedOccurrence k,
      (F z₀.1 z₀.2 : ℕ) < (F z.1 z.2 : ℕ) →
        h z.1 z.2 = 0 := by
  intro z hzLater
  by_cases hz : h z.1 z.2 = 0
  · exact hz
  · have hzNe : z ≠ z₀ := by
      intro hzz₀
      subst z
      exact (Nat.lt_irrefl _) hzLater
    have hle := hgap z hzNe hz
    omega

/-- For the canonical separated realization selected above, the complete
future block after the last nonzero occurrence is therefore an unmarked
indicator. -/
theorem
    canonicalAnnular_futureCharacter_eq_indicator_after_lastNonzero
    {grid N gap : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalAnnularGridTupleFamily N k e)
    (hsep : IsSeparatedNatTuple gap t)
    (B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ)) :
    ∃ F : GloballyInjectiveMixedDepthTuple N k,
      canonicalMixedOccurrenceOrder N k F = e ∧
        fixedOrderMixedTimes N k e F = t ∧
        ∃ z₀ : GaussPrefixMixedOccurrence k,
          unflattenedAnnularFourierMode e mode z₀.1 z₀.2 ≠ 0 ∧
            ∀ x : ℝ,
              gaussPrefixMarkedMixedFutureCharacter N B k
                  (unflattenedAnnularFourierMode e mode) F.1
                  (F.1 z₀.1 z₀.2 : ℕ) x =
                (gaussPrefixMarkedMixedFutureEvent N B k F.1
                  (F.1 z₀.1 z₀.2 : ℕ)).indicator
                    (fun _ ↦ (1 : ℂ)) x := by
  obtain ⟨F, horder, htimes, z₀, hz₀, hgap⟩ :=
    exists_lastNonzeroOccurrence_of_mem_separated_canonicalAnnular
      k e mode hmode t ht hsep
  refine ⟨F, horder, htimes, z₀, hz₀, ?_⟩
  intro x
  apply gaussPrefixMarkedMixedFutureCharacter_eq_indicator_of_modes_zero
  exact modes_zero_strictly_after_lastNonzeroOccurrence
    (unflattenedAnnularFourierMode e mode) F.1 z₀ hgap

/-- For any fixed finite labeled Fourier assignment, the exponential
carrier budget required by the gap non-cancellation lemma holds
eventually along every gap tending to infinity.  The conclusion is
uniform in the chosen subset and erased distinguished occurrence. -/
theorem eventually_fourierWeightBudget_of_gap_atTop
    {ι : Type*} [Fintype ι]
    {k : ι → ℕ}
    (gap : ℕ → ℕ) (hgap : Tendsto gap atTop atTop)
    (h : ∀ i, Fin (k i) → ℤ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (S : Finset (GaussPrefixMixedOccurrence k))
        (z₀ : GaussPrefixMixedOccurrence k),
        2 * (∑ z ∈ S.erase z₀, |(h z.1 z.2 : ℝ)|) ≤
          ((2 ^ (gap N / 2) : ℕ) : ℝ) := by
  have hgapHalf :
      Tendsto (fun N ↦ gap N / 2) atTop atTop :=
    (Nat.tendsto_div_const_atTop (by norm_num)).comp hgap
  have hpowNat :
      Tendsto (fun N ↦ 2 ^ (gap N / 2)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt
      (show (1 : ℕ) < 2 by norm_num)).comp hgapHalf
  have hpowReal :
      Tendsto (fun N ↦ ((2 ^ (gap N / 2) : ℕ) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  filter_upwards
    [hpowReal.eventually_ge_atTop
      (2 * ∑ z : GaussPrefixMixedOccurrence k,
        |(h z.1 z.2 : ℝ)|)] with N hN
  intro S z₀
  calc
    2 * (∑ z ∈ S.erase z₀, |(h z.1 z.2 : ℝ)|) ≤
        2 * ∑ z : GaussPrefixMixedOccurrence k,
          |(h z.1 z.2 : ℝ)| := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_univ_sum_of_nonneg
        (fun z ↦ abs_nonneg (h z.1 z.2 : ℝ))
    _ ≤ ((2 ^ (gap N / 2) : ℕ) : ℝ) := hN

/-- The preceding fixed-mode budget at the annular square-root
separation gap. -/
theorem eventually_annularSeparationGap_fourierWeightBudget
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (h : ∀ i, Fin (k i) → ℤ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (S : Finset (GaussPrefixMixedOccurrence k))
        (z₀ : GaussPrefixMixedOccurrence k),
        2 * (∑ z ∈ S.erase z₀, |(h z.1 z.2 : ℝ)|) ≤
          ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) :=
  eventually_fourierWeightBudget_of_gap_atTop
    annularSeparationGap tendsto_annularSeparationGap_atTop h

/-- Uniform-in-the-tuple package of all deterministic hypotheses needed
to invoke either the early full-character cylinder estimate or the late
prefix-character estimate.  The occurrence order and Fourier mode are
fixed, but the canonical family, gap, and realizing mixed tuple vary with
`N`. -/
theorem eventually_canonicalAnnular_lastNonzero_and_weightBudgets
    {grid : ℕ} {k : AnnularGridIndex grid → ℕ}
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0) :
    ∀ᶠ N : ℕ in atTop,
      ∀ t : Fin (MixedOccurrenceCount k) → ℕ,
        t ∈ canonicalAnnularGridTupleFamily N k e →
        IsSeparatedNatTuple (annularSeparationGap N) t →
        ∃ F : GloballyInjectiveMixedDepthTuple N k,
          canonicalMixedOccurrenceOrder N k F = e ∧
            fixedOrderMixedTimes N k e F = t ∧
            ∃ z₀ : GaussPrefixMixedOccurrence k,
              unflattenedAnnularFourierMode e mode z₀.1 z₀.2 ≠ 0 ∧
                (∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
                  unflattenedAnnularFourierMode e mode z.1 z.2 ≠ 0 →
                    (F.1 z.1 z.2 : ℕ) + annularSeparationGap N ≤
                      (F.1 z₀.1 z₀.2 : ℕ)) ∧
                2 * (∑ z ∈
                    (Finset.univ :
                      Finset (GaussPrefixMixedOccurrence k)).erase z₀,
                  |(unflattenedAnnularFourierMode e mode
                    z.1 z.2 : ℝ)|) ≤
                  ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) ∧
                ∀ m : ℕ,
                  2 * (∑ z ∈
                      ((Finset.univ :
                          Finset (GaussPrefixMixedOccurrence k)).filter
                        (fun z ↦ (F.1 z.1 z.2 : ℕ) ≤ m)).erase z₀,
                    |(unflattenedAnnularFourierMode e mode
                      z.1 z.2 : ℝ)|) ≤
                    ((2 ^ (annularSeparationGap N / 2) : ℕ) : ℝ) := by
  filter_upwards
    [eventually_annularSeparationGap_fourierWeightBudget
      (unflattenedAnnularFourierMode e mode)] with N hbudget
  intro t ht hsep
  obtain ⟨F, horder, htimes, z₀, hz₀, hgap⟩ :=
    exists_lastNonzeroOccurrence_of_mem_separated_canonicalAnnular
      k e mode hmode t ht hsep
  refine ⟨F, horder, htimes, z₀, hz₀, hgap,
    hbudget Finset.univ z₀, ?_⟩
  intro m
  exact hbudget
    ((Finset.univ :
      Finset (GaussPrefixMixedOccurrence k)).filter
        (fun z ↦ (F.1 z.1 z.2 : ℕ) ≤ m))
    z₀

end

end Erdos1002
