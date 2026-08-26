import ErdosProblems.Erdos1002.GaussPrefixAnnularLateFutureBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Delayed prefix freezing for the upper retained annular family

The midpoint gap may be used twice.  We freeze the prefix not at the raw
midpoint `m`, but at

`b = m + ⌊g / 2⌋`,

where `g` is the retained midpoint gap.  No selected coordinate lies
between `m` and `b`.  The prefix therefore contains exactly the same
selected occurrences, while both of the following margins remain:

* prefix coordinates lie well before the freezing depth `b`;
* future coordinates lie at least `g - ⌊g / 2⌋` after `b`.

All natural-number rounding identities are recorded explicitly.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularDelayedFreezingPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {rho : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- Half of the already-retained midpoint gap is spent by moving the
freezing depth to the right. -/
def annularUpperRetainedFreezingOffset (rho : ℝ) (N : ℕ) : ℕ :=
  annularUpperRetainedGap rho N / 2

/-- Prefix freezing depth obtained by moving halfway into the empty band. -/
def annularUpperRetainedDelayedSplitDepth
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : ℕ :=
  annularUpperRetainedSplitDepth p +
    annularUpperRetainedFreezingOffset rho N

/-- The part of the midpoint gap still available for prefix--future
mixing after delaying the freezing depth. -/
def annularUpperRetainedDelayedMixingGap (rho : ℝ) (N : ℕ) : ℕ :=
  annularUpperRetainedGap rho N -
    annularUpperRetainedFreezingOffset rho N

/-- The distance from every selected prefix coordinate to the delayed
freezing depth. -/
def annularUpperRetainedDelayedPrefixMargin (rho : ℝ) (N : ℕ) : ℕ :=
  annularUpperRetainedGap rho N +
    annularUpperRetainedFreezingOffset rho N

theorem annularUpperRetainedFreezingOffset_le_gap
    (rho : ℝ) (N : ℕ) :
    annularUpperRetainedFreezingOffset rho N ≤
      annularUpperRetainedGap rho N := by
  unfold annularUpperRetainedFreezingOffset
  omega

/-- The delayed split followed by its residual mixing gap reaches exactly
the original future base `m + g`. -/
theorem annularUpperRetained_delayedSplit_add_mixingGap
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    annularUpperRetainedDelayedSplitDepth p +
        annularUpperRetainedDelayedMixingGap rho N =
      annularUpperRetainedFutureBase p := by
  unfold annularUpperRetainedDelayedSplitDepth
    annularUpperRetainedDelayedMixingGap
    annularUpperRetainedFreezingOffset
    annularUpperRetainedFutureBase
  omega

/-- The delayed offset diverges for every fixed positive band ratio. -/
theorem tendsto_annularUpperRetainedFreezingOffset_atTop
    (hrho : 0 < rho) :
    Tendsto (annularUpperRetainedFreezingOffset rho) atTop atTop := by
  unfold annularUpperRetainedFreezingOffset
  exact
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_annularUpperRetainedGap_atTop hrho)

/-- The residual delayed mixing gap also diverges. -/
theorem tendsto_annularUpperRetainedDelayedMixingGap_atTop
    (hrho : 0 < rho) :
    Tendsto (annularUpperRetainedDelayedMixingGap rho) atTop atTop := by
  apply Filter.tendsto_atTop_mono
    (f := annularUpperRetainedFreezingOffset rho)
    (g := annularUpperRetainedDelayedMixingGap rho)
  · intro N
    unfold annularUpperRetainedDelayedMixingGap
      annularUpperRetainedFreezingOffset
    omega
  · exact tendsto_annularUpperRetainedFreezingOffset_atTop hrho

/-- The enlarged delayed prefix margin diverges. -/
theorem tendsto_annularUpperRetainedDelayedPrefixMargin_atTop
    (hrho : 0 < rho) :
    Tendsto (annularUpperRetainedDelayedPrefixMargin rho) atTop atTop := by
  apply Filter.tendsto_atTop_mono
    (f := annularUpperRetainedGap rho)
    (g := annularUpperRetainedDelayedPrefixMargin rho)
  · intro N
    exact Nat.le_add_right _ _
  · exact tendsto_annularUpperRetainedGap_atTop hrho

/-- The complete annular horizon is bounded linearly by one plus the
delayed freezing offset.  This is the exact natural-number comparison
needed by polynomial-versus-geometric summation. -/
theorem
    annularDepthAmbientSize_le_two_natCeil_two_div_rho_mul_offset_add_one
    (hrho : 0 < rho) (N : ℕ) :
    annularDepthAmbientSize N ≤
      (2 * ⌈2 / rho⌉₊) *
        (annularUpperRetainedFreezingOffset rho N + 1) := by
  have hbase :=
    annularDepthAmbientSize_le_natCeil_two_div_rho_mul_gap_add_one
      hrho N
  have hround :
      annularUpperRetainedGap rho N + 1 ≤
        2 * (annularUpperRetainedFreezingOffset rho N + 1) := by
    unfold annularUpperRetainedFreezingOffset
    omega
  calc
    annularDepthAmbientSize N ≤
        ⌈2 / rho⌉₊ * (annularUpperRetainedGap rho N + 1) := hbase
    _ ≤ ⌈2 / rho⌉₊ *
        (2 * (annularUpperRetainedFreezingOffset rho N + 1)) :=
      Nat.mul_le_mul_left _ hround
    _ = (2 * ⌈2 / rho⌉₊) *
        (annularUpperRetainedFreezingOffset rho N + 1) := by
      ac_rfl

/-- The same horizon comparison with the residual delayed mixing gap. -/
theorem
    annularDepthAmbientSize_le_two_natCeil_two_div_rho_mul_delayedGap_add_one
    (hrho : 0 < rho) (N : ℕ) :
    annularDepthAmbientSize N ≤
      (2 * ⌈2 / rho⌉₊) *
        (annularUpperRetainedDelayedMixingGap rho N + 1) := by
  have hoff :
      annularUpperRetainedFreezingOffset rho N ≤
        annularUpperRetainedDelayedMixingGap rho N := by
    unfold annularUpperRetainedDelayedMixingGap
      annularUpperRetainedFreezingOffset
    omega
  exact
    (annularDepthAmbientSize_le_two_natCeil_two_div_rho_mul_offset_add_one
      hrho N).trans
      (Nat.mul_le_mul_left _
        (Nat.add_le_add_right hoff 1))

/-! ## The selected-coordinate gap at the delayed split -/

/-- A selected coordinate is after the delayed split exactly when it is
after the original midpoint split. -/
theorem annularUpperRetained_after_delayed_iff_after_split
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (j : Fin (MixedOccurrenceCount k)) :
    annularUpperRetainedDelayedSplitDepth p <
        annularUpperRetainedTimes p j ↔
      annularUpperRetainedSplitDepth p <
        annularUpperRetainedTimes p j := by
  let m := annularUpperRetainedSplitDepth p
  let g := annularUpperRetainedGap rho N
  let u := annularUpperRetainedTimes p j
  have hfuture :=
    (annularUpperRetainedRealization_gap_package
      hgrid htime p hN hW).2.1
  constructor
  · intro h
    unfold annularUpperRetainedDelayedSplitDepth at h
    omega
  · intro h
    have hmg : m + g ≤ u := by
      exact hfuture j (by simpa only [m, u] using! h)
    unfold annularUpperRetainedDelayedSplitDepth
      annularUpperRetainedFreezingOffset
    dsimp only [m, g, u] at hmg ⊢
    omega

/-- Dually, a selected coordinate belongs to the delayed prefix exactly
when it belongs to the midpoint prefix. -/
theorem annularUpperRetained_le_delayed_iff_le_split
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (j : Fin (MixedOccurrenceCount k)) :
    annularUpperRetainedTimes p j ≤
        annularUpperRetainedDelayedSplitDepth p ↔
      annularUpperRetainedTimes p j ≤
        annularUpperRetainedSplitDepth p := by
  rw [← not_lt, ← not_lt,
    annularUpperRetained_after_delayed_iff_after_split
      hgrid htime p hN hW j]

/-- Every selected delayed-prefix coordinate enjoys the full original gap
plus the freezing offset before the delayed split. -/
theorem annularUpperRetained_prefixDepth_add_delayedMargin_le
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (j : Fin (MixedOccurrenceCount k))
    (hj : annularUpperRetainedTimes p j ≤
      annularUpperRetainedDelayedSplitDepth p) :
    annularUpperRetainedTimes p j +
        annularUpperRetainedDelayedPrefixMargin rho N ≤
      annularUpperRetainedDelayedSplitDepth p := by
  have hjm :
      annularUpperRetainedTimes p j ≤
        annularUpperRetainedSplitDepth p :=
    (annularUpperRetained_le_delayed_iff_le_split
      hgrid htime p hN hW j).mp hj
  have hprefix :=
    (annularUpperRetainedRealization_gap_package
      hgrid htime p hN hW).1 j hjm
  unfold annularUpperRetainedDelayedPrefixMargin
    annularUpperRetainedDelayedSplitDepth
  omega

/-- Every selected delayed-future coordinate is separated from the
delayed split by the residual mixing gap. -/
theorem annularUpperRetained_delayedSplit_add_gap_le_futureDepth
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (j : Fin (MixedOccurrenceCount k))
    (hj : annularUpperRetainedDelayedSplitDepth p <
      annularUpperRetainedTimes p j) :
    annularUpperRetainedDelayedSplitDepth p +
        annularUpperRetainedDelayedMixingGap rho N ≤
      annularUpperRetainedTimes p j := by
  have hjm :
      annularUpperRetainedSplitDepth p <
        annularUpperRetainedTimes p j :=
    (annularUpperRetained_after_delayed_iff_after_split
      hgrid htime p hN hW j).mp hj
  have hfuture :=
    (annularUpperRetainedRealization_gap_package
      hgrid htime p hN hW).2.1 j hjm
  rw [annularUpperRetained_delayedSplit_add_mixingGap p]
  simpa only [annularUpperRetainedFutureBase] using! hfuture

/-- The delayed split still lies strictly below the ambient horizon by at
least the whole residual mixing gap.  The proof uses the genuine future
coordinate supplied by upper retention, not an asymptotic rounding
convention. -/
theorem annularUpperRetained_delayedSplit_add_gap_lt_ambient
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularUpperRetainedDelayedSplitDepth p +
        annularUpperRetainedDelayedMixingGap rho N <
      annularDepthAmbientSize N := by
  obtain ⟨j, hj⟩ := annularUpperRetained_exists_after_split p hW
  have hjDelayed :
      annularUpperRetainedDelayedSplitDepth p <
        annularUpperRetainedTimes p j :=
    (annularUpperRetained_after_delayed_iff_after_split
      hgrid htime p hN hW j).2 hj
  have hgap :=
    annularUpperRetained_delayedSplit_add_gap_le_futureDepth
      hgrid htime p hN hW j hjDelayed
  have hbound :=
    canonicalAnnularGridTupleFamily_lt_ambient
      hgrid k htime hN p.1 (annularUpperRetainedTimes p)
      (annularUpperRetainedTimes_mem_canonical p) j
  exact hgap.trans_lt hbound

/-- Fourier modes vanish after the delayed split. -/
theorem annularUpperRetained_mode_zero_after_delayed
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (j : Fin (MixedOccurrenceCount k))
    (hj : annularUpperRetainedDelayedSplitDepth p <
      annularUpperRetainedTimes p j) :
    mode p.1 j = 0 := by
  have hjm :=
    (annularUpperRetained_after_delayed_iff_after_split
      hgrid htime p hN hW j).mp hj
  exact
    (annularUpperRetainedRealization_gap_package
      hgrid htime p hN hW).2.2 j hjm

/-! ## Labeled realization and exact character factorization -/

/-- The same no-coordinate band in the labeled realization. -/
theorem annularUpperRetained_labeled_after_delayed_iff_after_split
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (z : GaussPrefixMixedOccurrence k) :
    annularUpperRetainedDelayedSplitDepth p <
        ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) ↔
      annularUpperRetainedSplitDepth p <
        ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) := by
  let j : Fin (MixedOccurrenceCount k) := p.1.symm z
  have htimeEq :
      annularUpperRetainedTimes p j =
        ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) := by
    have htimes :=
      congrFun (annularUpperRetainedRealization_times p) j
    change
      ((annularUpperRetainedRealization p).1
          (p.1 j).1 (p.1 j).2 : ℕ) =
        annularUpperRetainedTimes p j at htimes
    have hej : p.1 j = z := p.1.apply_symm_apply z
    rw [hej] at htimes
    exact htimes.symm
  simpa only [htimeEq] using!
    annularUpperRetained_after_delayed_iff_after_split
      hgrid htime p hN hW j

/-- Delaying the split does not change the simultaneous selected future
event. -/
theorem annularUpperRetained_futureEvent_delayed_eq_split
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ)) :
    gaussPrefixMarkedMixedFutureEvent N B k
        (annularUpperRetainedRealization p).1
        (annularUpperRetainedDelayedSplitDepth p) =
      gaussPrefixMarkedMixedFutureEvent N B k
        (annularUpperRetainedRealization p).1
        (annularUpperRetainedSplitDepth p) := by
  ext x
  unfold gaussPrefixMarkedMixedFutureEvent
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h z hz
    exact h z
      ((annularUpperRetained_labeled_after_delayed_iff_after_split
        hgrid htime p hN hW z).mpr hz)
  · intro h z hz
    exact h z
      ((annularUpperRetained_labeled_after_delayed_iff_after_split
        hgrid htime p hN hW z).mp hz)

/-- Exact prefix/future indicator factorization at the delayed freezing
depth.  The future event is rewritten back to the original midpoint event,
which is unchanged because the intervening band is empty. -/
theorem annularUpperRetained_character_eq_delayedPrefix_mul_futureIndicator
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ))
    (x : ℝ) :
    gaussPrefixMarkedMixedTupleCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularUpperRetainedRealization p).1 x =
      gaussPrefixMarkedMixedPrefixCharacter N B k
          (unflattenedAnnularFourierMode p.1 (mode p.1))
          (annularUpperRetainedRealization p).1
          (annularUpperRetainedDelayedSplitDepth p) x *
        (gaussPrefixMarkedMixedFutureEvent N B k
          (annularUpperRetainedRealization p).1
          (annularUpperRetainedSplitDepth p)).indicator
            (fun _ ↦ (1 : ℂ)) x := by
  rw [← annularUpperRetained_futureEvent_delayed_eq_split
    hgrid htime p hN hW B]
  apply gaussPrefixMarkedMixedTupleCharacter_eq_prefix_mul_futureIndicator
  intro z hz
  exact annularUpperRetained_labeledMode_zero_after_split
    hgrid htime p hN hW z
      ((annularUpperRetained_labeled_after_delayed_iff_after_split
        hgrid htime p hN hW z).mp hz)

end

end Erdos1002
