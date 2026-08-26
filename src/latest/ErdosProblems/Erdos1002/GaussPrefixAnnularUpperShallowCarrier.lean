import ErdosProblems.Erdos1002.GaussPrefixDelayedCarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Shallow oscillatory carrier for upper-retained annular tuples

The delayed depth is the correct cutoff for measurability and mixing, but
it is too deep for oscillatory cancellation.  Here we introduce the
shallow cutoff

`d = m - g`,

where `m` is the midpoint split and `g` is the retained half-band gap.
Every selected prefix coordinate lies at or before `d`, and no selected
coordinate is lost when the cutoff is moved from `m` (or the delayed
freezing depth) to `d`.  At this cutoff the exact midpoint arithmetic gives

`2 d + 2 g ≤ H + s`,

where `s` is the last nonzero depth and `H` is the ambient horizon.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUpperShallowCarrierPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {rho : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- The cutoff used for the oscillatory cylinder sum. -/
def annularUpperRetainedShallowSplitDepth
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) : ℕ :=
  annularUpperRetainedSplitDepth p - annularUpperRetainedGap rho N

/-- The last nonzero chronological depth lies before the midpoint split. -/
theorem annularUpperRetained_centerDepth_le_split
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N) :
    annularUpperRetainedTimes p
        (annularLastNonzeroIndex (mode p.1) (hmode p.1)) ≤
      annularUpperRetainedSplitDepth p := by
  let s := annularLastNonzeroIndex (mode p.1) (hmode p.1)
  have hslt :
      annularUpperRetainedTimes p s <
        annularDepthAmbientSize N :=
    canonicalAnnularGridTupleFamily_lt_ambient
      hgrid k htime hN p.1 (annularUpperRetainedTimes p)
      (annularUpperRetainedTimes_mem_canonical p) s
  unfold annularUpperRetainedSplitDepth midpointPrefixSplitDepth
  dsimp only [s] at hslt ⊢
  omega

/-- Consequently the retained gap itself is no larger than the split. -/
theorem annularUpperRetained_gap_le_split
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularUpperRetainedGap rho N ≤
      annularUpperRetainedSplitDepth p := by
  let s := annularLastNonzeroIndex (mode p.1) (hmode p.1)
  have hs :
      annularUpperRetainedTimes p s ≤
        annularUpperRetainedSplitDepth p :=
    annularUpperRetained_centerDepth_le_split hgrid htime p hN
  have hsg :=
    (annularUpperRetainedRealization_gap_package
      hgrid htime p hN hW).1 s hs
  omega

/-- Subtracting the gap and then restoring it recovers the midpoint
split exactly. -/
theorem annularUpperRetained_shallowSplit_add_gap
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularUpperRetainedShallowSplitDepth p +
        annularUpperRetainedGap rho N =
      annularUpperRetainedSplitDepth p := by
  unfold annularUpperRetainedShallowSplitDepth
  exact Nat.sub_add_cancel
    (annularUpperRetained_gap_le_split hgrid htime p hN hW)

/-- A selected coordinate is in the shallow prefix exactly when it is in
the original midpoint prefix. -/
theorem annularUpperRetained_le_shallow_iff_le_split
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (j : Fin (MixedOccurrenceCount k)) :
    annularUpperRetainedTimes p j ≤
        annularUpperRetainedShallowSplitDepth p ↔
      annularUpperRetainedTimes p j ≤
        annularUpperRetainedSplitDepth p := by
  constructor
  · intro hj
    exact hj.trans (Nat.sub_le _ _)
  · intro hj
    have hjg :=
      (annularUpperRetainedRealization_gap_package
        hgrid htime p hN hW).1 j hj
    unfold annularUpperRetainedShallowSplitDepth
    omega

/-- The center itself survives at the shallow cutoff. -/
theorem annularUpperRetained_centerDepth_le_shallow
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    annularUpperRetainedTimes p
        (annularLastNonzeroIndex (mode p.1) (hmode p.1)) ≤
      annularUpperRetainedShallowSplitDepth p :=
  (annularUpperRetained_le_shallow_iff_le_split
    hgrid htime p hN hW _).2
      (annularUpperRetained_centerDepth_le_split hgrid htime p hN)

/-- Labeled form of the shallow-prefix equivalence. -/
theorem annularUpperRetained_labeled_le_shallow_iff_le_split
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (z : GaussPrefixMixedOccurrence k) :
    ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) ≤
        annularUpperRetainedShallowSplitDepth p ↔
      ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) ≤
        annularUpperRetainedSplitDepth p := by
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
    annularUpperRetained_le_shallow_iff_le_split
      hgrid htime p hN hW j

/-- Moving from the delayed freezing depth back to the shallow cutoff
does not change the literal selected prefix character. -/
theorem annularUpperRetained_delayedPrefixCharacter_eq_shallow
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N)
    (B : AnnularGridIndex grid → Set (ℝ × ℝ × ℝ))
    (x : ℝ) :
    gaussPrefixMarkedMixedPrefixCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularUpperRetainedRealization p).1
        (annularUpperRetainedDelayedSplitDepth p) x =
      gaussPrefixMarkedMixedPrefixCharacter N B k
        (unflattenedAnnularFourierMode p.1 (mode p.1))
        (annularUpperRetainedRealization p).1
        (annularUpperRetainedShallowSplitDepth p) x := by
  unfold gaussPrefixMarkedMixedPrefixCharacter
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hdelayed :
      ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) ≤
          annularUpperRetainedDelayedSplitDepth p ↔
        ((annularUpperRetainedRealization p).1 z.1 z.2 : ℕ) ≤
          annularUpperRetainedSplitDepth p := by
    rw [← not_lt, ← not_lt,
      annularUpperRetained_labeled_after_delayed_iff_after_split
        hgrid htime p hN hW z]
  rw [hdelayed,
    annularUpperRetained_labeled_le_shallow_iff_le_split
      hgrid htime p hN hW z]

/-- Exact arithmetic behind the decaying shallow-carrier exponent. -/
theorem annularUpperRetained_two_shallow_add_two_gap_le_ambient_add_center
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N)
    (hW : 0 < annularMidpointBandWidth rho N) :
    2 * annularUpperRetainedShallowSplitDepth p +
        2 * annularUpperRetainedGap rho N ≤
      annularDepthAmbientSize N +
        annularUpperRetainedTimes p
          (annularLastNonzeroIndex (mode p.1) (hmode p.1)) := by
  have hrestore :=
    annularUpperRetained_shallowSplit_add_gap
      hgrid htime p hN hW
  calc
    2 * annularUpperRetainedShallowSplitDepth p +
          2 * annularUpperRetainedGap rho N =
        2 * (annularUpperRetainedShallowSplitDepth p +
          annularUpperRetainedGap rho N) := by omega
    _ = 2 * annularUpperRetainedSplitDepth p := by rw [hrestore]
    _ ≤ annularDepthAmbientSize N +
          annularUpperRetainedTimes p
            (annularLastNonzeroIndex (mode p.1) (hmode p.1)) := by
      unfold annularUpperRetainedSplitDepth midpointPrefixSplitDepth
      omega

end

end Erdos1002
