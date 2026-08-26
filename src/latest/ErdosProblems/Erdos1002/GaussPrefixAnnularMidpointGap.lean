import ErdosProblems.Erdos1002.GaussPrefixAnnularMidpointSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deterministic prefix--future gaps in the retained upper midpoint case

For a tuple in the upper retained family, split at the integer midpoint
between the ambient horizon and the last nonzero depth.  The deleted open
band then gives a genuine gap of `W / 2` on both sides of this split.
All statements below include the natural-number rounding explicitly.
-/

open Finset

namespace Erdos1002

noncomputable section

/-- Integer midpoint between an ambient horizon and one distinguished
coordinate of a natural tuple. -/
def midpointPrefixSplitDepth
    {r : ℕ} (centerIndex : Fin r) (H : ℕ)
    (t : Fin r → ℕ) : ℕ :=
  (H + t centerIndex) / 2

/-- The half-width which survives integer midpoint rounding. -/
def midpointPrefixFutureGap (W : ℕ) : ℕ :=
  W / 2

/-- Existence of an upper retained coordinate below `H` forces the center
itself to stay at least the full band width below `H`. -/
theorem center_add_width_lt_horizon_of_upper_witness
    {r H W : ℕ} {centerIndex : Fin r} {t : Fin r → ℕ}
    (hbound : ∀ j, t j < H)
    (hupper : ∃ j : Fin r, centerIndex < j ∧
      H + t centerIndex + W ≤ 2 * t j) :
    t centerIndex + W < H := by
  obtain ⟨j, _hj, hjUpper⟩ := hupper
  have hjBound := hbound j
  omega

/-- The center lies on the prefix side of the integer midpoint, with the
surviving half-band gap. -/
theorem center_add_halfWidth_le_midpointPrefixSplitDepth
    {r H W : ℕ} {centerIndex : Fin r} {t : Fin r → ℕ}
    (hcenter : t centerIndex + W ≤ H) :
    t centerIndex + midpointPrefixFutureGap W ≤
      midpointPrefixSplitDepth centerIndex H t := by
  unfold midpointPrefixFutureGap midpointPrefixSplitDepth
  omega

/-- Every coordinate no later than the center lies on the prefix side with
the same half-band gap. -/
theorem le_center_add_halfWidth_le_midpointPrefixSplitDepth
    {r H W : ℕ} {centerIndex j : Fin r} {t : Fin r → ℕ}
    (hjt : t j ≤ t centerIndex)
    (hcenter : t centerIndex + W ≤ H) :
    t j + midpointPrefixFutureGap W ≤
      midpointPrefixSplitDepth centerIndex H t := by
  exact
    (Nat.add_le_add_right hjt _).trans
      (center_add_halfWidth_le_midpointPrefixSplitDepth hcenter)

/-- A later coordinate outside the band and not beyond the midpoint lies
at least `W / 2` before the split.  Positivity of `W` rules out the upper
half-line at a point no larger than the midpoint. -/
theorem later_prefix_add_halfWidth_le_midpointPrefixSplitDepth
    {r H W : ℕ} (hW : 0 < W)
    {centerIndex j : Fin r} {t : Fin r → ℕ}
    (_hj : centerIndex < j)
    (houtside :
      ¬ Nat.dist (2 * t j) (H + t centerIndex) < W)
    (hprefix :
      t j ≤ midpointPrefixSplitDepth centerIndex H t) :
    t j + midpointPrefixFutureGap W ≤
      midpointPrefixSplitDepth centerIndex H t := by
  rcases lower_or_upper_of_not_dist_lt houtside with hlower | hupper
  · unfold midpointPrefixFutureGap midpointPrefixSplitDepth
    omega
  · unfold midpointPrefixSplitDepth at hprefix
    omega

/-- A coordinate strictly beyond the midpoint, outside the band, lies at
least `W / 2` after the split.  The lower half-line is incompatible with
being strictly beyond the midpoint. -/
theorem midpointPrefixSplitDepth_add_halfWidth_le_later_future
    {r H W : ℕ}
    {centerIndex j : Fin r} {t : Fin r → ℕ}
    (_hj : centerIndex < j)
    (houtside :
      ¬ Nat.dist (2 * t j) (H + t centerIndex) < W)
    (hfuture :
      midpointPrefixSplitDepth centerIndex H t < t j) :
    midpointPrefixSplitDepth centerIndex H t +
        midpointPrefixFutureGap W ≤ t j := by
  rcases lower_or_upper_of_not_dist_lt houtside with hlower | hupper
  · unfold midpointPrefixSplitDepth at hfuture
    omega
  · unfold midpointPrefixFutureGap midpointPrefixSplitDepth
    omega

/-- Every upper-half-line witness is genuinely beyond the integer
midpoint when the deleted band has positive width. -/
theorem midpointPrefixSplitDepth_lt_of_upper_witness
    {r H W : ℕ} (hW : 0 < W)
    {centerIndex j : Fin r} {t : Fin r → ℕ}
    (hupper : H + t centerIndex + W ≤ 2 * t j) :
    midpointPrefixSplitDepth centerIndex H t < t j := by
  unfold midpointPrefixSplitDepth
  omega

/-- Complete prefix-side gap for an upper retained chronological tuple. -/
theorem upperRetained_prefixDepth_add_gap_le_split
    {r H W : ℕ} (hW : 0 < W)
    {centerIndex : Fin r} {t : Fin r → ℕ}
    (hmono : StrictMono t)
    (hbound : ∀ j, t j < H)
    (houtside : ∀ j : Fin r, centerIndex < j →
      ¬ Nat.dist (2 * t j) (H + t centerIndex) < W)
    (hupper : ∃ j : Fin r, centerIndex < j ∧
      H + t centerIndex + W ≤ 2 * t j)
    (j : Fin r)
    (hprefix : t j ≤ midpointPrefixSplitDepth centerIndex H t) :
    t j + midpointPrefixFutureGap W ≤
      midpointPrefixSplitDepth centerIndex H t := by
  have hcenter :
      t centerIndex + W ≤ H :=
    (center_add_width_lt_horizon_of_upper_witness
      hbound hupper).le
  by_cases hj : centerIndex < j
  · exact later_prefix_add_halfWidth_le_midpointPrefixSplitDepth
      hW hj (houtside j hj) hprefix
  · have hjle : j ≤ centerIndex := le_of_not_gt hj
    have htj : t j ≤ t centerIndex := hmono.monotone hjle
    exact
      le_center_add_halfWidth_le_midpointPrefixSplitDepth
        htj hcenter

/-- Complete future-side gap for an upper retained chronological tuple. -/
theorem upperRetained_split_add_gap_le_futureDepth
    {r H W : ℕ}
    {centerIndex : Fin r} {t : Fin r → ℕ}
    (hmono : StrictMono t)
    (hcenterMid :
      t centerIndex ≤ midpointPrefixSplitDepth centerIndex H t)
    (houtside : ∀ j : Fin r, centerIndex < j →
      ¬ Nat.dist (2 * t j) (H + t centerIndex) < W)
    (j : Fin r)
    (hfuture : midpointPrefixSplitDepth centerIndex H t < t j) :
    midpointPrefixSplitDepth centerIndex H t +
        midpointPrefixFutureGap W ≤ t j := by
  have hj : centerIndex < j := by
    by_cases hjle : j ≤ centerIndex
    · have htj : t j ≤ t centerIndex := hmono.monotone hjle
      exfalso
      omega
    · exact lt_of_not_ge hjle
  exact midpointPrefixSplitDepth_add_halfWidth_le_later_future
    hj (houtside j hj) hfuture

/-- Every Fourier mode strictly after the midpoint split is zero, since
the distinguished coordinate is the last nonzero chronological mode. -/
theorem mode_eq_zero_of_midpointSplitDepth_lt
    {r H : ℕ} {mode : Fin r → ℤ} (hmode : mode ≠ 0)
    {t : Fin r → ℕ} (hmono : StrictMono t)
    (hcenterMid :
      t (annularLastNonzeroIndex mode hmode) ≤
        midpointPrefixSplitDepth
          (annularLastNonzeroIndex mode hmode) H t)
    (j : Fin r)
    (hj :
      midpointPrefixSplitDepth
          (annularLastNonzeroIndex mode hmode) H t < t j) :
    mode j = 0 := by
  have hindex :
      annularLastNonzeroIndex mode hmode < j := by
    by_cases hjle : j ≤ annularLastNonzeroIndex mode hmode
    · have htj :=
        hmono.monotone hjle
      exfalso
      omega
    · exact lt_of_not_ge hjle
  exact annularLastNonzeroIndex_zero_after mode hmode j hindex

/-- Annular upper retained tuples satisfy the full deterministic package:
the center is on the prefix side, every retained prefix coordinate has a
half-band margin, every future coordinate has a half-band mixing gap, and
all future Fourier modes vanish. -/
theorem annularUpperRetained_midpointGap_package
    {rho : ℝ} {N grid : ℕ}
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (e : Fin (MixedOccurrenceCount k) ≃
      GaussPrefixMixedOccurrence k)
    (mode : Fin (MixedOccurrenceCount k) → ℤ)
    (hmode : mode ≠ 0)
    {t : Fin (MixedOccurrenceCount k) → ℕ}
    (ht :
      t ∈ annularCanonicalLaterUpperMidpointTupleFamily
        rho N k hr e mode hmode)
    (hW : 0 < annularMidpointBandWidth rho N)
    (hbound : ∀ j, t j < annularDepthAmbientSize N) :
    let s := annularLastNonzeroIndex mode hmode
    let m := midpointPrefixSplitDepth s
      (annularDepthAmbientSize N) t
    let gap := midpointPrefixFutureGap
      (annularMidpointBandWidth rho N)
    t s ≤ m ∧
      (∀ j, t j ≤ m → t j + gap ≤ m) ∧
      (∀ j, m < t j → m + gap ≤ t j) ∧
      (∀ j, m < t j → mode j = 0) ∧
      ∃ j, s < j ∧ m < t j := by
  let s := annularLastNonzeroIndex mode hmode
  let H := annularDepthAmbientSize N
  let W := annularMidpointBandWidth rho N
  let m := midpointPrefixSplitDepth s H t
  let gap := midpointPrefixFutureGap W
  have hmem :=
    mem_laterUpperMidpointNatTupleFamily_iff.mp ht
  have htInterior := hmem.1
  have htSeparated :=
    (mem_lateFirstNatTupleFamily_iff.mp htInterior).1
  have htCanonical :=
    (mem_separatedNatTupleFamily_iff.mp htSeparated).1
  have hmono :
      StrictMono t :=
    canonicalAnnularGridTupleFamily_chronological N k e t htCanonical
  have houtside :
      ∀ j : Fin (MixedOccurrenceCount k), s < j →
        ¬ Nat.dist (2 * t j) (H + t s) < W := by
    simpa only [s, H, W] using! hmem.2.1
  have hupper :
      ∃ j : Fin (MixedOccurrenceCount k), s < j ∧
        H + t s + W ≤ 2 * t j := by
    simpa only [s, H, W] using! hmem.2.2
  have hcenter :
      t s + W ≤ H :=
    (center_add_width_lt_horizon_of_upper_witness
      (by simpa only [H] using! hbound) hupper).le
  have hcenterMid : t s ≤ m := by
    have :=
      center_add_halfWidth_le_midpointPrefixSplitDepth
        (centerIndex := s) hcenter
    simpa only [m, gap, Nat.le_add_right] using!
      (Nat.le_add_right (t s) gap).trans this
  refine ⟨hcenterMid, ?_, ?_, ?_, ?_⟩
  · intro j hj
    simpa only [m, gap] using!
      upperRetained_prefixDepth_add_gap_le_split
        hW hmono (by simpa only [H] using! hbound)
        houtside hupper j hj
  · intro j hj
    simpa only [m, gap] using!
      upperRetained_split_add_gap_le_futureDepth
        hmono hcenterMid houtside j hj
  · intro j hj
    exact mode_eq_zero_of_midpointSplitDepth_lt
      hmode hmono (by simpa only [m, s] using! hcenterMid) j
      (by simpa only [m, s] using! hj)
  · obtain ⟨j, hsj, hjUpper⟩ := hupper
    refine ⟨j, hsj, ?_⟩
    exact midpointPrefixSplitDepth_lt_of_upper_witness hW hjUpper

end

end Erdos1002
