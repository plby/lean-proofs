import ErdosProblems.Erdos1002.GaussPrefixAnnularUpperShallowCarrier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A uniform floor for the delayed upper-retained freezing depth

Every upper-retained tuple belongs to the late-first family.  Its first
selected depth is therefore at least the canonical separation gap.  Since
the tuple is chronological, that first depth is no larger than the last
nonzero selected depth; the latter lies before the midpoint split.  The
delayed freezing depth is obtained by adding a nonnegative offset to that
split.  This file records the resulting lower bound explicitly.
-/

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularUpperDelayedFloorPropDecidable
    (P : Prop) : Decidable P := Classical.propDecidable P

variable {rho : ℝ} {N grid : ℕ}
variable {k : AnnularGridIndex grid → ℕ}
variable {hr : 0 < MixedOccurrenceCount k}
variable
  {mode :
    (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) →
      Fin (MixedOccurrenceCount k) → ℤ}
variable {hmode : ∀ e, mode e ≠ 0}

/-- The first selected depth is no larger than the last nonzero selected
depth.  This includes the endpoint case in which those indices coincide. -/
theorem annularUpperRetained_firstDepth_le_centerDepth
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode) :
    annularUpperRetainedTimes p ⟨0, hr⟩ ≤
      annularUpperRetainedTimes p
        (annularLastNonzeroIndex (mode p.1) (hmode p.1)) := by
  let first : Fin (MixedOccurrenceCount k) := ⟨0, hr⟩
  let center : Fin (MixedOccurrenceCount k) :=
    annularLastNonzeroIndex (mode p.1) (hmode p.1)
  have hchronological :
      IsChronologicalNatTuple (annularUpperRetainedTimes p) :=
    canonicalAnnularGridTupleFamily_chronological
      N k p.1 (annularUpperRetainedTimes p)
      (annularUpperRetainedTimes_mem_canonical p)
  by_cases hfc : first = center
  · exact
      (congrArg (annularUpperRetainedTimes p) hfc).le
  · have hfirstLe : first ≤ center := by
      apply Fin.le_iff_val_le_val.mpr
      dsimp only [first]
      omega
    have hfirstLt : first < center := lt_of_le_of_ne hfirstLe hfc
    exact
      (Nat.le_add_right
        (annularUpperRetainedTimes p first) 1).trans
        (hchronological first center hfirstLt)

/-- The canonical separation gap is a uniform lower bound for every
upper-retained delayed freezing depth. -/
theorem annularSeparationGap_le_annularUpperRetainedDelayedSplitDepth
    (hgrid : 0 < grid)
    (htime : ∀ i, 0 < k i → i.time.1 < grid)
    (p : AnnularUpperRetainedTaggedTuple rho N k hr mode hmode)
    (hN : 1 < N) :
    annularSeparationGap N ≤
      annularUpperRetainedDelayedSplitDepth p := by
  have hupper :=
    (mem_laterUpperMidpointNatTupleFamily_iff.mp p.2.2).1
  have hfirst :
      annularSeparationGap N ≤
        annularUpperRetainedTimes p ⟨0, hr⟩ :=
    (mem_lateFirstNatTupleFamily_iff.mp hupper).2
  have hfirstCenter :
      annularUpperRetainedTimes p ⟨0, hr⟩ ≤
        annularUpperRetainedTimes p
          (annularLastNonzeroIndex (mode p.1) (hmode p.1)) :=
    annularUpperRetained_firstDepth_le_centerDepth p
  have hcenterSplit :
      annularUpperRetainedTimes p
          (annularLastNonzeroIndex (mode p.1) (hmode p.1)) ≤
        annularUpperRetainedSplitDepth p :=
    annularUpperRetained_centerDepth_le_split hgrid htime p hN
  have hsplitDelayed :
      annularUpperRetainedSplitDepth p ≤
        annularUpperRetainedDelayedSplitDepth p := by
    unfold annularUpperRetainedDelayedSplitDepth
    omega
  exact
    hfirst.trans
      (hfirstCenter.trans (hcenterSplit.trans hsplitDelayed))

/-- The cylinder-density decay at any depth above the separation gap is
dominated, up to one fixed factor, by the standard Gauss transfer decay.
The factor absorbs the single parity loss caused by integer division by
two. -/
theorem quarter_pow_half_le_transferDecay_of_le
    {gap depth : ℕ} (hgapDepth : gap ≤ depth) :
    (1 / 4 : ℝ) ^ (depth / 2) ≤
      (540 / 527 : ℝ) * (527 / 540 : ℝ) ^ gap := by
  let q : ℝ := 527 / 540
  let theta : ℝ := 540 / 527
  have hp0 : (0 : ℝ) < 1 / 4 := by norm_num
  have hp1 : (1 / 4 : ℝ) < 1 := by norm_num
  have hq0 : 0 < q := by
    dsimp only [q]
    norm_num
  have hq1 : q < 1 := by
    dsimp only [q]
    norm_num
  have hdiv : gap / 2 ≤ depth / 2 :=
    Nat.div_le_div_right hgapDepth
  have hfirst :
      (1 / 4 : ℝ) ^ (depth / 2) ≤
        (1 / 4 : ℝ) ^ (gap / 2) :=
    (pow_le_pow_iff_right_of_lt_one₀ hp0 hp1).2 hdiv
  have hbase : (1 / 4 : ℝ) ≤ q ^ 2 := by
    dsimp only [q]
    norm_num
  have hsecond :
      (1 / 4 : ℝ) ^ (gap / 2) ≤
        (q ^ 2) ^ (gap / 2) :=
    pow_le_pow_left₀ (by positivity) hbase _
  have hexponent : gap ≤ 2 * (gap / 2) + 1 := by omega
  have hthird :
      q ^ (2 * (gap / 2) + 1) ≤ q ^ gap :=
    (pow_le_pow_iff_right_of_lt_one₀ hq0 hq1).2 hexponent
  have hfactor :
      q ^ (2 * (gap / 2)) =
        theta * q ^ (2 * (gap / 2) + 1) := by
    dsimp only [q, theta]
    rw [pow_succ]
    field_simp
  calc
    (1 / 4 : ℝ) ^ (depth / 2) ≤
        (1 / 4 : ℝ) ^ (gap / 2) := hfirst
    _ ≤ (q ^ 2) ^ (gap / 2) := hsecond
    _ = q ^ (2 * (gap / 2)) := by rw [← pow_mul]
    _ = theta * q ^ (2 * (gap / 2) + 1) := hfactor
    _ ≤ theta * q ^ gap :=
      mul_le_mul_of_nonneg_left hthird (by positivity)
    _ = (540 / 527 : ℝ) * (527 / 540 : ℝ) ^ gap := by
      rfl

end

end Erdos1002
