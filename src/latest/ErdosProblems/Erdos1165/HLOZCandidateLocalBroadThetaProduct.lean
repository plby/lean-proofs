/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalLazyCap
import ErdosProblems.Erdos1165.HLOZSourceOrientedThetaProduct

/-!
# Broad one-sided source-Theta product bound

The candidate-local product branch permits a deficit as large as
`ceil (m ^ (7 / 10))`.  Its source balance screen is therefore not the
first-strip screen of width `shellWidth48 m`.  This file records the literal
one-coordinate estimate for the wider, one-sided event which is actually
needed there.

The scalar capacity inequality moves the retained-count lower threshold
down by exactly the broad deficit width.  Consequently a retained count
below that threshold still forces the same `geometricDeviation m` upper-tail
deviation.  No dominance condition is used in this finite-product statement.
-/

open Filter
open scoped BigOperators

namespace Erdos1165.HLOZCandidateLocalBroadThetaProduct

open ExternalProposition44 FiniteDominoProductLaw
open HLOZCandidateLocalLazyCap HLOZNegativeBinomialTruncation
open HLOZProposition48Candidates HLOZShellZeroExternalWindow
open HLOZShellZeroReplacementWindows HLOZSourceOrientedThetaBalance
open HLOZSourceOrientedThetaProduct ScreeningInstantiation
open TilingCappedMarginalization TilingSpatialInsertionFiber

noncomputable section

abbrev DominoTiling := Tilings.Tiling

/-- The largest deficit retained by the source product branch. -/
def candidateLocalBroadWidth48 (m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) ^ (7 / 10 : ℝ))

/-- Scale-only facts for the broad candidate-local window.  The capacity
inequality is data-dependent and is intentionally not part of this record. -/
structure CandidateLocalBroadThetaScaleArithmetic (m : ℕ) : Prop where
  level_pos : 0 < m
  width_pos : 1 ≤ candidateLocalBroadWidth48 m
  width : (candidateLocalBroadWidth48 m : ℝ) ≤ (m : ℝ) / 10
  radius : shellZeroCenterRadius m ≤ (m : ℝ)
  margin : (16 / 15 : ℝ) * shellZeroExternalLow48 m +
    geometricDeviation m ≤ (m : ℝ) + 1
  geometric : geometricDeviation m ≤
    (m + candidateLocalBroadWidth48 m : ℕ)
  theta : thetaLowDeviation m ≤
    (m + candidateLocalBroadWidth48 m : ℕ)
  thick_nonneg : 0 ≤ hlozThickThresholdReal44 m
  low_dom : (candidateLocalBroadWidth48 m : ℝ) + thetaLowDeviation m ≤
    (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ)

/-- One-sided source-window failure for the broad product branch. -/
def broadSourceThetaCoordinateBad
    (m width externalThreshold i v : ℕ) : Prop :=
  v ∈ shellZeroSourceFailureWindow m width i ∧ i < externalThreshold

instance (m width externalThreshold i : ℕ) :
    DecidablePred (broadSourceThetaCoordinateBad
      m width externalThreshold i) :=
  Classical.decPred _

/-- The rounded retained-count lower endpoint leaves the same geometric
deviation margin after the broad deficit width is subtracted. -/
theorem shellZeroExternalLow48_geometric_margin
    {m : ℕ}
    (hradius : shellZeroCenterRadius m ≤ (m : ℝ))
    (hwidthPos : 1 ≤ shellWidth48 m) :
    (16 / 15 : ℝ) * shellZeroExternalLow48 m +
        geometricDeviation m ≤ (m : ℝ) + 1 := by
  unfold shellZeroExternalLow48
  have harg : 0 ≤ (15 / 16 : ℝ) *
      ((m : ℝ) - shellZeroCenterRadius m) := by positivity
  have hceil := Nat.ceil_lt_add_one harg
  unfold shellZeroCenterRadius at hceil ⊢
  have hwidthR : (1 : ℝ) ≤ shellWidth48 m := by exact_mod_cast hwidthPos
  nlinarith

/-- Every scale comparison required by the broad one-coordinate screen is
eventually true. -/
theorem eventually_candidateLocalBroadThetaScaleArithmetic :
    ∀ᶠ m : ℕ in atTop, CandidateLocalBroadThetaScaleArithmetic m := by
  have hbroadLinear := eventually_const_mul_nat_rpow_le
    (20 : ℝ) (7 / 10 : ℝ) 1 (by norm_num)
  have hbroadToFourFifths := eventually_const_mul_nat_rpow_le
    (8 : ℝ) (7 / 10 : ℝ) (4 / 5 : ℝ) (by norm_num)
  have hthreeQuarterToFourFifths := eventually_const_mul_nat_rpow_le
    (36 : ℝ) (3 / 4 : ℝ) (4 / 5 : ℝ) (by norm_num)
  filter_upwards
      [HLOZSharpWindowProductClosure.eventually_shellWidth48_cast_le_two_rpow,
        HLOZSharpWindowProductClosure.eventually_shellWidth48_moderate_nat,
        eventually_geometricDeviation_le_half,
        eventually_theta_low_arithmetic, hbroadLinear,
        hbroadToFourFifths, hthreeQuarterToFourFifths,
        eventually_ge_atTop (20 : ℕ)] with
      m hshell hshellModerate hgeometric htheta hbroadLinearM hbroadFourM
        hthreeQuarterFourM hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hbroadNonneg : 0 ≤ (m : ℝ) ^ (7 / 10 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hbroadOne : 1 ≤ (m : ℝ) ^ (7 / 10 : ℝ) :=
    Real.one_le_rpow hmR (by norm_num)
  have hbroadCeilLt : (candidateLocalBroadWidth48 m : ℝ) <
      (m : ℝ) ^ (7 / 10 : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one hbroadNonneg
  have hwidthPos : 1 ≤ candidateLocalBroadWidth48 m := by
    have hceil : (1 : ℝ) ≤ (candidateLocalBroadWidth48 m : ℝ) :=
      hbroadOne.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  have hwidth : (candidateLocalBroadWidth48 m : ℝ) ≤ (m : ℝ) / 10 := by
    simp only [Real.rpow_one] at hbroadLinearM
    have hmTwenty : (20 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hradius : shellZeroCenterRadius m ≤ (m : ℝ) := by
    unfold shellZeroCenterRadius
    have hshellHalf : (shellWidth48 m : ℝ) ≤ (m : ℝ) / 2 := by
      have hshellHalfNat : shellWidth48 m ≤ m / 2 := by omega
      calc
        (shellWidth48 m : ℝ) ≤ (m / 2 : ℕ) := by exact_mod_cast hshellHalfNat
        _ ≤ (m : ℝ) / 2 := Nat.cast_div_le
    nlinarith
  have hshellPos : 1 ≤ shellWidth48 m := by
    have hshellOne : 1 ≤ (m : ℝ) ^ kappaOne :=
      Real.one_le_rpow hmR (by norm_num [kappaOne])
    have hceil : (1 : ℝ) ≤ (shellWidth48 m : ℝ) :=
      hshellOne.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  have hmargin := shellZeroExternalLow48_geometric_margin
    hradius hshellPos
  have hgeometricNat : geometricDeviation m ≤
      (m + candidateLocalBroadWidth48 m : ℕ) := by
    have hcast : geometricDeviation m ≤
        ((m + candidateLocalBroadWidth48 m : ℕ) : ℝ) := by
      rw [Nat.cast_add]
      apply hgeometric.trans
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have hw0 : (0 : ℝ) ≤ candidateLocalBroadWidth48 m := by positivity
      exact (half_le_self hm0).trans
        (le_add_of_nonneg_right hw0)
    exact_mod_cast hcast
  have hthetaNat : thetaLowDeviation m ≤
      (m + candidateLocalBroadWidth48 m : ℕ) := by
    have hcast : thetaLowDeviation m ≤
        ((m + candidateLocalBroadWidth48 m : ℕ) : ℝ) := by
      rw [Nat.cast_add]
      apply htheta.2.2.trans
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have hw0 : (0 : ℝ) ≤ candidateLocalBroadWidth48 m := by positivity
      exact (half_le_self hm0).trans
        (le_add_of_nonneg_right hw0)
    exact_mod_cast hcast
  have hlowDom : (candidateLocalBroadWidth48 m : ℝ) +
      thetaLowDeviation m ≤
        (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ) := by
    simp only [thetaLowDeviation] at hthreeQuarterFourM ⊢
    nlinarith
  exact
    { level_pos := by omega
      width_pos := hwidthPos
      width := hwidth
      radius := hradius
      margin := hmargin
      geometric := hgeometricNat
      theta := hthetaNat
      thick_nonneg := htheta.1
      low_dom := hlowDom }

/-- Capacity plus a retained count below the candidate threshold forces the
whole broad source window into the same negative-binomial upper tail used by
the first-strip balance estimate. -/
theorem geometricDeviation_le_lazy_of_broad_capacity
    {m width externalThreshold i v : ℕ}
    (hcapacity : sourceCandidateLazyCap48 m + externalThreshold + width ≤
      m + 1)
    (hi : i < externalThreshold)
    (hv : v ∈ shellZeroSourceFailureWindow m width i)
    (hmargin : (16 / 15 : ℝ) * shellZeroExternalLow48 m +
      geometricDeviation m ≤ (m : ℝ) + 1) :
    (i : ℝ) / 15 + geometricDeviation m ≤ v := by
  have hlowLevel := shellZeroExternalLow48_le m
  have hiLow : i + width ≤ shellZeroExternalLow48 m := by
    unfold sourceCandidateLazyCap48 at hcapacity
    omega
  have hiSource : i ≤ m - width + 1 := by omega
  have hvLower : m - width + 1 - i ≤ v :=
    (mem_shellZeroSourceFailureWindow.mp hv).1
  have hvLowerR : ((m - width + 1 - i : ℕ) : ℝ) ≤ (v : ℝ) := by
    exact_mod_cast hvLower
  have hiSourceR : (i : ℝ) ≤ (m - width + 1 : ℕ) := by
    exact_mod_cast hiSource
  have hwidthLevel : width ≤ m := by omega
  rw [Nat.cast_sub hiSource] at hvLowerR
  rw [Nat.cast_add, Nat.cast_sub hwidthLevel, Nat.cast_one] at hvLowerR
  rw [Nat.cast_add, Nat.cast_sub hwidthLevel, Nat.cast_one] at hiSourceR
  have hiLowR : (i : ℝ) + width ≤ shellZeroExternalLow48 m := by
    exact_mod_cast hiLow
  nlinarith

/-- Broad high-external source-window mass.  The proof uses the capacity
inequality directly, rather than identifying the broad width with the much
smaller first-strip width. -/
theorem broadSourceFailureWindowMass_le_high_cost
    {m width externalThreshold i : ℕ}
    (hm : 0 < m) (hi : 0 < i)
    (hwidth : (width : ℝ) ≤ (m : ℝ) / 10)
    (hcapacity : sourceCandidateLazyCap48 m + externalThreshold + width ≤
      m + 1)
    (hiExternal : i < externalThreshold)
    (hmargin : (16 / 15 : ℝ) * shellZeroExternalLow48 m +
      geometricDeviation m ≤ (m : ℝ) + 1)
    (hdeviation : geometricDeviation m ≤ (m + width : ℕ)) :
    SmallWindow.windowMass i (shellZeroSourceFailureWindow m width i) ≤
      Real.exp (-17 * balanceRateScale m) := by
  by_cases hempty : shellZeroSourceFailureWindow m width i = ∅
  · rw [hempty, SmallWindow.windowMass]
    simp only [Finset.sum_empty]
    positivity
  obtain ⟨v0, hv0⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have him : i ≤ m + width := by
    have hv0Data := mem_shellZeroSourceFailureWindow.mp hv0
    omega
  let a := geometricDeviation m
  let threshold := Nat.ceil ((i : ℝ) / 15 + a)
  have hwindow : ∀ v ∈ shellZeroSourceFailureWindow m width i,
      threshold ≤ v := by
    intro v hv
    apply Nat.ceil_le.mpr
    exact geometricDeviation_le_lazy_of_broad_capacity
      hcapacity hiExternal hv hmargin
  have hmw : 0 < m + width := by omega
  have hraw := windowMass_le_exp_neg_upper_ambient hmw hi him
    (geometricDeviation_nonneg m) hdeviation (Nat.le_ceil _) _ hwindow
  refine hraw.trans ?_
  apply Real.exp_le_exp.mpr
  rw [show -geometricDeviation m ^ 2 / (4 * ((m + width : ℕ) : ℝ)) =
      -(geometricDeviation m ^ 2 / (4 * ((m + width : ℕ) : ℝ))) by ring,
    show -17 * balanceRateScale m = -(17 * balanceRateScale m) by ring]
  exact neg_le_neg
    (seventeen_balanceRateScale_le_geometric_rate_add_width hm hwidth)

/-- Literal one-coordinate broad source screen.  High retained counts use
the capacity-derived geometric deviation; low retained counts use the
stronger physical-slot deviation already checked for Proposition 4.5. -/
theorem sum_broadSourceThetaCoordinateBad_tilingAwayPointMass_le
    {retainedCount cap upper m width externalThreshold : ℕ}
    (t : DominoTiling) (x : Point)
    (r : TilingRetainedWord t x retainedCount) (D : Finset Point)
    (b : TilingAwayDomino t x r D)
    (hm : 0 < m)
    (hwidth : (width : ℝ) ≤ (m : ℝ) / 10)
    (hcapacity : sourceCandidateLazyCap48 m + externalThreshold + width ≤
      m + 1)
    (hmargin : (16 / 15 : ℝ) * shellZeroExternalLow48 m +
      geometricDeviation m ≤ (m : ℝ) + 1)
    (hgeometric : geometricDeviation m ≤ (m + width : ℕ))
    (htheta : thetaLowDeviation m ≤ (m + width : ℕ))
    (hthreshold0 : 0 ≤ hlozThickThresholdReal44 m)
    (hdom : (width : ℝ) + thetaLowDeviation m ≤
      (16 / 15 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ))
    (hwindowUpper : ∀ v ∈ shellZeroSourceFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t x r b.1)), v < upper)
    (hwindowCap : ∀ v ∈ shellZeroSourceFailureWindow m width
      (Fintype.card (TilingCoordinatesAt t x r b.1)), v ≤ cap) :
    (∑ v : Fin upper,
        if broadSourceThetaCoordinateBad m width externalThreshold
            (Fintype.card (TilingCoordinatesAt t x r b.1)) v then
          tilingAwayPointMass (cap := cap) t x r D b v else 0) ≤
      thetaCoordinateCost m
        (Fintype.card (TilingCoordinatesAt t x r b.1)) := by
  classical
  let i := Fintype.card (TilingCoordinatesAt t x r b.1)
  have hi : 0 < i := card_tilingCoordinatesAt_pos t x r b.1
  by_cases himbalance : i < externalThreshold
  · have heq : (∑ v : Fin upper,
        if broadSourceThetaCoordinateBad m width externalThreshold i v then
          tilingAwayPointMass (cap := cap) t x r D b v else 0) =
        SmallWindow.windowMass i
          (shellZeroSourceFailureWindow m width i) := by
      calc
        _ = ∑ v : Fin upper,
            if (v : ℕ) ∈ shellZeroSourceFailureWindow m width i then
              tilingAwayPointMass (cap := cap) t x r D b v else 0 := by
          apply Finset.sum_congr rfl
          intro v _hv
          simp only [broadSourceThetaCoordinateBad, himbalance,
            and_true]
        _ = _ := sum_tilingAwayPointMass_window t x r D b upper
          (shellZeroSourceFailureWindow m width i) hwindowUpper hwindowCap hi
    rw [heq]
    unfold thetaCoordinateCost
    by_cases hhigh : hlozThickLevel44 m ≤ i
    · rw [if_pos hhigh]
      exact broadSourceFailureWindowMass_le_high_cost hm hi hwidth
        hcapacity himbalance hmargin hgeometric
    · rw [if_neg hhigh]
      have hsub : shellZeroSourceFailureWindow m width i ⊆
          thetaFailureWindow m width i := by
        intro v hv
        rw [thetaFailureWindow, Finset.mem_union]
        exact Or.inl hv
      calc
        SmallWindow.windowMass i
            (shellZeroSourceFailureWindow m width i) ≤
          SmallWindow.windowMass i (thetaFailureWindow m width i) := by
            unfold SmallWindow.windowMass
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun _ _ _ ↦ NegativeBinomial.hlozMass_nonneg _ _)
        _ ≤ Real.exp (-17 * thetaLowRateScale m) :=
          thetaFailureWindowMass_le_low_cost hm hi hwidth
            (Nat.lt_of_not_ge hhigh) hthreshold0 hdom htheta
  · have hfalse : ∀ v : Fin upper,
        ¬broadSourceThetaCoordinateBad m width externalThreshold i v := by
      intro v hv
      exact himbalance hv.2
    simp only [i, hfalse, ↓reduceIte, Finset.sum_const_zero]
    unfold thetaCoordinateCost
    split <;> positivity

end

end Erdos1165.HLOZCandidateLocalBroadThetaProduct
