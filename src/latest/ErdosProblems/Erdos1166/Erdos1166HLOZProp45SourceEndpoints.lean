import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceMirrors
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceObjects
import ErdosProblems.Erdos1166.Erdos1166HLOZActualStopped
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedStopped
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma412Windows

/-!
The source-specific endpoint arithmetic for HLOZ Proposition 4.5.  This
module converts the real interval `[m-m^κ₁+1,m)` into natural endpoints and
discharges every analytic field of the lower- and upper-endpoint scale
structures at those endpoints.
-/

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal BigOperators

namespace Erdos1166.HLOZProp45SourceEndpoints

open HLOZFoundation HLOZDecomposition HLOZUrn
open HLOZProp45SourceClock HLOZProp45SourceInterval
open HLOZProp45SourceMirrors HLOZProp47Parameters HLOZProp47SourceObjects
open HLOZLemma412Windows
open HLOZActualStopped
open HLOZPrimedStopped

/-- The natural lower endpoint of the paper's interval
`[m - m^κ₁ + 1, m)`. -/
noncomputable def sourceBandLowerNat (m : ℕ) : ℕ :=
  Nat.ceil (thetaBandLower m)

lemma thetaBandLower_le_sourceBandLowerNat (m : ℕ) :
    thetaBandLower m ≤ (sourceBandLowerNat m : ℝ) := by
  exact Nat.le_ceil _

lemma sourceBandLowerNat_le_iff (m j : ℕ) :
    sourceBandLowerNat m ≤ j ↔ thetaBandLower m ≤ (j : ℝ) := by
  exact Nat.ceil_le

lemma thetaBandLower_nonneg (m : ℕ) (hm : 1 ≤ m) :
    0 ≤ thetaBandLower m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk : kappaOne ≤ 1 := by norm_num [kappaOne]
  have hp : (m : ℝ) ^ kappaOne ≤ (m : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR hk
  rw [Real.rpow_one] at hp
  rw [thetaBandLower]
  linarith

lemma sourceBandLowerNat_lt_add_one (m : ℕ) (hm : 1 ≤ m) :
    (sourceBandLowerNat m : ℝ) < thetaBandLower m + 1 := by
  exact Nat.ceil_lt_add_one (thetaBandLower_nonneg m hm)

lemma one_le_sourceBandLowerNat (m : ℕ) (hm : 1 ≤ m) :
    1 ≤ sourceBandLowerNat m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk : kappaOne ≤ 1 := by norm_num [kappaOne]
  have hp : (m : ℝ) ^ kappaOne ≤ (m : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hmR hk
  rw [Real.rpow_one] at hp
  have hlow : 0 < thetaBandLower m := by
    rw [thetaBandLower]
    linarith
  exact Nat.ceil_pos.mpr hlow

lemma sourceBandLowerNat_le_m (m : ℕ) (hm : 1 ≤ m) :
    sourceBandLowerNat m ≤ m := by
  rw [sourceBandLowerNat, Nat.ceil_le]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) ≤ kappaOne := by norm_num [kappaOne]
  have hp : (1 : ℝ) ≤ (m : ℝ) ^ kappaOne := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hmR hk0
  rw [thetaBandLower]
  linarith

/-- On integer local-time levels, the source's real half-open band is exactly
the natural interval with the ceiling lower endpoint. -/
lemma mem_sourceBand_iff (m j : ℕ) :
    sourceBandLowerNat m ≤ j ∧ j < m ↔
      thetaBandLower m ≤ (j : ℝ) ∧ (j : ℝ) < m := by
  rw [sourceBandLowerNat_le_iff]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨hlo, by exact_mod_cast hhi⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨hlo, by exact_mod_cast hhi⟩

@[simp] lemma sourceKappa_eq_kappaOne : sourceKappa = kappaOne := by
  norm_num [sourceKappa, kappaOne]

/-- The real lower-profile cutoff in the source definition implies the
integer cutoff used by the stopped negative-binomial estimate. -/
lemma le_intervalLowCut_of_le_sourceBandThreshold (m e : ℕ)
    (h : (e : ℝ) ≤ (15 / 16 : ℝ) * thetaBandLower m -
      10 * (m : ℝ) ^ (1 - kappaOne)) :
    e ≤ intervalLowCut m (sourceBandLowerNat m) := by
  rw [intervalLowCut]
  apply Nat.le_floor
  calc
    (e : ℝ) ≤ (15 / 16 : ℝ) * thetaBandLower m -
        10 * (m : ℝ) ^ (1 - kappaOne) := h
    _ ≤ intervalLowCutReal m (sourceBandLowerNat m) := by
      rw [intervalLowCutReal, sourceNearWidth, sourceKappa_eq_kappaOne]
      have := thetaBandLower_le_sourceBandLowerNat m
      nlinarith
    _ ≤ max (intervalLowCutReal m (sourceBandLowerNat m)) 0 :=
      le_max_left _ _

/-- The source's strict real upper-profile cutoff is exactly strong enough
for the successor-of-floor natural cutoff used by the upper branch. -/
lemma intervalHighCut_top_le_of_sourceBandThreshold (m e : ℕ)
    (h : (15 / 16 : ℝ) * m +
      10 * (m : ℝ) ^ (1 - kappaOne) < e) :
    intervalHighCut m m ≤ e := by
  have hreal : intervalHighCutReal m m < (e : ℝ) := by
    rw [intervalHighCutReal, sourceNearWidth, sourceKappa_eq_kappaOne]
    exact h
  have hreal0 : 0 ≤ intervalHighCutReal m m := by
    rw [intervalHighCutReal, sourceNearWidth]
    positivity
  have hfloor : Nat.floor (intervalHighCutReal m m) < e :=
    (Nat.floor_lt hreal0).mpr hreal
  rw [intervalHighCut]
  omega

/-- The source object's direct natural horizon agrees with the decomposition
horizon used by Proposition 4.5 in the paper range `m ≥ 2`. -/
lemma favoriteCreationHorizon_eq_directCreationTime (s : ℕ → Site)
    (m k : ℕ) (hm : 2 ≤ m) :
    favoriteCreationHorizon m (k + 1) s = directCreationTime m (k + 1) s := by
  rw [favoriteCreationHorizon, directCreationTime,
    favoriteCreationTime_eq_firstKSitesReachLevel s m k hm]

/-- A site in the real lower half of the source `Theta` band satisfies the
natural stopped lower event used by the unprimed Proposition 4.5 core.  The
parity predicate is intentionally arbitrary: parity only selects the branch,
while the endpoint conversion itself is deterministic. -/
lemma mem_intervalStoppedThetaMinusAt_of_mem_stoppedThetaHalfSites
    (parity : Site → Prop) (s : ℕ → Site) (m k : ℕ) (hm : 2 ≤ m) (x : Site)
    (hx : x ∈ stoppedThetaHalfSites paperExternalLocalTime parity false 10
      s m (k + 1)) :
    s ∈ intervalStoppedThetaMinusAt m (sourceBandLowerNat m) (k + 1) x := by
  simp only [stoppedThetaHalfSites, Finset.mem_filter, Bool.false_eq_true,
    ↓reduceIte] at hx
  rcases hx with ⟨_hxVisited, _hxFinite, _hxParity, hxLower, _hxUpper,
    hxExternal⟩
  rw [intervalStoppedThetaMinusAt, Set.mem_ofPred_eq,
    favoriteCreationHorizon_eq_directCreationTime s m k hm]
  refine ⟨le_intervalLowCut_of_le_sourceBandThreshold m _ ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, one_mul] using hxExternal
  · exact (sourceBandLowerNat_le_iff m _).mpr hxLower

/-- A site in the real upper half of the source `Theta` band satisfies the
natural stopped upper event at the source top endpoint `b=m`. -/
lemma mem_intervalStoppedThetaPlusAt_of_mem_stoppedThetaHalfSites
    (parity : Site → Prop) (s : ℕ → Site) (m k : ℕ) (hm : 2 ≤ m) (x : Site)
    (hx : x ∈ stoppedThetaHalfSites paperExternalLocalTime parity true 10
      s m (k + 1)) :
    s ∈ intervalStoppedThetaPlusAt m m (k + 1) x := by
  simp only [stoppedThetaHalfSites, Finset.mem_filter, ↓reduceIte] at hx
  rcases hx with ⟨_hxVisited, _hxFinite, _hxParity, _hxLower, hxUpper,
    hxExternal⟩
  rw [intervalStoppedThetaPlusAt, Set.mem_ofPred_eq,
    favoriteCreationHorizon_eq_directCreationTime s m k hm]
  refine ⟨intervalHighCut_top_le_of_sourceBandThreshold m _ ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, one_mul] using hxExternal
  · exact_mod_cast hxUpper

private lemma eventually_sourceBandLowerScale :
    ∀ᶠ m : ℕ in atTop,
      SourceIntervalScale m (sourceBandLowerNat m) := by
  have hfarNear :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := 10) (p := 1 - sourceKappa) (q := 3 / 4)
      (by norm_num) (by norm_num) (by norm_num [sourceKappa])
  have hhalf :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1) (d := 1 / 2) (p := kappaOne) (q := 1)
      (by norm_num) (by norm_num) (by norm_num [kappaOne])
  have hsplit1 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := ((15 / 16 : ℝ) - 15 / 31) / 4)
      (p := 3 / 4) (q := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hsplit2 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1) (d := ((15 / 16 : ℝ) - 15 / 31) / 4)
      (p := 0) (q := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hprop1 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := 1 / 3) (p := 3 / 4) (q := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
  have hprop2 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 15 / 16) (d := 1 / 3) (p := kappaOne) (q := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num [kappaOne])
  have hprop3 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1 / 16) (d := 1 / 3) (p := 0) (q := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hfarNear, hhalf, hsplit1, hsplit2, hprop1, hprop2,
    hprop3, eventually_sourceScale, eventually_ge_atTop 1] with
      m hfarNear hhalf hsplit1 hsplit2 hprop1 hprop2 hprop3 hs hm
  let a := sourceBandLowerNat m
  change SourceIntervalScale m a
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha1 : 1 ≤ a := one_le_sourceBandLowerNat m hm
  have ham : a ≤ m := sourceBandLowerNat_le_m m hm
  have haLower : (m : ℝ) - (m : ℝ) ^ kappaOne + 1 ≤ a := by
    simpa only [thetaBandLower] using thetaBandLower_le_sourceBandLowerNat m
  have haHalf : (m : ℝ) / 2 ≤ a := by
    simp only [Real.rpow_one] at hhalf
    linarith
  have hsplitTerm :
      10 * (m : ℝ) ^ (3 / 4 : ℝ) + 1 ≤
        ((15 / 16 : ℝ) - 15 / 31) * a := by
    simp only [Real.rpow_zero, Real.rpow_one, mul_one] at hsplit1 hsplit2
    calc
      10 * (m : ℝ) ^ (3 / 4 : ℝ) + 1 ≤
          ((15 / 16 : ℝ) - 15 / 31) / 4 * m +
            ((15 / 16 : ℝ) - 15 / 31) / 4 * m :=
        add_le_add hsplit1 hsplit2
      _ = ((15 / 16 : ℝ) - 15 / 31) * (m / 2) := by ring
      _ ≤ ((15 / 16 : ℝ) - 15 / 31) * a := by
        exact mul_le_mul_of_nonneg_left haHalf (by norm_num)
  have hpropTerm :
      10 * (m : ℝ) ^ (3 / 4 : ℝ) +
          (15 / 16 : ℝ) * (m : ℝ) ^ kappaOne + 1 / 16 ≤
        (m : ℝ) ^ (4 / 5 : ℝ) := by
    simp only [Real.rpow_zero, mul_one] at hprop3
    norm_num at hprop1 hprop2 hprop3 ⊢
    nlinarith
  have hsplitPos : 0 ≤ intervalSplitCutReal m a := by
    rw [intervalSplitCutReal, sourceFarWidth]
    have hfarCoeff : 10 * (m : ℝ) ^ (3 / 4 : ℝ) ≤
        ((15 / 16 : ℝ) - 15 / 31) * a := by
      exact (le_add_of_nonneg_right (by norm_num)).trans hsplitTerm
    have hcoeffCenter : ((15 / 16 : ℝ) - 15 / 31) * a ≤
        (15 / 16 : ℝ) * a := by
      gcongr
      norm_num
    exact sub_nonneg.mpr (hfarCoeff.trans hcoeffCenter)
  have hlowPos : 0 ≤ intervalLowCutReal m a := by
    rw [intervalLowCutReal, sourceNearWidth]
    rw [intervalSplitCutReal, sourceFarWidth] at hsplitPos
    exact sub_nonneg.mpr (hfarNear.trans (sub_nonneg.mp hsplitPos))
  have hsplitFloor : intervalSplitCutReal m a < intervalSplitCut m a + 1 := by
    rw [intervalSplitCut, max_eq_left hsplitPos]
    exact Nat.lt_floor_add_one _
  refine
    { one_le_m := hm
      one_le_a := ha1
      a_le_m := ham
      split_le_low := ?_
      split_lower := ?_
      prop44_le_split := ?_
      far_linear := hs.far_linear }
  · apply Nat.floor_mono
    rw [max_eq_left hsplitPos, max_eq_left hlowPos]
    rw [intervalSplitCutReal, intervalLowCutReal, sourceFarWidth, sourceNearWidth]
    nlinarith
  · rw [intervalSplitCutReal, sourceFarWidth] at hsplitFloor
    have htarget : (15 / 31 : ℝ) * a ≤
        (15 / 16 : ℝ) * a - 10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by
      calc
        (15 / 31 : ℝ) * a = (15 / 16 : ℝ) * a -
            ((15 / 16 : ℝ) - 15 / 31) * a := by ring
        _ ≤ (15 / 16 : ℝ) * a -
            (10 * (m : ℝ) ^ (3 / 4 : ℝ) + 1) :=
          sub_le_sub_left hsplitTerm _
        _ = (15 / 16 : ℝ) * a -
            10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by ring
    have hfloorLower :
        (15 / 16 : ℝ) * a - 10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 <
          (intervalSplitCut m a : ℝ) := by
      linarith
    exact le_of_lt (htarget.trans_lt hfloorLower)
  · rw [sourceProp44Threshold]
    rw [intervalSplitCutReal, sourceFarWidth] at hsplitFloor
    have htarget :
        (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ) ≤
          (15 / 16 : ℝ) * a - 10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by
      calc
        (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ) ≤
            (15 / 16 : ℝ) * m -
              (10 * (m : ℝ) ^ (3 / 4 : ℝ) +
                (15 / 16 : ℝ) * (m : ℝ) ^ kappaOne + 1 / 16) :=
          sub_le_sub_left hpropTerm _
        _ = (15 / 16 : ℝ) *
              ((m : ℝ) - (m : ℝ) ^ kappaOne + 1) -
                10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by ring
        _ ≤ (15 / 16 : ℝ) * a -
              10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by
          gcongr
    have hfloorLower :
        (15 / 16 : ℝ) * a - 10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 <
          (intervalSplitCut m a : ℝ) := by
      linarith
    exact le_of_lt (htarget.trans_lt hfloorLower)

/-- All lower-endpoint analytic hypotheses required by Proposition 4.5 hold
eventually at the source's actual endpoint. -/
theorem eventually_sourceIntervalScale_sourceBandLower :
    ∀ᶠ m : ℕ in atTop,
      SourceIntervalScale m (sourceBandLowerNat m) :=
  eventually_sourceBandLowerScale

/-- The lower and upper source endpoint packages hold simultaneously. -/
theorem eventually_sourceEndpointScales :
    ∀ᶠ m : ℕ in atTop,
      SourceIntervalScale m (sourceBandLowerNat m) ∧ SourceUpperScale m m := by
  filter_upwards [eventually_sourceIntervalScale_sourceBandLower,
    eventually_sourceUpperScale_top] with m hl hu
  exact ⟨hl, hu⟩

/-- The arbitrary lower and previous-upper endpoints occurring in the
Proposition-4.8 recursion satisfy the Proposition-4.5 scale hypotheses,
uniformly throughout the range `α ≤ 7/10` used by Lemma 4.10.

The proof uses the sharp deterministic displacement bound
`L * ceil(m^κ₁) ≤ 4 m^(7/10)`.  In particular, it does not fall back to the
much coarser `m/2` bound, which would be insufficient for the fixed
Proposition-4.4 cutoff. -/
theorem eventually_sourceRecursiveEndpointScales :
    ∀ᶠ m : ℕ in atTop, ∀ (α : ℝ) (l : ℕ),
      kappaOne ≤ α → α ≤ (7 : ℝ) / 10 →
      1 ≤ l → l ≤ sourceAlphaIntervalCount m α →
      SourceIntervalScale m (sourceIntervalLower m l) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m l) := by
  have hfarNear :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := 10) (p := 1 - sourceKappa) (q := 3 / 4)
      (by norm_num) (by norm_num) (by norm_num [sourceKappa])
  have hsplit1 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := ((15 / 16 : ℝ) - 15 / 31) / 4)
      (p := 3 / 4) (q := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hsplit2 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1) (d := ((15 / 16 : ℝ) - 15 / 31) / 4)
      (p := 0) (q := 1)
      (by norm_num) (by norm_num) (by norm_num)
  have hprop1 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := 1 / 3) (p := 3 / 4) (q := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
  have hprop2 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 15 / 4) (d := 1 / 3) (p := 7 / 10) (q := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
  have hprop3 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1) (d := 1 / 3) (p := 0) (q := 4 / 5)
      (by norm_num) (by norm_num) (by norm_num)
  have hnear1 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 10) (d := 1 / 64) (p := 1 - sourceKappa) (q := 1)
      (by norm_num) (by norm_num) (by norm_num [sourceKappa])
  have hnear2 :=
    eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := 1) (d := 1 / 64) (p := 0) (q := 1)
      (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hfarNear, hsplit1, hsplit2, hprop1, hprop2, hprop3,
      hnear1, hnear2, eventually_sourceScale, eventually_sourceIntervalIndex,
      eventually_ge_atTop 2] with
      m hfarNear hsplit1 hsplit2 hprop1 hprop2 hprop3 hnear1 hnear2 hs
        hindices hm α l hα0 hα1 hl1 hlCount
  have hm1 : 1 ≤ m := by omega
  have hαcut : α ≤ (4 : ℝ) / 5 := by linarith
  have hcountCut : sourceAlphaIntervalCount m α ≤ sourceIntervalCutoff m :=
    sourceAlphaIntervalCount_le_cutoff m hm1 hαcut
  have hindex : SourceIntervalIndex m l :=
    hindices l hl1 (hlCount.trans hcountCut)
  let a := sourceIntervalLower m l
  let b := sourceThetaIntervalUpper m l
  have hfit : l * sourceCellWidth m ≤ m := by
    calc
      l * sourceCellWidth m ≤ 2 * (l * sourceCellWidth m) := by omega
      _ = 2 * l * sourceCellWidth m := by ring
      _ ≤ m := hindex.2
  have ham : a ≤ m := by
    dsimp [a, sourceIntervalLower]
    omega
  have hhalfNat : m ≤ 2 * a := by
    have htwice : 2 * (l * sourceCellWidth m) ≤ m := by
      simpa only [mul_assoc] using hindex.2
    dsimp [a, sourceIntervalLower]
    omega
  have ha1 : 1 ≤ a := by omega
  have hab : a ≤ b := by
    dsimp only [a, b, sourceThetaIntervalUpper]
    split_ifs with hl
    · dsimp [sourceIntervalLower]
      omega
    · have hl2 : 2 ≤ l := by omega
      have hendpoints := sourceInterval_endpoint_relations m l hl1 hfit
      rw [hendpoints.2]
      omega
  have hb1 : 1 ≤ b := ha1.trans hab
  have hbm : b ≤ m := by
    dsimp only [b, sourceThetaIntervalUpper]
    split_ifs with hl
    · exact le_rfl
    · have hl2 : 2 ≤ l := by omega
      dsimp [sourcePreviousUpper]
      have hlPred : l - 1 = (l - 2) + 1 := by omega
      rw [hlPred, Nat.add_mul]
      simp only [one_mul]
      omega
  have haLower : (m : ℝ) - 4 * (m : ℝ) ^ ((7 : ℝ) / 10) ≤ a := by
    dsimp only [a]
    exact sourceIntervalLower_cast_ge_of_le_alphaCount
      m l hm1 hα0 hα1 hlCount hindex
  have haHalf : (m : ℝ) / 2 ≤ a := by
    have hhalfR : (m : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hhalfNat
    linarith
  have hbLower : (m : ℝ) - 4 * (m : ℝ) ^ ((7 : ℝ) / 10) ≤ b := by
    exact haLower.trans (by exact_mod_cast hab)
  have hsplitTerm :
      10 * (m : ℝ) ^ (3 / 4 : ℝ) + 1 ≤
        ((15 / 16 : ℝ) - 15 / 31) * a := by
    simp only [Real.rpow_zero, Real.rpow_one, one_mul, mul_one] at hsplit1 hsplit2
    calc
      10 * (m : ℝ) ^ (3 / 4 : ℝ) + 1 ≤
          ((15 / 16 : ℝ) - 15 / 31) / 4 * m +
            ((15 / 16 : ℝ) - 15 / 31) / 4 * m :=
        add_le_add hsplit1 hsplit2
      _ = ((15 / 16 : ℝ) - 15 / 31) * (m / 2) := by ring
      _ ≤ ((15 / 16 : ℝ) - 15 / 31) * a := by
        exact mul_le_mul_of_nonneg_left haHalf (by norm_num)
  have hpropTerm :
      10 * (m : ℝ) ^ (3 / 4 : ℝ) +
          (15 / 4 : ℝ) * (m : ℝ) ^ (7 / 10 : ℝ) + 1 ≤
        (m : ℝ) ^ (4 / 5 : ℝ) := by
    simp only [Real.rpow_zero, mul_one] at hprop3
    nlinarith
  have hsplitPos : 0 ≤ intervalSplitCutReal m a := by
    rw [intervalSplitCutReal, sourceFarWidth]
    have hfarCoeff : 10 * (m : ℝ) ^ (3 / 4 : ℝ) ≤
        ((15 / 16 : ℝ) - 15 / 31) * a :=
      (le_add_of_nonneg_right (by norm_num)).trans hsplitTerm
    have hcoeffCenter : ((15 / 16 : ℝ) - 15 / 31) * a ≤
        (15 / 16 : ℝ) * a := by
      gcongr
      norm_num
    exact sub_nonneg.mpr (hfarCoeff.trans hcoeffCenter)
  have hlowPos : 0 ≤ intervalLowCutReal m a := by
    rw [intervalLowCutReal, sourceNearWidth]
    rw [intervalSplitCutReal, sourceFarWidth] at hsplitPos
    exact sub_nonneg.mpr (hfarNear.trans (sub_nonneg.mp hsplitPos))
  have hsplitFloor : intervalSplitCutReal m a < intervalSplitCut m a + 1 := by
    rw [intervalSplitCut, max_eq_left hsplitPos]
    exact Nat.lt_floor_add_one _
  have hLowerScale : SourceIntervalScale m a := by
    refine
      { one_le_m := hm1
        one_le_a := ha1
        a_le_m := ham
        split_le_low := ?_
        split_lower := ?_
        prop44_le_split := ?_
        far_linear := hs.far_linear }
    · apply Nat.floor_mono
      rw [max_eq_left hsplitPos, max_eq_left hlowPos]
      rw [intervalSplitCutReal, intervalLowCutReal, sourceFarWidth,
        sourceNearWidth]
      nlinarith
    · rw [intervalSplitCutReal, sourceFarWidth] at hsplitFloor
      have htarget : (15 / 31 : ℝ) * a ≤
          (15 / 16 : ℝ) * a - 10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by
        calc
          (15 / 31 : ℝ) * a = (15 / 16 : ℝ) * a -
              ((15 / 16 : ℝ) - 15 / 31) * a := by ring
          _ ≤ (15 / 16 : ℝ) * a -
              (10 * (m : ℝ) ^ (3 / 4 : ℝ) + 1) :=
            sub_le_sub_left hsplitTerm _
          _ = (15 / 16 : ℝ) * a -
              10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by ring
      have hfloorLower :
          (15 / 16 : ℝ) * a - 10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 <
            (intervalSplitCut m a : ℝ) := by
        linarith
      exact le_of_lt (htarget.trans_lt hfloorLower)
    · rw [sourceProp44Threshold]
      rw [intervalSplitCutReal, sourceFarWidth] at hsplitFloor
      have htarget :
          (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ) ≤
            (15 / 16 : ℝ) * a -
              10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by
        calc
          (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ) ≤
              (15 / 16 : ℝ) * m -
                (10 * (m : ℝ) ^ (3 / 4 : ℝ) +
                  (15 / 4 : ℝ) * (m : ℝ) ^ (7 / 10 : ℝ) + 1) :=
            sub_le_sub_left hpropTerm _
          _ = (15 / 16 : ℝ) *
                ((m : ℝ) - 4 * (m : ℝ) ^ (7 / 10 : ℝ)) -
                10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by ring
          _ ≤ (15 / 16 : ℝ) * a -
                10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 := by
            gcongr
      have hfloorLower :
          (15 / 16 : ℝ) * a - 10 * (m : ℝ) ^ (3 / 4 : ℝ) - 1 <
            (intervalSplitCut m a : ℝ) := by
        linarith
      exact le_of_lt (htarget.trans_lt hfloorLower)
  have hnearB : sourceNearWidth m + 1 ≤ (1 / 16 : ℝ) * b := by
    rw [sourceNearWidth]
    simp only [Real.rpow_zero, Real.rpow_one, one_mul, mul_one] at hnear1 hnear2
    have hnearM : 10 * (m : ℝ) ^ (1 - sourceKappa) + 1 ≤
        (1 / 32 : ℝ) * m := by
      calc
        10 * (m : ℝ) ^ (1 - sourceKappa) + 1 ≤
            (1 / 64 : ℝ) * m + (1 / 64 : ℝ) * m :=
          add_le_add hnear1 hnear2
        _ = (1 / 32 : ℝ) * m := by ring
    have hbHalf : (m : ℝ) / 2 ≤ b := haHalf.trans (by exact_mod_cast hab)
    calc
      10 * (m : ℝ) ^ (1 - sourceKappa) + 1 ≤
          (1 / 32 : ℝ) * m := hnearM
      _ ≤ (1 / 16 : ℝ) * b := by nlinarith
  have hhigh0 : 0 ≤ intervalHighCutReal m b := by
    rw [intervalHighCutReal]
    have : 0 ≤ sourceNearWidth m := by
      rw [sourceNearWidth]
      positivity
    positivity
  have hhighFloor : (Nat.floor (intervalHighCutReal m b) : ℝ) ≤
      intervalHighCutReal m b := Nat.floor_le hhigh0
  have hhighLe : intervalHighCut m b ≤ b := by
    have hR : (intervalHighCut m b : ℝ) ≤ b := by
      rw [intervalHighCut]
      push_cast
      rw [intervalHighCutReal] at hhighFloor ⊢
      nlinarith
    exact_mod_cast hR
  have hpropHigh : sourceProp44Threshold m ≤ intervalHighCut m b := by
    have hreal : sourceProp44Threshold m ≤ intervalHighCutReal m b := by
      rw [sourceProp44Threshold, intervalHighCutReal]
      have hgap : (15 / 4 : ℝ) * (m : ℝ) ^ (7 / 10 : ℝ) ≤
          (m : ℝ) ^ (4 / 5 : ℝ) := by
        have hp : 0 ≤ (m : ℝ) ^ (4 / 5 : ℝ) := by positivity
        calc
          (15 / 4 : ℝ) * (m : ℝ) ^ (7 / 10 : ℝ) ≤
              (1 / 3 : ℝ) * (m : ℝ) ^ (4 / 5 : ℝ) := hprop2
          _ ≤ 1 * (m : ℝ) ^ (4 / 5 : ℝ) :=
            mul_le_mul_of_nonneg_right (by norm_num) hp
          _ = (m : ℝ) ^ (4 / 5 : ℝ) := one_mul _
      have hgapB : (15 / 16 : ℝ) * m - (15 / 16 : ℝ) * b ≤
          (15 / 4 : ℝ) * (m : ℝ) ^ (7 / 10 : ℝ) := by
        nlinarith [hbLower]
      have hthreshold : (15 / 16 : ℝ) * m - (15 / 16 : ℝ) * b ≤
          (m : ℝ) ^ (4 / 5 : ℝ) := hgapB.trans hgap
      have hnear0 : 0 ≤ sourceNearWidth m := by
        rw [sourceNearWidth]
        positivity
      calc
        (15 / 16 : ℝ) * m - (m : ℝ) ^ (4 / 5 : ℝ) ≤
            (15 / 16 : ℝ) * b := by
          apply (sub_le_iff_le_add).2
          have hsum := (sub_le_iff_le_add).1 hthreshold
          simpa only [add_comm] using hsum
        _ ≤ (15 / 16 : ℝ) * b + sourceNearWidth m :=
          le_add_of_nonneg_right hnear0
    exact hreal.trans (le_of_lt (intervalHighCutReal_lt_cut m b))
  exact ⟨hLowerScale,
    { one_le_m := hm1
      one_le_b := hb1
      b_le_m := hbm
      highCut_le_b := hhighLe
      prop44_le_high := hpropHigh }⟩

/-- The four-branch error term in the finite conditional core of source
Proposition 4.5. -/
noncomputable def sourceProp45FourBranchError (m : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp (-sourceRate m)) +
      ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
    ENNReal.ofReal (Real.exp (-sourceRate m)) +
    (ENNReal.ofReal (Real.exp (-sourceRate m)) +
      ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
    ENNReal.ofReal (Real.exp (-sourceRate m))

/-- Source-endpoint specialization of the abstract four-way stopped estimate.
The single scale package is supplied eventually by
`eventually_sourceEndpointScales`; both event endpoints are fixed here to
the actual paper interval, so callers cannot accidentally instantiate the
probability core at a different band. -/
theorem cond_inter_fullProp45StoppedEvent_sourceBand_le
    (q m k : ℕ)
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (clock : PrimedShiftedDeletionClock m k)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (unprimedProfile primedProfile : Site → ℕ)
    (hUnprimedMinusSubset :
      C ∩ H ∩ intervalStoppedThetaMinusEvent
          sites m (sourceBandLowerNat m) k ⊆
        intervalCanonicalDotThetaEvent q sites m
          (sourceBandLowerNat m) unprimedProfile)
    (hUnprimedPlusSubset :
      C ∩ H ∩ intervalStoppedThetaPlusEvent sites m m k ⊆
        intervalCanonicalDotThetaPlusEvent q sites m m unprimedProfile)
    (hPrimedMinusSubset :
      C ∩ H ∩ primedIntervalStoppedThetaMinusEvent
          clock sites (sourceBandLowerNat m) ⊆
        primedIntervalCanonicalDotThetaMinusEvent
          clock sites (sourceBandLowerNat m) primedProfile)
    (hPrimedPlusSubset :
      C ∩ H ∩ primedIntervalStoppedThetaPlusEvent clock sites m ⊆
        primedIntervalCanonicalDotThetaPlusEvent
          clock sites m primedProfile)
    (hUnprimedProp44 :
      ((sourceProp44Candidates sites m unprimedProfile).card : ℝ) ≤
        Real.exp (16 * sourceRate m))
    (hPrimedProp44 :
      ((sourceProp44Candidates sites m primedProfile).card : ℝ) ≤
        Real.exp (16 * sourceRate m))
    (hHorizonCard :
      (sites.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ)))
    (hUnprimedMinusLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q
        (intervalDotIndex m (sourceBandLowerNat m) unprimedProfile x) x)
        (negBinMeasure
          (intervalDotIndex m (sourceBandLowerNat m) unprimedProfile x)) μ[|C])
    (hUnprimedPlusLaw : ∀ x ∈ intervalPlusCandidates sites m m unprimedProfile,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q (intervalHighCut m m) x)
        (negBinMeasure (intervalHighCut m m)) μ[|C])
    (hPrimedMinusLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ clock.inverseHoldingPrefix s
        (intervalDotIndex m (sourceBandLowerNat m) primedProfile x) x)
        (negBinMeasure
          (intervalDotIndex m (sourceBandLowerNat m) primedProfile x)) μ[|C])
    (hPrimedPlusLaw : ∀ x ∈ intervalPlusCandidates sites m m primedProfile,
      HasLaw (fun s ↦ clock.inverseHoldingPrefix s (intervalHighCut m m) x)
        (negBinMeasure (intervalHighCut m m)) μ[|C]) :
    μ[|C] (C ∩ H ∩ fullProp45StoppedEvent clock sites
      (sourceBandLowerNat m) m) ≤ sourceProp45FourBranchError m := by
  exact cond_inter_fullProp45StoppedEvent_le
    q m (sourceBandLowerNat m) m k hs.1 hs.2 clock μ C H sites
      unprimedProfile primedProfile hUnprimedMinusSubset
      hUnprimedPlusSubset hPrimedMinusSubset hPrimedPlusSubset
      hUnprimedProp44 hPrimedProp44 hHorizonCard hUnprimedMinusLaw
      hUnprimedPlusLaw hPrimedMinusLaw hPrimedPlusLaw

/-- Concrete-primed specialization at the actual source interval.  Compared
with `cond_inter_fullProp45ConcretePrimedStoppedEvent_le`, this wrapper has no
free endpoint parameters and no endpoint arithmetic premises beyond the
single eventual scale package. -/
theorem cond_inter_fullProp45ConcretePrimedStoppedEvent_sourceBand_le
    (q qPrime m k : ℕ)
    (hs : SourceIntervalScale m (sourceBandLowerNat m) ∧
      SourceUpperScale m m)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (unprimedProfile primedProfile : Site → ℕ)
    (hUnprimedProfile : C ⊆
      inverseClockProfileAtom q sites unprimedProfile)
    (hUnprimedMinusCompatible :
      C ∩ H ∩ intervalStoppedThetaMinusEvent
          sites m (sourceBandLowerNat m) k ⊆
        intervalClockPrefixCompatibleEvent q sites m
          (sourceBandLowerNat m) k unprimedProfile)
    (hUnprimedPlusCompatible :
      C ∩ H ∩ intervalStoppedThetaPlusEvent sites m m k ⊆
        intervalClockInitialPrefixCompatibleEvent q sites m m k)
    (hPrimedProfile : C ⊆ primedInverseProfileAtom
      (concretePrimedShiftedDeletionClock m k qPrime) sites primedProfile)
    (hPrimedMinusCompatible :
      C ∩ H ∩ primedIntervalStoppedThetaMinusEvent
          (concretePrimedShiftedDeletionClock m k qPrime) sites
            (sourceBandLowerNat m) ⊆
        primedMinusPrefixCompatibleEvent
          (concretePrimedShiftedDeletionClock m k qPrime)
          sites (sourceBandLowerNat m) primedProfile)
    (hPrimedPlusCompatible :
      C ∩ H ∩ primedIntervalStoppedThetaPlusEvent
          (concretePrimedShiftedDeletionClock m k qPrime) sites m ⊆
        primedPlusInitialPrefixCompatibleEvent
          (concretePrimedShiftedDeletionClock m k qPrime) sites m)
    (hUnprimedProp44 :
      ((sourceProp44Candidates sites m unprimedProfile).card : ℝ) ≤
        Real.exp (16 * sourceRate m))
    (hPrimedProp44 :
      ((sourceProp44Candidates sites m primedProfile).card : ℝ) ≤
        Real.exp (16 * sourceRate m))
    (hHorizonCard :
      (sites.card : ℝ) ≤ Real.exp (16 * Real.sqrt (m : ℝ)))
    (hUnprimedMinusLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q
        (intervalDotIndex m (sourceBandLowerNat m) unprimedProfile x) x)
        (negBinMeasure
          (intervalDotIndex m (sourceBandLowerNat m) unprimedProfile x)) μ[|C])
    (hUnprimedPlusLaw : ∀ x ∈ intervalPlusCandidates sites m m unprimedProfile,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q (intervalHighCut m m) x)
        (negBinMeasure (intervalHighCut m m)) μ[|C])
    (hPrimedMinusLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ primedInverseClockHoldingPrefix s qPrime
        (intervalDotIndex m (sourceBandLowerNat m) primedProfile x) x)
        (negBinMeasure
          (intervalDotIndex m (sourceBandLowerNat m) primedProfile x)) μ[|C])
    (hPrimedPlusLaw : ∀ x ∈ intervalPlusCandidates sites m m primedProfile,
      HasLaw (fun s ↦ primedInverseClockHoldingPrefix s qPrime
        (intervalHighCut m m) x)
        (negBinMeasure (intervalHighCut m m)) μ[|C]) :
    μ[|C] (C ∩ H ∩ fullProp45StoppedEvent
      (concretePrimedShiftedDeletionClock m k qPrime) sites
        (sourceBandLowerNat m) m) ≤ sourceProp45FourBranchError m := by
  exact cond_inter_fullProp45ConcretePrimedStoppedEvent_le
    q qPrime m (sourceBandLowerNat m) m k hs.1 hs.2 μ C H sites
      unprimedProfile primedProfile hUnprimedProfile
      hUnprimedMinusCompatible hUnprimedPlusCompatible hPrimedProfile
      hPrimedMinusCompatible hPrimedPlusCompatible hUnprimedProp44
      hPrimedProp44 hHorizonCard hUnprimedMinusLaw hUnprimedPlusLaw
      hPrimedMinusLaw hPrimedPlusLaw

end Erdos1166.HLOZProp45SourceEndpoints
