/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166HLOZProp13FromAppendix
import ErdosProblems.Erdos1166.Erdos1166HLOZProp44ExternalChain
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedStopped
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceAssembly
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma411
import ErdosProblems.Erdos1166.Erdos1166HLOZPairingProfiles

/-!
# Canonical source objects for HLOZ Proposition 4.7

This file fixes the pairing-adapted deletion profiles which occur in the
stopped `Theta` screen.  The four chessboard tilings and the two translated
column tilings retain their source endpoint selectors, so the family does
not silently identify the six deletion laws.

The file also fixes the source width `c_* = 10`, matching the checked
Proposition-4.5 cutoff.  In particular `c_*^2` is larger than the `12/5`
required in the endpoint estimates.
-/

namespace Erdos1166.HLOZProp47Canonical

open Filter MeasureTheory Set
open HLOZFoundation HLOZDecomposition HLOZProp47Parameters
open HLOZProp47SourceObjects
open HLOZNearCriticalBridge HLOZProp13FromAppendix
open HLOZProp47SourceAssembly HLOZPairing.ScreeningBridge
open HLOZScreeningAssembly HLOZLemma411
open HLOZPrimedStopped
open HLOZActualStopped HLOZProp45SourceClock HLOZProp45SourceInterval
open HLOZProp45SourceMirrors
open HLOZPairingProfiles
open scoped ENNReal

/-- Delete original time zero and translate the new starting point to zero. -/
def oneStepShiftedPath (s : ℕ → Site) (j : ℕ) : Site :=
  s (j + 1) - s 1

/-- The source's primed external profile, using the odd-endpoint deletion
realized in `HLOZPrimedStopped`. -/
noncomputable def paperPrimedProfile
    (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  primedExternalLocalTime s n x

private theorem oneStepShiftedPath_prefix
    {s t : ℕ → Site} {n : ℕ}
    (hst : ∀ j, j ≤ n + 2 → s j = t j) :
    ∀ j, j ≤ n + 1 → oneStepShiftedPath s j = oneStepShiftedPath t j := by
  intro j hj
  simp only [oneStepShiftedPath]
  rw [hst (j + 1) (by omega), hst 1 (by omega)]

theorem measurable_paperPrimedProfile (n : ℕ) (x : Site) :
    Measurable fun s ↦ paperPrimedProfile s n x := by
  have hfiltration : Measurable[canonicalFiltration (n + 1)]
      (fun s ↦ paperPrimedProfile s n x) := by
    apply measurable_of_prefix
    unfold PrefixDependent
    intro s t hst
    have hlazy (j : ℕ) (hj : j ≤ n + 1) :
        IsPrimedLazyEnd s j ↔ IsPrimedLazyEnd t j := by
      unfold IsPrimedLazyEnd
      constructor
      · rintro ⟨hj3, hjodd, hstep, hreturn⟩
        refine ⟨hj3, hjodd, ?_, ?_⟩
        · simpa only [hst (j - 2) (by omega), hst (j - 1) (by omega)] using hstep
        · simpa only [hst j hj, hst (j - 2) (by omega)] using hreturn
      · rintro ⟨hj3, hjodd, hstep, hreturn⟩
        refine ⟨hj3, hjodd, ?_, ?_⟩
        · simpa only [hst (j - 2) (by omega), hst (j - 1) (by omega)] using hstep
        · simpa only [hst j hj, hst (j - 2) (by omega)] using hreturn
    have hends : primedLazyEndsThrough s n = primedLazyEndsThrough t n := by
      ext j
      simp only [primedLazyEndsThrough, Finset.mem_filter, and_congr_right_iff]
      intro hj
      exact hlazy j (by
        have := (Finset.mem_Icc.mp hj).2
        omega)
    have hremoved : primedRemovedTimes s n = primedRemovedTimes t n := by
      unfold primedRemovedTimes primedCompletedRemovedTimes
        primedPartialRemovedTimes
      rw [hends]
      have hpartial := hlazy (n + 1) le_rfl
      by_cases hs : IsPrimedLazyEnd s (n + 1)
      · have ht := hpartial.mp hs
        simp [hs, ht]
      · have ht : ¬ IsPrimedLazyEnd t (n + 1) := fun ht ↦ hs (hpartial.mpr ht)
        simp [hs, ht]
    simp only [paperPrimedProfile, primedExternalLocalTime,
      primedRetainedTimes]
    rw [hremoved]
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hj
    rw [hst j (by
      simp only [Finset.mem_sdiff, Finset.mem_range] at hj
      omega)]
  exact hfiltration.mono (canonicalFiltration.le (n + 1)) le_rfl

/-- The original `X₁` unprimed/primed pair.  The six-pairing family below
uses the pairing-adapted generalization from `HLOZPairingProfiles`. -/
noncomputable def canonicalExternalProfilePair : ExternalProfilePair where
  unprimed := paperUnprimedProfile
  primed := paperPrimedProfile
  unprimedSites := HLOZPairing.chessEven
  primedSites := fun x ↦ ¬ HLOZPairing.chessEven x
  measurable_unprimed := measurable_paperUnprimedProfile
  measurable_primed := measurable_paperPrimedProfile

/-- Pairing-adapted auxiliary profile data.  The first four entries are the
literal rotated temporal deletions.  The last two entries are the
endpoint-adapted column parsers retained for the auxiliary column-law
development; they are not the deletion profiles of HLOZ (2.12). -/
noncomputable def canonicalProfiles : Fin 6 → ExternalProfilePair :=
  pairingProfiles

/-- Literal HLOZ profile family.  Equations (2.12), (4.29), and (4.30) keep
the temporal deletion fixed when the domino tiling changes from `X_j` to
`Y` or `Y'`.  Thus the four checkerboard entries rotate the temporal
deletion, while both column entries use the original `X₁` temporal pair.
The tiling dependence remains solely in `prefixPairingEvent`. -/
noncomputable def sourceCanonicalProfiles : Fin 6 → ExternalProfilePair :=
  fun i ↦ match i.1 with
    | 0 => deletionProfilePair (xDeletion HLOZPairing.east)
    | 1 => deletionProfilePair (xDeletion HLOZPairing.north)
    | 2 => deletionProfilePair (xDeletion HLOZPairing.west)
    | 3 => deletionProfilePair (xDeletion HLOZPairing.south)
    | _ => canonicalExternalProfilePair

@[simp] theorem sourceCanonicalProfiles_x (d : HLOZPairing.Dir) :
    sourceCanonicalProfiles ⟨d.1, by omega⟩ =
      canonicalProfiles ⟨d.1, by omega⟩ := by
  fin_cases d <;> rfl

@[simp] theorem sourceCanonicalProfiles_y :
    sourceCanonicalProfiles ⟨4, by omega⟩ =
      canonicalExternalProfilePair := rfl

@[simp] theorem sourceCanonicalProfiles_y' :
    sourceCanonicalProfiles ⟨5, by omega⟩ =
      canonicalExternalProfilePair := rfl

/-- The first pairing-adapted profile is exactly the paper's `X₁`
unprimed/primed decomposition, including its endpoint selectors. -/
theorem canonicalProfiles_xEast :
    canonicalProfiles ⟨0, by omega⟩ = canonicalExternalProfilePair := by
  change deletionProfilePair (xDeletion HLOZPairing.east) =
    canonicalExternalProfilePair
  unfold deletionProfilePair canonicalExternalProfilePair
  have hunprimed : deletionExternalLocalTime
      (xDeletion HLOZPairing.east) true =
      paperExternalLocalTime := by
    funext s n x
    exact deletionExternalLocalTime_xEast_forward s n x
  have hprimed : deletionExternalLocalTime
      (xDeletion HLOZPairing.east) false =
      primedExternalLocalTime := by
    funext s n x
    exact deletionExternalLocalTime_xEast_primed s n x
  apply ExternalProfilePair.ext _ _ hunprimed hprimed <;> rfl

/-- The concrete source width used by the checked Proposition-4.5 mirrors.
It amply satisfies the only required constraint `c_*^2 ≥ 12/5`. -/
noncomputable def canonicalCStar : Fin 6 → ℝ := fun _ ↦ 10

theorem canonicalCStar_sq_ge_twelve_fifths (i : Fin 6) :
    (12 : ℝ) / 5 ≤ (canonicalCStar i) ^ 2 := by
  norm_num [canonicalCStar]

/-! ### Exact stopped-event bridge for Proposition 4.5 -/

/-- The least integer local-time level in the source interval `I_m`. -/
noncomputable def canonicalThetaLower (m : ℕ) : ℕ :=
  Nat.ceil (thetaBandLower m)

theorem favoriteCreationHorizon_eq_directCreationTime
    (s : ℕ → Site) {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) :
    favoriteCreationHorizon m k s = directCreationTime m k s := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold favoriteCreationHorizon directCreationTime
  rw [favoriteCreationTime_eq_firstKSitesReachLevel s m j hm]

private theorem stoppedLower_le_intervalLowCut
    {m q : ℕ} (hs : SourceIntervalScale m (canonicalThetaLower m))
    (hq : (q : ℝ) ≤ (15 : ℝ) / 16 * thetaBandLower m -
      10 * (m : ℝ) ^ (1 - kappaOne)) :
    q ≤ intervalLowCut m (canonicalThetaLower m) := by
  have hceil : thetaBandLower m ≤ (canonicalThetaLower m : ℝ) := by
    exact Nat.le_ceil _
  have hreal : (q : ℝ) ≤
      intervalLowCutReal m (canonicalThetaLower m) := by
    calc
      (q : ℝ) ≤ (15 : ℝ) / 16 * thetaBandLower m -
          10 * (m : ℝ) ^ (1 - kappaOne) := hq
      _ ≤ (15 : ℝ) / 16 * (canonicalThetaLower m : ℝ) -
          10 * (m : ℝ) ^ (1 - kappaOne) := by gcongr
      _ = intervalLowCutReal m (canonicalThetaLower m) := by
        rw [intervalLowCutReal, sourceNearWidth]
        norm_num [sourceKappa, kappaOne]
  rw [intervalLowCut, max_eq_left (intervalLowCutReal_nonneg m _ hs)]
  exact Nat.le_floor hreal

private theorem intervalHighCut_le_stoppedUpper
    {m q : ℕ} (hs : SourceUpperScale m m)
    (hq : (15 : ℝ) / 16 * m +
      10 * (m : ℝ) ^ (1 - kappaOne) < q) :
    intervalHighCut m m ≤ q := by
  have hreal : intervalHighCutReal m m < (q : ℝ) := by
    simpa only [intervalHighCutReal, sourceNearWidth, sourceKappa, kappaOne]
      using hq
  have hq0 : q ≠ 0 := by
    have hpositive : 0 < (15 : ℝ) / 16 * m +
        10 * (m : ℝ) ^ (1 - kappaOne) := by
      have hm : 0 < (m : ℝ) := by exact_mod_cast hs.one_le_m
      positivity
    intro hzero
    subst q
    norm_num at hq
    linarith
  have hfloor : Nat.floor (intervalHighCutReal m m) < q :=
    (Nat.floor_lt' hq0).2 hreal
  rw [intervalHighCut]
  omega

/-- On a fixed stopped-profile atom, every canonical `Theta` violation is
one of the four concrete stopped events estimated by the checked
Proposition-4.5 mirror theorem.  The only set-theoretic input is that the
atom's fixed finite site set contains every site visited by the stopping
horizon. -/
theorem stoppedThetaEvent_subset_fullProp45ConcretePrimedStoppedEvent
    (m k qPrime : ℕ) (sites : Finset Site)
    (hm : 2 ≤ m) (hk : 1 ≤ k)
    (hsLower : SourceIntervalScale m (canonicalThetaLower m))
    (hsUpper : SourceUpperScale m m)
    {s : ℕ → Site}
    (hsites : visitedSites s (directCreationTime m k s) ⊆ sites)
    (htheta : s ∈ stoppedThetaEvent canonicalExternalProfilePair 10 m k) :
    s ∈ fullProp45StoppedEvent
      (concretePrimedShiftedDeletionClock m k qPrime) sites
      (canonicalThetaLower m) m := by
  rcases htheta with ⟨x, hx⟩
  change x ∈
    stoppedThetaHalfSites paperUnprimedProfile HLOZPairing.chessEven false 10 s m k ∪
      stoppedThetaHalfSites paperUnprimedProfile HLOZPairing.chessEven true 10 s m k ∪
      stoppedThetaHalfSites paperPrimedProfile
        (fun y ↦ ¬ HLOZPairing.chessEven y) false 10 s m k ∪
      stoppedThetaHalfSites paperPrimedProfile
        (fun y ↦ ¬ HLOZPairing.chessEven y) true 10 s m k at hx
  have htime := favoriteCreationHorizon_eq_directCreationTime s hm hk
  obtain hx123 | hx := Finset.mem_union.mp hx
  · obtain hx12 | hx := Finset.mem_union.mp hx123
    · obtain hx | hx := Finset.mem_union.mp hx12
      · left; left; left
        simp only [stoppedThetaHalfSites, Finset.mem_filter, Bool.false_eq_true,
          if_false] at hx
        rcases hx with ⟨hxv, _hfinite, _hparity, hxlow, _hxhigh, hxcut⟩
        apply Set.mem_iUnion_of_mem x
        apply Set.mem_iUnion_of_mem (hsites hxv)
        change paperExternalLocalTime s (favoriteCreationHorizon m k s) x ≤
            intervalLowCut m (canonicalThetaLower m) ∧
          canonicalThetaLower m ≤
            localTime s (favoriteCreationHorizon m k s) x
        rw [htime]
        exact ⟨stoppedLower_le_intervalLowCut hsLower hxcut,
          (Nat.ceil_le).2 hxlow⟩
      · left; left; right
        simp only [stoppedThetaHalfSites, Finset.mem_filter, if_true] at hx
        rcases hx with ⟨hxv, _hfinite, _hparity, _hxlow, hxhigh, hxcut⟩
        apply Set.mem_iUnion_of_mem x
        apply Set.mem_iUnion_of_mem (hsites hxv)
        change intervalHighCut m m ≤
            paperExternalLocalTime s (favoriteCreationHorizon m k s) x ∧
          localTime s (favoriteCreationHorizon m k s) x < m
        rw [htime]
        exact ⟨intervalHighCut_le_stoppedUpper hsUpper hxcut, by exact_mod_cast hxhigh⟩
    · left; right
      simp only [stoppedThetaHalfSites, Finset.mem_filter, Bool.false_eq_true,
        if_false] at hx
      rcases hx with ⟨hxv, _hfinite, _hparity, hxlow, _hxhigh, hxcut⟩
      change (primedExternalLocalTime s (directCreationTime m k s) x : ℝ) ≤
        (15 : ℝ) / 16 * thetaBandLower m -
          10 * (m : ℝ) ^ (1 - kappaOne) at hxcut
      apply Set.mem_iUnion_of_mem x
      apply Set.mem_iUnion_of_mem (hsites hxv)
      change primedExternalLocalTime s (favoriteCreationHorizon m k s) x ≤
          intervalLowCut m (canonicalThetaLower m) ∧
        canonicalThetaLower m ≤ localTime s (favoriteCreationHorizon m k s) x
      rw [htime]
      exact ⟨stoppedLower_le_intervalLowCut hsLower hxcut,
        (Nat.ceil_le).2 hxlow⟩
  · right
    simp only [stoppedThetaHalfSites, Finset.mem_filter, if_true] at hx
    rcases hx with ⟨hxv, _hfinite, _hparity, _hxlow, hxhigh, hxcut⟩
    change (15 : ℝ) / 16 * m + 10 * (m : ℝ) ^ (1 - kappaOne) <
      (primedExternalLocalTime s (directCreationTime m k s) x : ℝ) at hxcut
    apply Set.mem_iUnion_of_mem x
    apply Set.mem_iUnion_of_mem (hsites hxv)
    change intervalHighCut m m ≤
        primedExternalLocalTime s (favoriteCreationHorizon m k s) x ∧
      localTime s (favoriteCreationHorizon m k s) x < m
    rw [htime]
    exact ⟨intervalHighCut_le_stoppedUpper hsUpper hxcut, by exact_mod_cast hxhigh⟩

/-! ### The Proposition-1.3 cutoff absorbs the far-gap alternative -/

/-- Two sites reached by time `N` by a nearest-neighbor walk have Euclidean
distance at most `3N`.  The deliberately coarse constant avoids any square
root of two in the subsequent horizon comparison. -/
theorem siteDistance_le_three_mul_of_mem_squareDisk
    {x y : Site} {N : ℕ}
    (hx : x ∈ KilledGreen.squareDisk N)
    (hy : y ∈ KilledGreen.squareDisk N) :
    siteDistance x y ≤ 3 * (N : ℝ) := by
  have hx' := Finset.mem_product.mp hx
  have hy' := Finset.mem_product.mp hy
  have hx1 := Finset.mem_Icc.mp hx'.1
  have hx2 := Finset.mem_Icc.mp hx'.2
  have hy1 := Finset.mem_Icc.mp hy'.1
  have hy2 := Finset.mem_Icc.mp hy'.2
  have hxn1 : x.1.natAbs ≤ N := by
    have h : |x.1| ≤ (N : ℤ) := abs_le.mpr hx1
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hxn2 : x.2.natAbs ≤ N := by
    have h : |x.2| ≤ (N : ℤ) := abs_le.mpr hx2
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hyn1 : y.1.natAbs ≤ N := by
    have h : |y.1| ≤ (N : ℤ) := abs_le.mpr hy1
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hyn2 : y.2.natAbs ≤ N := by
    have h : |y.2| ≤ (N : ℤ) := abs_le.mpr hy2
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  have hd1 : (x.1 - y.1).natAbs ≤ 2 * N :=
    (Int.natAbs_sub_le _ _).trans (by omega)
  have hd2 : (x.2 - y.2).natAbs ≤ 2 * N :=
    (Int.natAbs_sub_le _ _).trans (by omega)
  rw [siteDistance, Real.sqrt_le_iff]
  constructor
  · positivity
  · norm_cast
    unfold siteSquaredDistance
    nlinarith [Nat.mul_self_le_mul_self hd1, Nat.mul_self_le_mul_self hd2]

/-- The rounded near-critical horizon is exponentially smaller than the
`exp(m)` distance cutoff. -/
theorem eventually_three_mul_nearCriticalHorizon_lt_exp :
    ∀ᶠ m : ℕ in atTop,
      3 * (nearCriticalHorizon m : ℝ) < Real.exp (m : ℝ) := by
  have hsqrt :=
    HLOZNearCriticalBridge.eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := (4 / 3 : ℝ) * Real.sqrt Real.pi) (d := (1 : ℝ) / 2)
    (p := (1 : ℝ) / 2) (q := 1)
    (by positivity) (by positivity) (by norm_num)
  have hconst :=
    HLOZNearCriticalBridge.eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := Real.log 3) (d := (1 : ℝ) / 4)
    (p := 0) (q := 1)
    (Real.log_nonneg (by norm_num)) (by positivity) (by norm_num)
  filter_upwards [eventually_log_horizon_le_four_thirds_leading,
    hsqrt, hconst, eventually_gt_atTop 0] with m hlogN hs hc hm
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hs' : (4 / 3 : ℝ) *
      (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ≤ (1 / 2 : ℝ) * m := by
    simpa only [Real.sqrt_eq_rpow, mul_assoc, Real.rpow_one] using hs
  have hc' : Real.log 3 ≤ (1 / 4 : ℝ) * m := by
    simpa only [Real.rpow_zero, mul_one, Real.rpow_one] using hc
  have hlogN' := hlogN.trans hs'
  have hlogprod : Real.log (3 * (nearCriticalHorizon m : ℝ)) < (m : ℝ) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (by exact_mod_cast (ne_of_gt (nearCriticalHorizon_pos m)))]
    have hsum : Real.log 3 + Real.log (nearCriticalHorizon m : ℝ) ≤
        (3 / 4 : ℝ) * m := by
      calc
        _ ≤ (1 / 4 : ℝ) * m + (1 / 2 : ℝ) * m :=
          add_le_add hc' hlogN'
        _ = (3 / 4 : ℝ) * m := by ring
    have hthreequarters : (3 / 4 : ℝ) * m < m := by linarith
    exact hsum.trans_lt hthreequarters
  have hprodpos : 0 < 3 * (nearCriticalHorizon m : ℝ) :=
    mul_pos (by norm_num) (by exact_mod_cast nearCriticalHorizon_pos m)
  calc
    3 * (nearCriticalHorizon m : ℝ) =
        Real.exp (Real.log (3 * (nearCriticalHorizon m : ℝ))) := by
      rw [Real.exp_log hprodpos]
    _ < Real.exp (m : ℝ) := Real.exp_lt_exp.mpr hlogprod

/-- An exponential Proposition-1.3 error is eventually below the exact
polynomial exceptional scale used in Proposition 4.7. -/
theorem eventually_exp_neg_le_sourceExceptionalRate :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-(m : ℝ))) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hlog0 := eventually_const_mul_log_sq_le_rpow
    (c := (2 : ℝ)) (c₁ := (1 : ℝ) / 2) (a := (1 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have habs0 := eventually_exp_neg_log_sq_le_rpow_neg
    (c := (2 : ℝ)) (a := 3 * kappa) (by norm_num)
    (by linarith [one_lt_three_kappa])
  have hlog := (Filter.tendsto_add_atTop_nat 1).eventually hlog0
  have habs := (Filter.tendsto_add_atTop_nat 1).eventually habs0
  filter_upwards [hlog, habs, eventually_ge_atTop 1] with m hlog habs hm
  have hm1 : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hhalf : (1 / 2 : ℝ) * (m + 1 : ℕ) ≤ (m : ℝ) := by
    calc
      _ ≤ (1 / 2 : ℝ) * (2 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hm1 (by norm_num)
      _ = (m : ℝ) := by ring
  have hlog' : 2 * Real.log ((m + 1 : ℕ) : ℝ) ^ 2 ≤
      (1 / 2 : ℝ) * (m + 1 : ℕ) := by
    simpa only [Real.rpow_one] using hlog
  have hdom : 2 * Real.log ((m + 1 : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) :=
    hlog'.trans hhalf
  have hreal : Real.exp (-(m : ℝ)) ≤
      ((m + 1 : ℕ) : ℝ) ^ (-(3 * kappa)) := by
    calc
      Real.exp (-(m : ℝ)) ≤
          Real.exp (-2 * Real.log ((m + 1 : ℕ) : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        simpa only [neg_mul] using neg_le_neg hdom
      _ ≤ ((m + 1 : ℕ) : ℝ) ^ (-(3 * kappa)) := habs
  have hexplicit := source_explicit_rate m 0 0 kappa
  norm_num [sourceScreeningConstant] at hexplicit
  simp only [sourceExceptionalRateWithPrefactor, Nat.cast_one, one_mul]
  rw [hexplicit]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ (m + 1 : ℕ))] at hreal
  simpa only [one_div, Nat.cast_add, Nat.cast_one] using hreal

private theorem simpleRandomWalk_preimage_farGap_subset_prop13
    (m : ℕ) (i : Fin 6) (r : StageIndex)
    (hhorizon : 3 * (nearCriticalHorizon m : ℝ) < Real.exp (m : ℝ))
    (hthreshold : (m : ℝ) <
      proposition13Threshold (nearCriticalHorizon m)) :
    simpleRandomWalk ⁻¹' farGapEvent m i r ⊆
      simpleRandomWalk ⁻¹'
        proposition13LowerTailEvent (nearCriticalHorizon m) := by
  intro ω hfar
  rcases hfar with ⟨hprefix, hfar⟩
  have hM : simpleRandomWalk ω ∈
      thresholdTimeEventK m (stageNumber r + 1) := hprefix.1
  have hlate : (nearCriticalHorizon m : WithTop ℕ) <
      firstKSitesReachLevel m (stageNumber r + 1) (simpleRandomWalk ω) := by
    by_contra hnot
    have hTnext : firstKSitesReachLevel m (stageNumber r + 1)
        (simpleRandomWalk ω) ≤
        (nearCriticalHorizon m : WithTop ℕ) := le_of_not_gt hnot
    have hTk := (firstKSitesReachLevel_mono_k (simpleRandomWalk ω) m
      (show stageNumber r ≤ stageNumber r + 1 by omega)).trans hTnext
    have ht := WithTop.untopA_le hTk
    have ht' := WithTop.untopA_le hTnext
    have hsite := KilledGreen.simpleRandomWalk_mem_squareDisk_of_time_le ω ht
    have hsite' := KilledGreen.simpleRandomWalk_mem_squareDisk_of_time_le ω ht'
    have hdist := siteDistance_le_three_mul_of_mem_squareDisk hsite hsite'
    exact (not_lt_of_ge hdist) (hhorizon.trans hfar)
  apply lowerMaxEvent_subset_proposition13LowerTailEvent
    nearCriticalHorizon m hthreshold
  exact lateOnThresholdEvent_subset_lowerMaxEvent
    nearCriticalHorizon m (stageNumber r + 1) ⟨hlate, hM⟩

/-- Proposition 1.3 quantitatively removes the `distance > exp(m)` branch,
with no new probabilistic premise. -/
theorem prop47FarGapEstimate_of_appendixDiskEstimate
    (hdisk : AppendixDiskEstimate) :
    Prop47FarGapEstimate 1 := by
  have hprop13 := eventually_nearCritical_prop13_bound hdisk
  filter_upwards [eventually_three_mul_nearCriticalHorizon_lt_exp,
    eventually_level_lt_proposition13Threshold_nearCriticalHorizon,
    hprop13, eventually_exp_neg_le_sourceExceptionalRate] with
      m hhorizon hthreshold hprop13m hrate
  intro i r
  calc
    simpleRandomWalkLaw (farGapEvent m i r) =
        incrementLaw (simpleRandomWalk ⁻¹' farGapEvent m i r) := by
      rw [simpleRandomWalkLaw, Measure.map_apply measurable_simpleRandomWalk
        (measurableSet_farGapEvent m i r)]
    _ ≤ incrementLaw (simpleRandomWalk ⁻¹'
          proposition13LowerTailEvent (nearCriticalHorizon m)) :=
      measure_mono (simpleRandomWalk_preimage_farGap_subset_prop13
        m i r hhorizon hthreshold)
    _ = simpleRandomWalkLaw
          (proposition13LowerTailEvent (nearCriticalHorizon m)) := by
      rw [simpleRandomWalkLaw, Measure.map_apply measurable_simpleRandomWalk
        (measurableSet_proposition13LowerTailEvent (nearCriticalHorizon m))]
    _ ≤ ENNReal.ofReal (Real.exp (-(m : ℝ))) := hprop13m
    _ ≤ sourceExceptionalRateWithPrefactor m 1 kappa := hrate

end Erdos1166.HLOZProp47Canonical
