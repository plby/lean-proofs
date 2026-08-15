/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.LastCrossing
import ErdosProblems.Erdos285.Proposition4

/-!
# Erdős 285: the concrete last-crossing score

This file instantiates the nonmonotone inversion theorem from
`LastCrossing.lean` with the moving smooth block and exact-correction score
defined in `Proposition4.lean`.
-/

namespace Erdos285.ScoreCrossing

open Filter Finset Real Asymptotics
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open RoughCounts

/-! ## Motion of the lower endpoint -/

lemma eventually_martinMargin_succ_le :
    ∀ᶠ x : ℕ in atTop,
      Proposition4.martinMargin (x + 1) ≤ Proposition4.martinMargin x := by
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hlog
  have hx : (0 : ℝ) < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    exact zero_lt_one.trans ((Real.log_pos_iff hx0).mp hlog)
  have hlogle : Real.log (x : ℝ) ≤ Real.log (x + 1 : ℕ) := by
    have hxsucc : (0 : ℝ) < (x + 1 : ℕ) := by exact_mod_cast (show 0 < x + 1 by omega)
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hxsucc)
      (by exact_mod_cast Nat.le_succ x)
  have hsqrt := Real.sqrt_le_sqrt hlogle
  dsimp [Proposition4.martinMargin]
  exact (inv_le_inv₀ (Real.sqrt_pos.2 (hlog.trans_le hlogle))
    (Real.sqrt_pos.2 hlog)).2 hsqrt

lemma log_succ_sub_log_le_inv {x : ℕ} (hx : 0 < x) :
    Real.log (x + 1 : ℕ) - Real.log (x : ℝ) ≤ (x : ℝ)⁻¹ := by
  have h := Analytic.log_succ_ratio_le_reciprocal hx
  rw [Real.log_div (by positivity) (by positivity)] at h
  simpa [one_div] using h

/-- The slowly varying contribution `x/sqrt(log x)` is eventually
nondecreasing. -/
lemma eventually_weighted_martinMargin_mono :
    ∀ᶠ x : ℕ in atTop,
      (x : ℝ) * Proposition4.martinMargin x ≤
        (x + 1 : ℕ) * Proposition4.martinMargin (x + 1) := by
  filter_upwards [tendsto_log_coe_at_top.eventually (eventually_gt_atTop (1 : ℝ))]
    with x hlog
  have hxNat : 0 < x := by
    have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    have hx1 := (Real.log_pos_iff hx0).mp (zero_lt_one.trans hlog)
    exact_mod_cast (zero_lt_one.trans hx1)
  have hx : (0 : ℝ) < x := by exact_mod_cast hxNat
  have hlogSucc : 0 < Real.log (x + 1 : ℕ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < x + 1 by omega))
  have hlogDiff := log_succ_sub_log_le_inv hxNat
  have hsq : (x : ℝ) ^ 2 * Real.log (x + 1 : ℕ) ≤
      ((x + 1 : ℕ) : ℝ) ^ 2 * Real.log (x : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hlogDiff (sq_nonneg (x : ℝ))
    have hxinv : (x : ℝ) ^ 2 * (x : ℝ)⁻¹ = x := by field_simp
    have hinc : (x : ℝ) ^ 2 *
        (Real.log (x + 1 : ℕ) - Real.log (x : ℝ)) ≤ x := by
      simpa [hxinv] using hmul
    have hinc' : (x : ℝ) ^ 2 *
        (Real.log ((x : ℝ) + 1) - Real.log (x : ℝ)) ≤ x := by
      simpa only [Nat.cast_add, Nat.cast_one] using hinc
    have hterm : (x : ℝ) ≤ (2 * x + 1) * Real.log x := by
      calc
        (x : ℝ) ≤ (2 * x + 1) * 1 := by nlinarith
        _ ≤ (2 * x + 1) * Real.log x := by
          gcongr
    push_cast
    calc
      (x : ℝ) ^ 2 * Real.log ((x : ℝ) + 1) =
          (x : ℝ) ^ 2 * Real.log (x : ℝ) +
            (x : ℝ) ^ 2 *
              (Real.log ((x : ℝ) + 1) - Real.log (x : ℝ)) := by ring
      _ ≤ (x : ℝ) ^ 2 * Real.log (x : ℝ) + x := by linarith
      _ ≤ ((x : ℝ) + 1) ^ 2 * Real.log (x : ℝ) := by
        nlinarith
  have hleft0 : 0 ≤ (x : ℝ) * Real.sqrt (Real.log (x + 1 : ℕ)) := by positivity
  have hright0 : 0 ≤ ((x + 1 : ℕ) : ℝ) *
      Real.sqrt (Real.log (x : ℝ)) := by positivity
  have hsq' : ((x : ℝ) * Real.sqrt (Real.log (x + 1 : ℕ))) ^ 2 ≤
      (((x + 1 : ℕ) : ℝ) * Real.sqrt (Real.log (x : ℝ))) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hlogSucc.le,
      Real.sq_sqrt (zero_lt_one.trans hlog).le]
    exact hsq
  have hcross : (x : ℝ) * Real.sqrt (Real.log (x + 1 : ℕ)) ≤
      ((x + 1 : ℕ) : ℝ) * Real.sqrt (Real.log (x : ℝ)) := by
    nlinarith [sq_nonneg
      (((x + 1 : ℕ) : ℝ) * Real.sqrt (Real.log (x : ℝ)) -
        (x : ℝ) * Real.sqrt (Real.log (x + 1 : ℕ)))]
  dsimp [Proposition4.martinMargin]
  change (x : ℝ) / Real.sqrt (Real.log (x : ℝ)) ≤
    ((x + 1 : ℕ) : ℝ) / Real.sqrt (Real.log (x + 1 : ℕ))
  exact (div_le_div_iff₀ (Real.sqrt_pos.2 (zero_lt_one.trans hlog))
    (Real.sqrt_pos.2 hlogSucc)).2 hcross

lemma eventually_martinLowerEndpoint_mono :
    ∀ᶠ x : ℕ in atTop,
      Proposition4.martinLowerRatio x * (x : ℝ) ≤
        Proposition4.martinLowerRatio (x + 1) * (x + 1 : ℕ) := by
  filter_upwards [eventually_weighted_martinMargin_mono] with x hm
  dsimp [Proposition4.martinLowerRatio]
  have hexp : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  push_cast
  have hm' : (x : ℝ) * Proposition4.martinMargin x ≤
      ((x : ℝ) + 1) * Proposition4.martinMargin (x + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hm
  calc
    (Real.exp (-1) + Proposition4.martinMargin x) * (x : ℝ) =
        Real.exp (-1) * x + x * Proposition4.martinMargin x := by ring
    _ ≤ Real.exp (-1) * (x + 1) +
        (x + 1) * Proposition4.martinMargin (x + 1) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (by linarith) hexp) hm'
    _ = (Real.exp (-1) + Proposition4.martinMargin (x + 1)) * (x + 1) := by ring

lemma eventually_martinLowerFloor_mono :
    ∀ᶠ x : ℕ in atTop,
      ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊ ≤
        ⌊Proposition4.martinLowerRatio (x + 1) * (x + 1 : ℕ)⌋₊ := by
  filter_upwards [eventually_martinLowerEndpoint_mono] with x hx
  exact Nat.floor_mono hx

/-! ## One-step change of the smooth block -/

lemma newly_smooth_dvd_cutoffSucc {x n : ℕ}
    (hcut : mainCutoffNat (x + 1) ≤ mainCutoffNat x + 1)
    (hnzero : n ≠ 0)
    (hnew : UnitFractions.is_smooth (proposition6MainCutoff (x + 1)) n)
    (hold : ¬ UnitFractions.is_smooth (proposition6MainCutoff x) n) :
    mainCutoffNat x + 1 ∣ n := by
  have hnewMax : PrimePowers.largestPrimePowerPart n ≤ mainCutoffNat (x + 1) :=
    (isSmooth_iff_largestPrimePowerPart_le_floor
      (proposition6MainCutoff_nonneg (x + 1)) hnzero).1 hnew
  have holdMax : ¬ PrimePowers.largestPrimePowerPart n ≤ mainCutoffNat x := by
    intro h
    exact hold ((isSmooth_iff_largestPrimePowerPart_le_floor
      (proposition6MainCutoff_nonneg x) hnzero).2 h)
  have heq : PrimePowers.largestPrimePowerPart n = mainCutoffNat x + 1 := by omega
  have hn2 : 2 ≤ n := by
    by_contra hnlt
    have hempty : PrimePowers.primePowerParts n = ∅ :=
      PrimePowers.primePowerParts_empty_iff.mpr (Nat.lt_of_not_ge hnlt)
    have hz : PrimePowers.largestPrimePowerPart n = 0 := by
      simp [PrimePowers.largestPrimePowerPart, hempty]
    omega
  have hmem := PrimePowers.largestPrimePowerPart_mem hn2
  have hspec := (PrimePowers.mem_primePowerParts hnzero).mp hmem
  rw [← heq]
  exact hspec.2.1

lemma martinInitialBlock_succ_subset (x : ℕ)
    (hfloor : ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊ ≤
      ⌊Proposition4.martinLowerRatio (x + 1) * (x + 1 : ℕ)⌋₊)
    (hcut : mainCutoffNat (x + 1) ≤ mainCutoffNat x + 1) :
    Proposition4.martinInitialBlock (x + 1) ⊆
      Proposition4.martinInitialBlock x ∪
        insert (x + 1) (multiplesUpTo x (mainCutoffNat x + 1)) := by
  intro n hn
  by_cases hnold : n ∈ Proposition4.martinInitialBlock x
  · exact Finset.mem_union_left _ hnold
  apply Finset.mem_union_right
  have hn' := hn
  simp only [Proposition4.martinInitialBlock, initialBlockAt, initialSmoothBlock,
    Finset.mem_filter, Finset.mem_Ioc] at hn'
  by_cases hnx : n ≤ x
  · rw [Finset.mem_insert]
    right
    rw [mem_multiplesUpTo]
    refine ⟨?_, hnx, ?_⟩
    · omega
    · apply newly_smooth_dvd_cutoffSucc hcut (by omega) hn'.2
      intro hsold
      apply hnold
      simp only [Proposition4.martinInitialBlock, initialBlockAt, initialSmoothBlock,
        Finset.mem_filter, Finset.mem_Ioc]
      exact ⟨⟨lt_of_le_of_lt hfloor hn'.1.1, hnx⟩, hsold⟩
  · rw [Finset.mem_insert]
    left
    omega

lemma martinInitialBlock_succ_card_le (x : ℕ)
    (hfloor : ⌊Proposition4.martinLowerRatio x * (x : ℝ)⌋₊ ≤
      ⌊Proposition4.martinLowerRatio (x + 1) * (x + 1 : ℕ)⌋₊)
    (hcut : mainCutoffNat (x + 1) ≤ mainCutoffNat x + 1) :
    (Proposition4.martinInitialBlock (x + 1)).card ≤
      (Proposition4.martinInitialBlock x).card +
        (x / (mainCutoffNat x + 1) + 1) := by
  calc
    (Proposition4.martinInitialBlock (x + 1)).card ≤
        (Proposition4.martinInitialBlock x ∪
          insert (x + 1) (multiplesUpTo x (mainCutoffNat x + 1))).card :=
      Finset.card_le_card (martinInitialBlock_succ_subset x hfloor hcut)
    _ ≤ (Proposition4.martinInitialBlock x).card +
        (insert (x + 1) (multiplesUpTo x (mainCutoffNat x + 1))).card :=
      Finset.card_union_le _ _
    _ ≤ (Proposition4.martinInitialBlock x).card +
        ((multiplesUpTo x (mainCutoffNat x + 1)).card + 1) := by
      gcongr
      exact Finset.card_insert_le _ _
    _ = (Proposition4.martinInitialBlock x).card +
        (x / (mainCutoffNat x + 1) + 1) := by
      have hcard : (multiplesUpTo x (mainCutoffNat x + 1)).card =
          x / (mainCutoffNat x + 1) := by
        simpa [multiplesUpTo] using
          (UnitFractions.count_multiples (n := x)
            (show 1 ≤ mainCutoffNat x + 1 by omega))
      rw [hcard]

theorem eventually_martinInitialBlock_succ_card_le :
    ∀ᶠ x : ℕ in atTop,
      (Proposition4.martinInitialBlock (x + 1)).card ≤
        (Proposition4.martinInitialBlock x).card +
          (x / (mainCutoffNat x + 1) + 1) := by
  filter_upwards [eventually_martinLowerFloor_mono,
    LastCrossing.eventually_mainCutoffNat_succ_le] with x hfloor hcut
  exact martinInitialBlock_succ_card_le x hfloor hcut

/-! ## The concrete score jump -/

theorem eventually_martinScore_succ_le :
    ∀ᶠ x : ℕ in atTop,
      Proposition4.martinScore (x + 1) ≤
        Proposition4.martinScore x + LastCrossing.logarithmicStepJump x := by
  filter_upwards [eventually_martinInitialBlock_succ_card_le] with x hblock
  have hcorr := Proposition4.correctionCount_fifthRoot_succ_le x
  simp only [Proposition4.martinScore, LastCrossing.logarithmicStepJump]
  omega

/-! ## The unconditional selected scale -/

lemma martinScore_exists_above (t : ℕ) :
    ∃ x : ℕ, t < Proposition4.martinScore x := by
  obtain ⟨a, ha⟩ :=
    (tendsto_atTop_atTop.mp Proposition4.martinScore_tendsto_atTop) (t + 1)
  refine ⟨a, ?_⟩
  exact lt_of_lt_of_le (Nat.lt_succ_self t) (ha a le_rfl)

/-- The first cutoff at which the full source score exceeds the requested
number of terms. -/
def martinFirstAbove : ℕ → ℕ :=
  LastCrossing.firstAbove Proposition4.martinScore martinScore_exists_above

lemma martinFirstAbove_crosses (t : ℕ) :
    t < Proposition4.martinScore (martinFirstAbove t) :=
  LastCrossing.firstAbove_spec t

lemma martinFirstAbove_tendsto_atTop : Tendsto martinFirstAbove atTop atTop :=
  LastCrossing.firstAbove_tendsto_atTop martinScore_exists_above

/-- The largest cutoff no later than the first crossing whose score is still
at most the requested cardinality. -/
def martinSelectedScale : ℕ → ℕ :=
  LastCrossing.lastBelow Proposition4.martinScore martinFirstAbove

lemma martinSelectedScale_tendsto_atTop : Tendsto martinSelectedScale atTop atTop :=
  LastCrossing.lastBelow_tendsto_atTop Proposition4.martinScore_zero
    martinFirstAbove_tendsto_atTop

lemma martinScore_selected_le (t : ℕ) :
    Proposition4.martinScore (martinSelectedScale t) ≤ t :=
  LastCrossing.sourceCount_lastBelow_le Proposition4.martinScore_zero t

lemma martinSelectedScale_ratio_tendsto :
    Tendsto (fun t : ℕ ↦ (martinSelectedScale t : ℝ) / (t : ℝ)) atTop
      (nhds Analytic.densityConstant) := by
  have hd : 0 < 1 - Real.exp (-1) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  have h := LastCrossing.lastBelow_ratio_tendsto_of_cap_tendsto
    Proposition4.martinScore_zero hd martinFirstAbove_tendsto_atTop
    Proposition4.martinScore_ratio_tendsto
    (Filter.Eventually.of_forall martinFirstAbove_crosses)
    eventually_martinScore_succ_le LastCrossing.logarithmicStepJump_isLittleO
  have hinv : (1 - Real.exp (-1))⁻¹ = Analytic.densityConstant := by
    rw [← Analytic.densityConstant_inv, inv_inv]
  simpa [martinSelectedScale, hinv] using h

lemma eventually_selected_deficit_le_stepJump :
    ∀ᶠ t : ℕ in atTop,
      t - Proposition4.martinScore (martinSelectedScale t) ≤
        LastCrossing.logarithmicStepJump (martinSelectedScale t) := by
  exact LastCrossing.eventually_deficit_lastBelow_le_jump
    Proposition4.martinScore_zero martinFirstAbove_tendsto_atTop
    (Filter.Eventually.of_forall martinFirstAbove_crosses)
    eventually_martinScore_succ_le

/-- The exact-cardinality deficit fits inside one Proposition 6 deletion
budget at the selected scale. -/
theorem eventually_selected_deficit_le_deletionBudget :
    ∀ᶠ t : ℕ in atTop,
      t - Proposition4.martinScore (martinSelectedScale t) ≤
        proposition6DeletionBudget (martinSelectedScale t) := by
  have hbudget := martinSelectedScale_tendsto_atTop.eventually
    LastCrossing.eventually_logarithmicStepJump_le_deletionBudget
  filter_upwards [eventually_selected_deficit_le_stepJump, hbudget]
    with t hdef hstep
  exact hdef.trans hstep

lemma selected_correctionCount_le (t : ℕ) :
    correctionCount (Proposition4.fifthRootFloor (martinSelectedScale t)) ≤ t := by
  have hs := martinScore_selected_le t
  simp only [Proposition4.martinScore] at hs
  omega

/-- The full selected block has no more than the number of main terms left
after reserving the exact-correction cardinality. -/
lemma selected_block_card_le_mainCount (t : ℕ) :
    (Proposition4.martinInitialBlock (martinSelectedScale t)).card ≤
      mainCount t (Proposition4.fifthRootFloor (martinSelectedScale t)) := by
  have hs := martinScore_selected_le t
  simp only [Proposition4.martinScore, mainCount] at hs ⊢
  omega

end

end Erdos285.ScoreCrossing

#print axioms Erdos285.ScoreCrossing.eventually_martinLowerFloor_mono
#print axioms Erdos285.ScoreCrossing.eventually_martinScore_succ_le
#print axioms Erdos285.ScoreCrossing.martinSelectedScale_ratio_tendsto
#print axioms Erdos285.ScoreCrossing.eventually_selected_deficit_le_deletionBudget
