/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos308.CrootAsymptotic

/-!
# Erdős 308: Croot's eventual interval theorem

This file assembles the large-prime-power descent and the exact small-prime-
power correction.  The cutoff is the first harmonic partial sum exceeding
`k + 3/4`; this gives the slack needed for both correction stages while
keeping the final residual strictly below one.
-/

namespace Erdos308.CrootInterval

open Filter Finset Real
open scoped BigOperators Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285 Erdos285.PrimePowers Erdos285.RoughCounts
open Erdos285.Proposition7
open Erdos308.CrootRemoval Erdos308.CrootAsymptotic

def harmonicMass (n : ℕ) : ℝ := ((harmonic n : ℚ) : ℝ)

lemma harmonicMass_tendsto_atTop : Tendsto harmonicMass atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    tendsto_log_coe_at_top
  have hsum := hlog.atTop_add Real.tendsto_harmonic_sub_log
  apply hsum.congr'
  filter_upwards with n
  dsimp [harmonicMass]
  ring

lemma exists_harmonicMass_gt (t : ℝ) : ∃ n : ℕ, t < harmonicMass n := by
  exact (harmonicMass_tendsto_atTop.eventually (eventually_gt_atTop t)).exists

noncomputable def crossingIndex (k : ℕ) : ℕ :=
  Nat.find (exists_harmonicMass_gt ((k : ℝ) + 3 / 4))

lemma crossingIndex_spec (k : ℕ) :
    (k : ℝ) + 3 / 4 < harmonicMass (crossingIndex k) :=
  Nat.find_spec (exists_harmonicMass_gt ((k : ℝ) + 3 / 4))

lemma crossingIndex_min {k n : ℕ}
    (hn : (k : ℝ) + 3 / 4 < harmonicMass n) :
    crossingIndex k ≤ n :=
  Nat.find_min' (exists_harmonicMass_gt ((k : ℝ) + 3 / 4)) hn

lemma crossingIndex_pos (k : ℕ) : 0 < crossingIndex k := by
  by_contra h
  have hx : crossingIndex k = 0 := Nat.eq_zero_of_not_pos h
  have hs := crossingIndex_spec k
  rw [hx] at hs
  simp [harmonicMass] at hs
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma crossingIndex_pred_mass_le (k : ℕ) :
    harmonicMass (crossingIndex k - 1) ≤ (k : ℝ) + 3 / 4 := by
  apply le_of_not_gt
  intro h
  have hmin := Nat.find_min
    (exists_harmonicMass_gt ((k : ℝ) + 3 / 4))
    (show crossingIndex k - 1 < crossingIndex k by
      exact Nat.sub_one_lt (crossingIndex_pos k).ne')
  exact hmin h

lemma crossingIndex_mass_lt_add_one {k : ℕ} (hx : 4 < crossingIndex k) :
    harmonicMass (crossingIndex k) < (k : ℝ) + 1 := by
  let x := crossingIndex k
  have hxpos : 0 < x := crossingIndex_pos k
  have hxEq : x - 1 + 1 = x := Nat.sub_add_cancel (by omega : 1 ≤ x)
  have hrec : harmonicMass x =
      harmonicMass (x - 1) + ((x : ℝ))⁻¹ := by
    dsimp [harmonicMass]
    conv_lhs => rw [← hxEq]
    rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, hxEq]
  have hinv : ((x : ℝ))⁻¹ < 1 / 4 := by
    simpa [one_div] using
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4)
        (by exact_mod_cast hx : (4 : ℝ) < x)
  rw [hrec]
  linarith [crossingIndex_pred_mass_le k]

lemma crossingIndex_tendsto_atTop : Tendsto crossingIndex atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨⌈harmonicMass b⌉₊, ?_⟩
  intro k hk
  by_contra hnot
  have hxb : crossingIndex k < b := Nat.lt_of_not_ge hnot
  have hmono : harmonic (crossingIndex k) ≤ harmonic b :=
    harmonic_mono_local hxb.le
  have hmonoR : harmonicMass (crossingIndex k) ≤ harmonicMass b := by
    dsimp [harmonicMass]
    exact_mod_cast hmono
  have hceil : harmonicMass b ≤ (⌈harmonicMass b⌉₊ : ℕ) := Nat.le_ceil _
  have hkR : ((⌈harmonicMass b⌉₊ : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
  linarith [crossingIndex_spec k, hmonoR, hceil, hkR]

lemma crossingIndex_le_of_harmonicFloor {N k : ℕ}
    (hk : k + 1 ≤ ⌊harmonicMass N⌋₊) : crossingIndex k ≤ N := by
  apply crossingIndex_min
  have hfloor : ((⌊harmonicMass N⌋₊ : ℕ) : ℝ) ≤ harmonicMass N :=
    Nat.floor_le (by
      dsimp [harmonicMass]
      exact_mod_cast harmonic_nonneg_local N)
  have hkR : ((k + 1 : ℕ) : ℝ) ≤ (⌊harmonicMass N⌋₊ : ℕ) := by
    exact_mod_cast hk
  norm_num at hkR
  linarith

lemma rec_sum_sdiff_eq {A B : Finset ℕ} (hBA : B ⊆ A) :
    UnitFractions.rec_sum (A \ B) =
      UnitFractions.rec_sum A - UnitFractions.rec_sum B := by
  unfold UnitFractions.rec_sum
  have h := Finset.sum_sdiff hBA (f := fun n : ℕ ↦ (1 : ℚ) / n)
  linarith

lemma fullSmoothBlock_subset_Icc (x : ℕ) :
    fullSmoothBlock x (proposition6MainCutoff x) ⊆ Icc 1 x := by
  intro n hn
  have hn' := mem_initialSmoothBlock.mp hn
  exact Finset.mem_Icc.mpr ⟨by omega, hn'.2.1⟩

lemma totalEliminationBudget_mono_local (x : ℕ) :
    Monotone (totalEliminationBudget x) := by
  intro a b hab
  unfold totalEliminationBudget
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hab)) (fun _ _ _ ↦ Nat.zero_le _)

/-! ## Eventual arithmetic data at a fixed cutoff -/

theorem eventually_croot_assembly_data :
    ∀ᶠ x : ℕ in atTop,
      reciprocalMass (roughNumbersIn 1 x (mainCutoffNat x)) < 1 / 16 ∧
      deletionBudgetRatio removalRatio x < 1 / 16 ∧
      totalEliminationBudget x (mainCutoffNat x) ≤ deletionBudget x ∧
      2 * Erdos285.approximationCorrectionScale x ^ 4 ≤
        ⌊removalRatio * (x : ℝ)⌋₊ ∧
      2 * Erdos285.approximationCorrectionScale x ^ 4 ≤ mainCutoffNat x ∧
      (∀ k : ℕ, Nonempty (RemovalDescentOutcome
        (removalBase x (proposition6MainCutoff x)) x
        (Erdos285.approximationCorrectionScale x)
        (initialState k x (proposition6MainCutoff x)))) ∧
      (∀ r : ℚ,
        largestPrimePowerPart r.den ≤ Erdos285.approximationCorrectionScale x →
        1 / Real.log (Erdos285.approximationCorrectionScale x : ℝ) < (r : ℝ) →
        (r : ℝ) < 1 →
        ∃ E : Finset ℕ,
          E.card = 2 * piStar (Erdos285.approximationCorrectionScale x) ∧
          UnitFractions.rec_sum E = r ∧
          0 ∉ E ∧
          ∀ n ∈ E,
            n ≤ 2 * Erdos285.approximationCorrectionScale x ^ 4) ∧
      1 / Real.log (Erdos285.approximationCorrectionScale x : ℝ) < 1 / 2 ∧
      4 < x := by
  have hrough := globalRoughMass_tendsto_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hbudget := (deletionBudgetRatio_tendsto_zero removalRatio removalRatio_pos).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 16))
  have hprop7 := correctionScale_tendsto_atTop.eventually
    (eventually_proposition7 (by norm_num : (0 : ℝ) < 1))
  have hylog := correctionScale_tendsto_atTop.eventually
    (eventually_ge_atTop ⌈Real.exp 3⌉₊)
  filter_upwards [hrough, hbudget, eventually_totalEliminationBudget_le,
    eventually_correctionCutoff_le_removalFloor,
    eventually_correctionCutoff_le_mainCutoff,
    eventually_crootRemovalDescent, hprop7, hylog, eventually_ge_atTop 5]
      with x hrough hbudget htotal hremove hsmooth hdescent hprop7 hylog hx
  refine ⟨hrough, hbudget, htotal, hremove, hsmooth, hdescent, hprop7, ?_, by omega⟩
  have hceil : Real.exp 3 ≤ (⌈Real.exp 3⌉₊ : ℕ) := Nat.le_ceil _
  have hyR : ((⌈Real.exp 3⌉₊ : ℕ) : ℝ) ≤
      Erdos285.approximationCorrectionScale x := by exact_mod_cast hylog
  have hlog : (3 : ℝ) ≤
      Real.log (Erdos285.approximationCorrectionScale x : ℝ) := by
    have hpos : 0 < (Erdos285.approximationCorrectionScale x : ℝ) := by
      exact (Real.exp_pos 3).trans_le (hceil.trans hyR)
    have := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 3)) (Set.mem_Ioi.mpr hpos) (hceil.trans hyR)
    simpa using this
  have hlogpos : 0 < Real.log (Erdos285.approximationCorrectionScale x : ℝ) :=
    (by norm_num : (0 : ℝ) < 3).trans_le hlog
  exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hlog).trans_lt
    (by norm_num : (1 / 3 : ℝ) < 1 / 2)

/-! ## Assembly of the exact representation -/

theorem eventually_large_target_representable :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ,
      k + 1 ≤ ⌊harmonicMass N⌋₊ →
      ∃ A : Finset ℕ,
        A ⊆ Icc 1 N ∧ UnitFractions.rec_sum A = (k : ℚ) := by
  have hdata := crossingIndex_tendsto_atTop.eventually eventually_croot_assembly_data
  have hcrossLarge := crossingIndex_tendsto_atTop.eventually (eventually_ge_atTop 5)
  filter_upwards [hdata, hcrossLarge] with k hdata hxlarge
  intro N hkN
  let x := crossingIndex k
  let z := proposition6MainCutoff x
  let y := Erdos285.approximationCorrectionScale x
  have hxN : x ≤ N := crossingIndex_le_of_harmonicFloor hkN
  obtain ⟨out⟩ := hdata.2.2.2.2.2.1 k
  have hstartMeasure : (initialState k x z).primePowerMeasure ≤ mainCutoffNat x := by
    have hz : 0 ≤ z := by dsimp [z, proposition6MainCutoff]; positivity
    simpa [z, mainCutoffNat_eq] using initialState_measure_le_floor (k := k) (x := x) hz
  have hcard : out.removed.card ≤ deletionBudget x :=
    out.card_le.trans ((totalEliminationBudget_mono_local x hstartMeasure).trans hdata.2.2.1)
  have hremovedMass : reciprocalMass out.removed < 1 / 16 := by
    calc
      reciprocalMass out.removed ≤
          (out.removed.card : ℝ) / (removalRatio * (x : ℝ)) := by
        apply reciprocalMass_le_card_div removalRatio_pos (by simpa [x] using crossingIndex_pos k)
        intro n hn
        exact initialSmoothBlock_lower removalRatio_pos.le
          (out.removed_subset_base hn)
      _ ≤ deletionBudgetRatio removalRatio x := by
        dsimp [deletionBudgetRatio]
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcard)
          (mul_nonneg removalRatio_pos.le (Nat.cast_nonneg x))
      _ < 1 / 16 := hdata.2.1
  have hstartMass :
      reciprocalMass (fullSmoothBlock x z) = harmonicMass x -
        reciprocalMass (roughNumbersIn 1 x (mainCutoffNat x)) := by
    simpa [x, z, harmonicMass] using fullSmoothBlock_mass x
  have hselectedMass : reciprocalMass out.final.terms.selected =
      reciprocalMass (fullSmoothBlock x z) - reciprocalMass out.removed := by
    change reciprocalMass out.final.terms.selected =
      reciprocalMass (initialSmoothBlock 0 x z) - reciprocalMass out.removed
    rw [out.selected_eq]
    simpa [initialState, initialApproximationState, x, z] using
      reciprocalMass_sdiff out.removed_subset_selected
  have hresLower : (1 / 2 : ℝ) <
      reciprocalMass out.final.terms.selected - (k : ℝ) := by
    rw [hselectedMass, hstartMass]
    linarith [crossingIndex_spec k, hdata.1, hremovedMass]
  have hresUpper : reciprocalMass out.final.terms.selected - (k : ℝ) < 1 := by
    have hsubset : out.final.terms.selected ⊆ fullSmoothBlock x z := by
      rw [out.selected_eq]
      exact Finset.sdiff_subset
    have hmassLe := reciprocalMass_mono hsubset
    have hharm : reciprocalMass (fullSmoothBlock x z) ≤ harmonicMass x := by
      rw [hstartMass]
      linarith [reciprocalMass_nonneg (roughNumbersIn 1 x (mainCutoffNat x))]
    have hcross : harmonicMass x < (k : ℝ) + 1 := by
      simpa [x] using crossingIndex_mass_lt_add_one (k := k) (by omega)
    linarith
  let r : ℚ := -out.final.residual
  have hrCast : (r : ℝ) = reciprocalMass out.final.terms.selected - (k : ℝ) := by
    dsimp [r]
    have hbal := out.final.balance
    have hcast : ((UnitFractions.rec_sum out.final.terms.selected : ℚ) : ℝ) =
        reciprocalMass out.final.terms.selected :=
      ratCast_recSum_eq_reciprocalMass _
    have hbalR : reciprocalMass out.final.terms.selected +
        (out.final.residual : ℝ) = (k : ℝ) := by
      rw [← hcast, ← Rat.cast_add, hbal]
      simp
    rw [Rat.cast_neg]
    linarith
  have hrLower : 1 / Real.log (y : ℝ) < (r : ℝ) := by
    rw [hrCast]
    exact hdata.2.2.2.2.2.2.2.1.trans hresLower
  have hrUpper : (r : ℝ) < 1 := hrCast ▸ hresUpper
  have hrSmooth : largestPrimePowerPart r.den ≤ y := by
    change largestPrimePowerPart (-out.final.residual).den ≤
      Erdos285.approximationCorrectionScale x
    simpa [ResidualApproximationState.primePowerMeasure] using out.measure_le
  obtain ⟨E, hEcard, hEsum, hEzero, hEbound⟩ :=
    hdata.2.2.2.2.2.2.1 r hrSmooth hrLower hrUpper
  have hEremove : ∀ n ∈ E, n ≤ ⌊removalRatio * (x : ℝ)⌋₊ := by
    intro n hn
    exact (hEbound n hn).trans hdata.2.2.2.1
  have hEfull : E ⊆ fullSmoothBlock x z := by
    intro n hn
    rw [fullSmoothBlock, mem_initialSmoothBlock]
    have hnpos : 0 < n := by
      exact Nat.pos_of_ne_zero (fun hn0 ↦ hEzero (hn0 ▸ hn))
    have hncut : n ≤ mainCutoffNat x :=
      (hEbound n hn).trans hdata.2.2.2.2.1
    have hnx : n ≤ x := by
      have hfloor : ((⌊removalRatio * (x : ℝ)⌋₊ : ℕ) : ℝ) ≤ (x : ℝ) :=
        (Nat.floor_le (mul_nonneg removalRatio_pos.le (Nat.cast_nonneg x))).trans
          (mul_le_of_le_one_left (Nat.cast_nonneg x) removalRatio_le_one)
      exact (hEremove n hn).trans (by exact_mod_cast hfloor)
    have hz0 : 0 ≤ z := by dsimp [z, proposition6MainCutoff]; positivity
    have hsmooth : UnitFractions.is_smooth z n :=
      (isSmooth_iff_largestPrimePowerPart_le_floor hz0 hnpos.ne').2 (by
        simpa [z, mainCutoffNat_eq] using
          (largestPrimePowerPart_le.trans hncut))
    exact ⟨by simpa using hnpos, hnx, hsmooth⟩
  have hdisj : Disjoint E out.removed := by
    rw [Finset.disjoint_left]
    intro n hnE hnR
    have hnlow := (mem_initialSmoothBlock.mp (out.removed_subset_base hnR)).1
    exact (Nat.not_lt_of_ge (hEremove n hnE)) hnlow
  have hEfinal : E ⊆ out.final.terms.selected := by
    rw [out.selected_eq]
    intro n hn
    exact Finset.mem_sdiff.mpr
      ⟨hEfull hn, fun hnR ↦ Finset.disjoint_left.mp hdisj hn hnR⟩
  refine ⟨out.final.terms.selected \ E, ?_, ?_⟩
  · exact (Finset.sdiff_subset.trans (by
      rw [out.selected_eq]
      exact Finset.sdiff_subset.trans
        ((fullSmoothBlock_subset_Icc x).trans
          (Finset.Icc_subset_Icc_right hxN))))
  · rw [rec_sum_sdiff_eq hEfinal, hEsum]
    have hbal := out.final.balance
    dsimp [r]
    linarith

end

end Erdos308.CrootInterval

#print axioms Erdos308.CrootInterval.eventually_large_target_representable
