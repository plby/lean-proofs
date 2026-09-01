/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1217.AnalyticWeight
import ErdosProblems.Erdos1217.Density
import ErdosProblems.Erdos1217.MarkovChain
import ErdosProblems.Erdos1217.Moments
import ErdosProblems.Erdos1217.OmegaBound
import ErdosProblems.Erdos1217.Reindex

/-!
# Resolution of Erdős Problem 1217

This file assembles the analytic invariant weight, its upward Markov chain,
the first- and second-moment estimates, reverse Fatou, and the deterministic
enumeration of visits.  The resulting theorem is the stronger set-valued
form: positive weighted logarithmic rate alone produces a divisibility chain
with at least the same rate.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal ArithmeticFunction.Omega

noncomputable section

namespace Erdos1217

attribute [local instance] Classical.propDecidable

/-! ## The analytic weight as upward-chain data -/

/-- The ABLLPSTT invariant weight, bundled with its row-normalization identity. -/
noncomputable def nuLambdaData : UpwardChain.Data where
  nu := nuLambda
  nu_one := nuLambda_one
  nu_pos := nuLambda_pos
  incoming := by
    intro n hn
    simpa only [incomingWeight, Nat.cast_mul] using
      (hasSum_incomingWeight_subtype hn)

private noncomputable def nuLambdaMassNat (A : Set ℕ) (X : ℕ) : ℝ :=
  ∑ n ∈ (positiveBelowNat X).filter (fun n ↦ n ∈ A), nuLambda n

private noncomputable def nuLambdaMeanTerm (A : Set ℕ) (X : ℕ) : ENNReal :=
  ENNReal.ofReal
    (nuLambdaMassNat A X / Real.log (Real.log (X : ℝ)))

private noncomputable def discrepancyTotal : ℝ :=
  ∑' n : ℕ,
    if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0

private lemma discrepancyTotal_nonneg : 0 ≤ discrepancyTotal := by
  exact tsum_nonneg fun n ↦ by
    split_ifs with hn
    · exact (nuLambda_error_bound hn).1
    · exact le_rfl

private lemma nuLambdaMassNat_nonneg (A : Set ℕ) (X : ℕ) :
    0 ≤ nuLambdaMassNat A X := by
  exact Finset.sum_nonneg fun n _ ↦ (nuLambda_nonneg n)

private lemma weightedMassNat_le_nuLambdaMassNat_add (A : Set ℕ) (X : ℕ) :
    weightedMassNat A X ≤ nuLambdaMassNat A X + discrepancyTotal := by
  let S := (positiveBelowNat X).filter (fun n ↦ n ∈ A)
  have hpoint (n : ℕ) (hn : n ∈ S) :
      doublyHarmonicWeight n ≤ nuLambda n +
        (if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0) := by
    have hnpos : 1 ≤ n := (mem_positiveBelowNat_iff.mp
      (Finset.mem_filter.mp hn).1).1
    rcases hnpos.eq_or_lt with rfl | hnlt
    · simp [nuLambda_one]
    · simp only [if_pos (by omega : 2 ≤ n)]
      linarith
  calc
    weightedMassNat A X = ∑ n ∈ S, doublyHarmonicWeight n := rfl
    _ ≤ ∑ n ∈ S, (nuLambda n +
        (if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0)) :=
      Finset.sum_le_sum hpoint
    _ = nuLambdaMassNat A X +
        ∑ n ∈ S, (if 2 ≤ n then doublyHarmonicWeight n - nuLambda n else 0) := by
      rw [Finset.sum_add_distrib]
      rfl
    _ ≤ nuLambdaMassNat A X + discrepancyTotal := by
      simpa only [discrepancyTotal, add_comm] using
        add_le_add_right (finite_sum_nuLambda_discrepancy_le_tsum S)
          (nuLambdaMassNat A X)

private lemma weightedTermNat_le_nuLambdaMeanTerm_add (A : Set ℕ) {X : ℕ}
    (hX : 0 < Real.log (Real.log (X : ℝ))) :
    weightedTermNat A X ≤ nuLambdaMeanTerm A X +
      ENNReal.ofReal (discrepancyTotal / Real.log (Real.log (X : ℝ))) := by
  have hquot := div_le_div_of_nonneg_right
    (weightedMassNat_le_nuLambdaMassNat_add A X) hX.le
  rw [weightedTermNat, nuLambdaMeanTerm]
  refine (ENNReal.ofReal_le_ofReal hquot).trans_eq ?_
  rw [add_div]
  exact ENNReal.ofReal_add
    (div_nonneg (nuLambdaMassNat_nonneg A X) hX.le)
    (div_nonneg discrepancyTotal_nonneg hX.le)

private lemma tendsto_discrepancyTerm_zero :
    Tendsto (fun X : ℕ ↦ ENNReal.ofReal
      (discrepancyTotal / Real.log (Real.log (X : ℝ)))) atTop (nhds 0) := by
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
    (tendsto_log_log_natCast_atTop.const_div_atTop discrepancyTotal)

private theorem weightedRateNat_le_limsup_nuLambdaMeanTerm (A : Set ℕ) :
    weightedRateNat A ≤ limsup (nuLambdaMeanTerm A) atTop := by
  let e : ℕ → ENNReal := fun X ↦ ENNReal.ofReal
    (discrepancyTotal / Real.log (Real.log (X : ℝ)))
  have hle : ∀ᶠ X : ℕ in atTop,
      weightedTermNat A X ≤ nuLambdaMeanTerm A X + e X := by
    filter_upwards [eventually_log_log_natCast_pos] with X hX
    exact weightedTermNat_le_nuLambdaMeanTerm_add A hX
  calc
    weightedRateNat A = limsup (weightedTermNat A) atTop := rfl
    _ ≤ limsup (fun X ↦ nuLambdaMeanTerm A X + e X) atTop :=
      limsup_le_limsup hle
    _ = limsup (nuLambdaMeanTerm A) atTop := by
      have he : Tendsto e atTop (nhds 0) := by
        simpa only [e] using tendsto_discrepancyTerm_zero
      exact ENNReal.limsup_add_of_right_tendsto_zero he _

private lemma lintegral_visitedTermNat_eq_nuLambdaMeanTerm
    {μ : Measure (ℕ → ℕ)} (A : Set ℕ) {X : ℕ}
    (hX : 0 < Real.log (Real.log (X : ℝ)))
    (hhit : ∀ n, μ (hitEvent n) = ENNReal.ofReal (nuLambda n)) :
    (∫⁻ ω, visitedTermNat A X ω ∂μ) = nuLambdaMeanTerm A X := by
  rw [lintegral_visitedTermNat A hX _ hhit]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [← ENNReal.ofReal_div_of_pos hX]
    rfl
  · intro n hn
    exact nuLambda_nonneg n

private theorem weightedRateNat_le_limsup_lintegral_visitedTermNat
    {μ : Measure (ℕ → ℕ)} (A : Set ℕ)
    (hhit : ∀ n, μ (hitEvent n) = ENNReal.ofReal (nuLambda n)) :
    weightedRateNat A ≤
      limsup (fun X ↦ ∫⁻ ω, visitedTermNat A X ω ∂μ) atTop := by
  refine (weightedRateNat_le_limsup_nuLambdaMeanTerm A).trans_eq ?_
  apply limsup_congr
  filter_upwards [eventually_log_log_natCast_pos] with X hX
  exact (lintegral_visitedTermNat_eq_nuLambdaMeanTerm A hX hhit).symm

/-! ## A uniform normalized second moment -/

private lemma invMulLog_antitoneOn {N : ℕ} :
    AntitoneOn (fun x : ℝ ↦ 1 / (x * Real.log x)) (Set.Icc 2 N) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := by linarith [hx.1]
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
  have hypos : 0 < y := hxpos.trans_le hxy
  have hlogle : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
  apply one_div_le_one_div_of_le (mul_pos hxpos hlogx)
  exact mul_le_mul hxy hlogle hlogx.le hypos.le

private lemma integral_invMulLog {N : ℕ} (hN : 2 ≤ N) :
    ∫ x in (2 : ℝ)..N, 1 / (x * Real.log x) =
      Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) := by
  apply intervalIntegral.integral_deriv_eq_sub'
      (fun x : ℝ ↦ Real.log (Real.log x))
  · funext x
    rw [Real.deriv_log_log_apply]
    ring
  · intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast hN)] at hx
    exact Real.differentiableAt_log_log (by linarith [hx.1])
      (by linarith [hx.1]) (by linarith [hx.1])
  · intro x hx
    rw [Set.uIcc_of_le (by exact_mod_cast hN)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hlog : Real.log x ≠ 0 :=
      ne_of_gt (Real.log_pos (by linarith [hx.1]))
    exact ContinuousAt.continuousWithinAt <|
      continuousAt_const.div (continuousAt_id.mul (Real.continuousAt_log hx0))
        (mul_ne_zero hx0 hlog)

private lemma sum_doublyHarmonicWeight_le (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.Ico 2 N, doublyHarmonicWeight n ≤
      doublyHarmonicWeight 2 +
        Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) := by
  by_cases hN2 : N = 2
  · subst N
    simp [doublyHarmonicWeight_nonneg]
  · have hN3 : 3 ≤ N := by omega
    have hsub : 2 ≤ N - 1 := by omega
    have htail := (invMulLog_antitoneOn (N := N - 1)).sum_le_integral_Ico hsub
    norm_num only [Nat.cast_ofNat] at htail
    rw [integral_invMulLog hsub] at htail
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 2 < N)]
    rw [doublyHarmonicWeight_of_two_le (by omega)]
    have htail' :
        (∑ n ∈ Finset.Ico 3 N, 1 / ((n : ℝ) * Real.log n)) ≤
          Real.log (Real.log (N : ℝ)) - Real.log (Real.log 2) := by
      have hsumEq :
          (∑ n ∈ Finset.Ico 3 N, 1 / ((n : ℝ) * Real.log n)) =
            ∑ n ∈ Finset.Ico 2 (N - 1),
              1 / (((n + 1 : ℕ) : ℝ) * Real.log (n + 1 : ℕ)) := by
        symm
        refine Finset.sum_bij (fun n _ ↦ n + 1) ?_ ?_ ?_ ?_
        · intro n hn
          simp only [Finset.mem_Ico] at hn ⊢
          omega
        · intro a ha b hb hab
          omega
        · intro b hb
          refine ⟨b - 1, ?_, ?_⟩
          · simp only [Finset.mem_Ico] at hb ⊢
            omega
          · exact Nat.sub_add_cancel (by
              simp only [Finset.mem_Ico] at hb
              omega)
        · intro n hn
          push_cast
          rfl
      rw [hsumEq]
      refine htail.trans ?_
      apply sub_le_sub_right
      apply Real.log_le_log
      · exact Real.log_pos (by exact_mod_cast hsub)
      · apply Real.log_le_log
        · positivity
        · exact_mod_cast Nat.sub_le N 1
    calc
      _ = 1 / ((2 : ℝ) * Real.log 2) +
          ∑ n ∈ Finset.Ico 3 N, 1 / ((n : ℝ) * Real.log n) := by
        norm_num only [Nat.cast_ofNat]
        simp only [one_div]
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        rw [doublyHarmonicWeight_of_two_le (by
          simp only [Finset.mem_Ico] at hn
          omega)]
      _ ≤ _ := by
        norm_num only [Nat.cast_ofNat]
        simp only [one_div]
        simp only [one_div] at htail'
        linarith only [htail']

private lemma omegaHitMoment_nuLambda_le (A : Set ℕ) (X : ℕ) :
    omegaHitMoment A X (fun n ↦ ENNReal.ofReal (nuLambda n)) ≤
      1 + 3 * ENNReal.ofReal (OmegaBound.omegaLogSum X) := by
  let S := (positiveBelowNat X).filter (fun n ↦ n ∈ A)
  have hpoint (n : ℕ) (hn : n ∈ S) :
      ((2 * Ω n + 1 : ℕ) : ENNReal) * ENNReal.ofReal (nuLambda n) ≤
        (if n = 1 then 1 else
          3 * ENNReal.ofReal (OmegaBound.omegaLogKernel n)) := by
    have hnpos : 1 ≤ n :=
      (mem_positiveBelowNat_iff.mp (Finset.mem_filter.mp hn).1).1
    by_cases hn1 : n = 1
    · subst n
      simp [nuLambda_one]
    · have hn2 : 2 ≤ n := by omega
      rw [if_neg hn1]
      have hOmega : 1 ≤ Ω n :=
        ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
      have hnu : ENNReal.ofReal (nuLambda n) ≤
          ENNReal.ofReal (doublyHarmonicWeight n) :=
        ENNReal.ofReal_le_ofReal (nuLambda_le_doublyHarmonicWeight hn2)
      calc
        ((2 * Ω n + 1 : ℕ) : ENNReal) * ENNReal.ofReal (nuLambda n) ≤
            ((3 * Ω n : ℕ) : ENNReal) *
              ENNReal.ofReal (doublyHarmonicWeight n) := by
          exact mul_le_mul
            (by exact_mod_cast (show 2 * Ω n + 1 ≤ 3 * Ω n by omega))
            hnu bot_le bot_le
        _ = 3 * ENNReal.ofReal (OmegaBound.omegaLogKernel n) := by
          rw [OmegaBound.omegaLogKernel,
            doublyHarmonicWeight_of_two_le hn2]
          rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (Ω n : ℝ))]
          norm_num
          ring
  calc
    omegaHitMoment A X (fun n ↦ ENNReal.ofReal (nuLambda n)) =
        ∑ n ∈ S, ((2 * Ω n + 1 : ℕ) : ENNReal) *
          ENNReal.ofReal (nuLambda n) := rfl
    _ ≤ ∑ n ∈ S, (if n = 1 then 1 else
          3 * ENNReal.ofReal (OmegaBound.omegaLogKernel n)) :=
      Finset.sum_le_sum hpoint
    _ ≤ ∑ n ∈ positiveBelowNat X, (if n = 1 then 1 else
          3 * ENNReal.ofReal (OmegaBound.omegaLogKernel n)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro n hn hnot
        split_ifs <;> positivity
    _ ≤ 1 + 3 * ENNReal.ofReal (OmegaBound.omegaLogSum X) := by
      rw [positiveBelowNat]
      by_cases hX : X ≤ 1
      · have : X = 0 ∨ X = 1 := by omega
        rcases this with rfl | rfl <;> simp [OmegaBound.omegaLogSum]
      · apply le_of_eq
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < X)]
        simp only [if_pos]
        rw [show (∑ n ∈ Finset.Ico 2 X,
            (if n = 1 then 1 else
              3 * ENNReal.ofReal (OmegaBound.omegaLogKernel n))) =
              ∑ n ∈ Finset.Ico 2 X,
                3 * ENNReal.ofReal (OmegaBound.omegaLogKernel n) by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [Finset.mem_Ico] at hn
          simp [show n ≠ 1 by omega]]
        rw [← Finset.mul_sum]
        congr 1
        rw [OmegaBound.omegaLogSum,
          ENNReal.ofReal_sum_of_nonneg (fun n _ ↦
            OmegaBound.omegaLogKernel_nonneg' n)]

private lemma exists_eventual_secondMoment_bound
    {μ : Measure (ℕ → ℕ)} (A : Set ℕ)
    (hhit : ∀ n, μ (hitEvent n) = ENNReal.ofReal (nuLambda n))
    (hpath : ∀ᵐ ω ∂μ, IsStrictDivisibilityPath ω) :
    ∃ N₀ : ℕ, ∃ M : ENNReal, M ≠ ∞ ∧ ∀ X, N₀ ≤ X →
      ∫⁻ ω, (visitedTermNat A X ω) ^ 2 ∂μ ≤ M := by
  obtain ⟨C, hC, N₂, hOmega⟩ :=
    OmegaBound.exists_omegaLogSum_le_log_log_sq
  have hLL : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    tendsto_log_log_natCast_atTop
  have hev : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (Real.log (X : ℝ)) :=
    hLL.eventually (eventually_ge_atTop 1)
  rw [eventually_atTop] at hev
  obtain ⟨N₁, hN₁⟩ := hev
  let M : ENNReal := 1 + 3 * ENNReal.ofReal C
  refine ⟨max N₁ N₂, M, ?_, ?_⟩
  · dsimp [M]
    finiteness
  · intro X hX
    have hXN₁ : N₁ ≤ X := (le_max_left N₁ N₂).trans hX
    have hXN₂ : N₂ ≤ X := (le_max_right N₁ N₂).trans hX
    let L : ℝ := Real.log (Real.log (X : ℝ))
    have hL : 1 ≤ L := hN₁ X hXN₁
    have hLpos : 0 < L := zero_lt_one.trans_le hL
    let l : ENNReal := ENNReal.ofReal L
    have hl1 : 1 ≤ l := by simpa [l, ENNReal.one_le_ofReal] using hL
    have hl0 : l ≠ 0 := ne_of_gt (zero_lt_one.trans_le hl1)
    have hltop : l ≠ ∞ := by simp [l]
    have hOmegaReal : OmegaBound.omegaLogSum X ≤ C * L ^ 2 := by
      simpa only [L] using hOmega X hXN₂
    have hOmegaENN : ENNReal.ofReal (OmegaBound.omegaLogSum X) ≤
        ENNReal.ofReal C * l ^ 2 := by
      refine (ENNReal.ofReal_le_ofReal hOmegaReal).trans_eq ?_
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hLpos.le]
    have hnum : 1 + 3 * ENNReal.ofReal (OmegaBound.omegaLogSum X) ≤
        M * l ^ 2 := by
      calc
        _ ≤ 1 + 3 * (ENNReal.ofReal C * l ^ 2) := by gcongr
        _ ≤ l ^ 2 + 3 * (ENNReal.ofReal C * l ^ 2) := by
          gcongr
          exact one_le_pow₀ hl1
        _ = M * l ^ 2 := by
          dsimp [M]
          ring
    calc
      (∫⁻ ω, (visitedTermNat A X ω) ^ 2 ∂μ) ≤
          omegaHitMoment A X (fun n ↦ ENNReal.ofReal (nuLambda n)) /
            (ENNReal.ofReal L) ^ 2 :=
        lintegral_visitedTermNat_sq_le A hLpos _ hhit hpath
      _ ≤ (1 + 3 * ENNReal.ofReal (OmegaBound.omegaLogSum X)) / l ^ 2 := by
        simpa only [l] using
          ENNReal.div_le_div_right (omegaHitMoment_nuLambda_le A X) _
      _ ≤ (M * l ^ 2) / l ^ 2 := ENNReal.div_le_div_right hnum _
      _ = M := by
        rw [ENNReal.mul_div_cancel_right]
        · exact pow_ne_zero _ hl0
        · exact ENNReal.pow_ne_top hltop

/-! ## Deterministic passage from a selected path to its chain -/

lemma visitedBelow_eq_filter_range_inter (A : Set ℕ) (X : ℕ) (ω : ℕ → ℕ) :
    visitedBelow A X ω =
      (positiveBelowNat X).filter (fun n ↦ n ∈ Set.range ω ∩ A) := by
  ext n
  simp only [mem_visitedBelow_iff, Finset.mem_filter, mem_positiveBelowNat_iff,
    Set.mem_inter_iff, Set.mem_range, hitEvent, Set.mem_ofPred_eq]
  aesop

lemma visitedCount_eq_chainCountNat_of_range
    {A : Set ℕ} {X : ℕ} {ω d : ℕ → ℕ}
    (hrange : Set.range d = Set.range ω ∩ A) :
    visitedCount A X ω = chainCountNat d X := by
  rw [visitedCount, visitedBelow_eq_filter_range_inter, chainCountNat]
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter]
  rw [hrange]

lemma visitedTermNat_eq_chainTermNat_of_range
    {A : Set ℕ} {X : ℕ} {ω d : ℕ → ℕ}
    (hrange : Set.range d = Set.range ω ∩ A) :
    visitedTermNat A X ω = chainTermNat d X := by
  rw [visitedTermNat, chainTermNat, visitedCount_eq_chainCountNat_of_range hrange]

lemma limsup_visitedTermNat_eq_chainRateNat_of_range
    {A : Set ℕ} {ω d : ℕ → ℕ}
    (hrange : Set.range d = Set.range ω ∩ A) :
    limsup (fun X ↦ visitedTermNat A X ω) atTop = chainRateNat d := by
  unfold chainRateNat
  congr 1
  funext X
  exact visitedTermNat_eq_chainTermNat_of_range hrange

lemma UpwardChain.Data.IsGoodPath.isStrictDivisibilityPath
    {ω : ℕ → ℕ} (hω : UpwardChain.Data.IsGoodPath ω) :
    IsStrictDivisibilityPath ω := by
  have hpos : ∀ k, 0 < ω k := by
    intro k
    induction k with
    | zero => rw [hω.1]; exact Nat.zero_lt_one
    | succ k ih => exact ih.trans (hω.2 k).1
  exact ⟨hpos, fun k ↦ ⟨(hω.2 k).2, (hω.2 k).1⟩⟩

lemma UpwardChain.Data.pathMeasure_ae_strictDivisibilityPath
    (D : UpwardChain.Data) :
    ∀ᵐ ω ∂D.pathMeasure, IsStrictDivisibilityPath ω :=
  D.pathMeasure_ae_good.mono fun _ hω ↦ hω.isStrictDivisibilityPath

private lemma nuLambdaData_pathMeasure_hit (n : ℕ) :
    nuLambdaData.pathMeasure (hitEvent n) = ENNReal.ofReal (nuLambda n) := by
  rcases n with _ | n
  · change nuLambdaData.pathMeasure (UpwardChain.Data.hitEvent 0) =
      ENNReal.ofReal (nuLambda 0)
    rw [nuLambdaData.pathMeasure_hitEvent, nuLambdaData.hitMass_zero]
    simp
  · change nuLambdaData.pathMeasure (UpwardChain.Data.hitEvent (n + 1)) =
      ENNReal.ofReal (nuLambda (n + 1))
    simpa only [nuLambdaData] using
      (nuLambdaData.pathMeasure_hitEvent_eq_ofReal_nu
        (show 1 ≤ n + 1 by omega))

/-! ## The strong set-valued resolution -/

/-- Positive doubly-harmonic upper rate produces an increasing divisibility
chain in the set with at least the same rate.  This is the strengthened form
of the affirmative resolution of Erdős Problem 1217. -/
theorem exists_divisibility_chain_of_weightedRate_pos
    {A : Set ℕ} (hA : 0 < weightedRate A) :
    ∃ d : ℕ → ℕ, StrictMono d ∧
      (∀ i, d i ∈ A) ∧
      (∀ i, d i ∣ d (i + 1)) ∧
      weightedRate A ≤ chainRate d := by
  let D : UpwardChain.Data := nuLambdaData
  have hhit : ∀ n, D.pathMeasure (hitEvent n) =
      ENNReal.ofReal (nuLambda n) := by
    intro n
    simpa only [D] using nuLambdaData_pathMeasure_hit n
  have hpath : ∀ᵐ ω ∂D.pathMeasure, IsStrictDivisibilityPath ω :=
    D.pathMeasure_ae_strictDivisibilityPath
  obtain ⟨N₀, M, hM, hsecond⟩ :=
    exists_eventual_secondMoment_bound A hhit hpath
  have hmean : weightedRateNat A ≤
      limsup (fun X ↦ ∫⁻ ω, visitedTermNat A X ω ∂D.pathMeasure) atTop :=
    weightedRateNat_le_limsup_lintegral_visitedTermNat A hhit
  have hposNat : 0 < weightedRateNat A := by
    rwa [weightedRate_eq_weightedRateNat A] at hA
  let Nbad : Set (ℕ → ℕ) := {ω | ¬ IsStrictDivisibilityPath ω}
  have hNbad : D.pathMeasure Nbad = 0 := by
    have hgood : {ω | IsStrictDivisibilityPath ω} ∈ ae D.pathMeasure := hpath
    rw [mem_ae_iff] at hgood
    simpa only [Nbad, Set.compl_ofPred, not_not] using hgood
  obtain ⟨ω, hωbad, hωrate, hωinf⟩ :=
    exists_infinite_path_with_limsup_visitedTermNat_ge_of_eventually_secondMoment
      A N₀ hM hsecond hmean hposNat hNbad
  have hω : IsStrictDivisibilityPath ω := by
    simpa only [Nbad, Set.mem_ofPred_eq, not_not] using hωbad
  have hinf : (hitTimes A ω).Infinite :=
    hitTimes_infinite_of_range_inter hωinf
  let d : ℕ → ℕ := fun i ↦ ω (hitIndex A ω i)
  have hrange : Set.range d = Set.range ω ∩ A := by
    simpa only [d] using range_hitSubsequence hinf
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · exact hitSubsequence_strictMono hinf hω.strictMono
  · intro i
    exact hitSubsequence_mem hinf i
  · intro i
    exact hitSubsequence_step_dvd hinf (fun j ↦ (hω.2 j).1) i
  · calc
      weightedRate A = weightedRateNat A := weightedRate_eq_weightedRateNat A
      _ ≤ limsup (fun X ↦ visitedTermNat A X ω) atTop := hωrate
      _ = chainRateNat d :=
        limsup_visitedTermNat_eq_chainRateNat_of_range hrange
      _ = chainRate d := (chainRate_eq_chainRateNat d).symm

end Erdos1217
