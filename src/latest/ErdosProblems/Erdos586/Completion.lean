/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.InitialStages
import ErdosProblems.Erdos586.ClassMassInvariant
import ErdosProblems.Erdos586.MomentInstantiation
import ErdosProblems.Erdos586.EventPartition
import ErdosProblems.Erdos586.TailBridge

/-!
# Completion of the distorted sieve for Erdős Problem 586

This file makes the final, concrete specialization of the BBMST sieve.  The
small guarded variant of `stageF` below is used only to organize the joint
positivity induction: it agrees with `stageF` whenever the remaining budget
is positive, and is negative otherwise.  Thus nonnegativity of the guarded
quantity records, without any circular hypothesis, exactly the survival fact
needed by the next stage.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Positivity and normalization identities -/

lemma stageGrowthFactor_pos {r : ℕ} (hr : 4 ≤ r) :
    0 < stageGrowthFactor r := by
  have hp : 1 < stagePrime r := stagePrime_one_lt (by omega)
  have hdelta : 0 < 1 - distortionDelta r := by
    have := distortionDelta_le_half r
    linarith
  unfold stageGrowthFactor
  have hden : 0 < (1 - distortionDelta r) *
      (((stagePrime r - 1 : ℕ) : ℝ) ^ 2) := by
    apply mul_pos hdelta
    exact sq_pos_of_pos (by exact_mod_cast Nat.sub_pos_of_lt hp)
  have hnum : 0 ≤ (((3 * stagePrime r - 1 : ℕ) : ℝ)) := by positivity
  have : 0 ≤ (((3 * stagePrime r - 1 : ℕ) : ℝ)) /
      ((1 - distortionDelta r) *
        (((stagePrime r - 1 : ℕ) : ℝ) ^ 2)) := div_nonneg hnum hden.le
  linarith

lemma stageGrowthProduct_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < stageGrowthProduct 3 n := by
  unfold stageGrowthProduct
  apply Finset.prod_pos
  intro r hr
  exact stageGrowthFactor_pos (by
    have := (Finset.mem_Ioc.mp hr).1
    omega)

lemma stageF_pos_of_survival_pos
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q n : ℕ) (hQ : Q ≠ 0) (hn : 3 ≤ n)
    (hsurv : 0 < stageSurvival A s Q n hQ) :
    0 < stageF fiveSmoothKappa A s Q 3 n hQ := by
  unfold stageF
  exact mul_pos (div_pos (by norm_num [fiveSmoothKappa]) hsurv)
    (stageGrowthProduct_pos hn)

/-- A total normalized sequence whose nonnegativity certifies positive
survival.  On the positive-survival branch it is the genuine BBMST
normalized quantity. -/
def guardedStageF (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q n : ℕ) (hQ : Q ≠ 0) : ℝ :=
  if 0 < stageSurvival A s Q n hQ then
    stageF fiveSmoothKappa A s Q 3 n hQ
  else -1

lemma guardedStageF_eq_of_survival_pos
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q n : ℕ) (hQ : Q ≠ 0)
    (hsurv : 0 < stageSurvival A s Q n hQ) :
    guardedStageF A s Q n hQ =
      stageF fiveSmoothKappa A s Q 3 n hQ := by
  simp [guardedStageF, hsurv]

lemma survival_pos_of_guardedStageF_nonneg
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q n : ℕ) (hQ : Q ≠ 0)
    (hf : 0 ≤ guardedStageF A s Q n hQ) :
    0 < stageSurvival A s Q n hQ := by
  by_contra hsurv
  have : guardedStageF A s Q n hQ = -1 := by
    simp [guardedStageF, hsurv]
  linarith

lemma guardedStageF_pos_of_survival_pos
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q n : ℕ) (hQ : Q ≠ 0) (hn : 3 ≤ n)
    (hsurv : 0 < stageSurvival A s Q n hQ) :
    0 < guardedStageF A s Q n hQ := by
  rw [guardedStageF_eq_of_survival_pos A s Q n hQ hsurv]
  exact stageF_pos_of_survival_pos A s Q n hQ hn hsurv

lemma stageGrowthFactor_eq_sieveFactor {r : ℕ} (hr : 4 ≤ r) :
    stageGrowthFactor r = sieveFactor (stagePrime r) (1 / 5) := by
  have hp : 1 ≤ stagePrime r := (stagePrime_one_lt (by omega)).le
  have hthree : 1 ≤ 3 * stagePrime r := by omega
  unfold stageGrowthFactor sieveFactor stageA
  rw [distortionDelta_of_three_lt (by omega : 3 < r)]
  push_cast [hp, hthree]
  have hpne : (stagePrime r : ℝ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (by
      exact_mod_cast (stagePrime_one_lt (by omega : 0 < r)).ne')
  field_simp [hpne]

lemma stageGrowthFactor_eq_secondMomentEulerFactor {r : ℕ} (hr : 4 ≤ r) :
    stageGrowthFactor r =
      secondMomentEulerFactor (stagePrime r) (distortionDelta r) := by
  have hp : 1 ≤ stagePrime r := (stagePrime_one_lt (by omega)).le
  have hthree : 1 ≤ 3 * stagePrime r := by omega
  unfold stageGrowthFactor secondMomentEulerFactor
  push_cast [hp, hthree]
  rfl

lemma stageGrowthProduct_eq_refined_product {r : ℕ} (hr : 4 ≤ r) :
    stageGrowthProduct 3 (r - 1) =
      ∏ t ∈ Finset.Ico 4 r,
        secondMomentEulerFactor (stagePrime t) (distortionDelta t) := by
  unfold stageGrowthProduct
  have hsets : Finset.Ioc 3 (r - 1) = Finset.Ico 4 r := by
    ext t
    simp
    omega
  rw [hsets]
  apply Finset.prod_congr rfl
  intro t ht
  exact stageGrowthFactor_eq_secondMomentEulerFactor
    (Finset.mem_Ico.mp ht).1

lemma refinedSecondMomentBound_eq_stageF
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) (hr : 4 ≤ r)
    (hsurv : 0 < stageSurvival A s Q (r - 1) hQ) :
    refinedSecondMomentBound fiveSmoothKappa (stagePrime r)
        (Finset.Ico 4 r) (fun t ↦ (stagePrime t : ℝ)) distortionDelta =
      stageSurvival A s Q (r - 1) hQ *
          stageF fiveSmoothKappa A s Q 3 (r - 1) hQ /
        ((stagePrime r : ℝ) - 1) ^ 2 := by
  rw [refinedSecondMomentBound, ← stageGrowthProduct_eq_refined_product hr]
  unfold stageF
  have hne : stageSurvival A s Q (r - 1) hQ ≠ 0 := hsurv.ne'
  have hpne : (stagePrime r : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by
      exact_mod_cast stagePrime_one_lt (by omega : 0 < r)))
  field_simp [hne, hpne]

lemma stageF_balance
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) (hr : 4 ≤ r)
    (hprev : 0 < stageSurvival A s Q (r - 1) hQ)
    (hnext : 0 < stageSurvival A s Q r hQ) :
    stageF fiveSmoothKappa A s Q 3 r hQ *
        stageSurvival A s Q r hQ =
      stageF fiveSmoothKappa A s Q 3 (r - 1) hQ *
        stageSurvival A s Q (r - 1) hQ *
          sieveFactor (stagePrime r) (1 / 5) := by
  have hpred : (r - 1) + 1 = r := by omega
  have hgrowth := stageGrowthProduct_succ
    (r₀ := 3) (n := r - 1) (by omega)
  rw [hpred, stageGrowthFactor_eq_sieveFactor hr] at hgrowth
  unfold stageF
  rw [hgrowth]
  field_simp [hprev.ne', hnext.ne']

/-! ## The concrete recurrence step -/

/-- Every post-initial prime stage satisfies the guarded normalized
recurrence.  The processed-class invariant supplies the probability input,
and the smooth/rough theorem supplies the complete second-moment bound. -/
theorem guardedStageF_step
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (Q r : ℕ) (hQ : Q ≠ 0) (hr : 4 ≤ r)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus)
    (hfprev : 0 ≤ guardedStageF A s Q (r - 1) hQ)
    (hvalid : lossRatio (stagePrime r) (1 / 5)
      (guardedStageF A s Q (r - 1) hQ) < 1) :
    0 ≤ guardedStageF A s Q r hQ ∧
      guardedStageF A s Q r hQ ≤
        recurrenceMap (stagePrime r) (1 / 5)
          (guardedStageF A s Q (r - 1) hQ) := by
  let muPrev := stageSurvival A s Q (r - 1) hQ
  let muNext := stageSurvival A s Q r hQ
  let fPrev := guardedStageF A s Q (r - 1) hQ
  let fNext := guardedStageF A s Q r hQ
  letI : NeZero (partialPeriod Q (r - 1)) :=
    ⟨(partialPeriod_pos Q (r - 1)).ne'⟩
  letI : NeZero (stagePrime r ^ stageExponent Q r) :=
    ⟨pow_ne_zero _ (stagePrime_pos (by omega)).ne'⟩
  let M2 := secondMoment (stageDistribution A s Q hQ (r - 1))
    (momentStageBadSet A s Q r hQ)
  have hpred : (r - 1) + 1 = r := by omega
  have hmuPrev : 0 < muPrev := by
    exact survival_pos_of_guardedStageF_nonneg A s Q (r - 1) hQ hfprev
  have hfPrevEq : fPrev =
      stageF fiveSmoothKappa A s Q 3 (r - 1) hQ := by
    exact guardedStageF_eq_of_survival_pos A s Q (r - 1) hQ hmuPrev
  have hfPrevPos : 0 < fPrev := by
    rw [hfPrevEq]
    exact stageF_pos_of_survival_pos A s Q (r - 1) hQ (by omega) hmuPrev
  have hclass : HasProcessedClassMassBound
      (Q := Q) (r := r)
      (stageDistribution A s Q hQ (r - 1)) distortionDelta := by
    convert (stageDistribution_hasProcessedClassMassBound A s Q (r - 1) hQ) using 1 <;>
      omega
  have hM2refined : M2 ≤
      refinedSecondMomentBound fiveSmoothKappa (stagePrime r)
        (Finset.Ico 4 r) (fun t ↦ (stagePrime t : ℝ)) distortionDelta := by
    exact momentStage_secondMoment_le_refined A s hQ hr hanti
      distortionDelta distortionDelta_le_half
      (by simp [distortionDelta]) (by simp [distortionDelta])
      (by simp [distortionDelta]) _ hclass
  have hmoment : M2 ≤
      muPrev * fPrev / ((stagePrime r : ℝ) - 1) ^ 2 := by
    calc
      M2 ≤ refinedSecondMomentBound fiveSmoothKappa (stagePrime r)
          (Finset.Ico 4 r) (fun t ↦ (stagePrime t : ℝ)) distortionDelta := hM2refined
      _ = muPrev *
          stageF fiveSmoothKappa A s Q 3 (r - 1) hQ /
            ((stagePrime r : ℝ) - 1) ^ 2 :=
        refinedSecondMomentBound_eq_stageF A s Q r hQ hr hmuPrev
      _ = muPrev * fPrev / ((stagePrime r : ℝ) - 1) ^ 2 := by
        rw [hfPrevEq]
  have hevent : stageBadEvent A s Q (r - 1) hQ =
      momentStageBadSet A s Q r hQ := by
    have h := stageBadEvent_eq_momentStageBadSet A s Q (r - 1) hQ
    exact hpred ▸ h
  have hcost : stageCost A s Q (r - 1) hQ ≤
      M2 / (4 * (1 / 5) * (1 - (1 / 5))) := by
    have hc := stageCost_le_moments A s Q (r - 1) hQ (by omega)
    have hc2 := hc.trans (min_le_right _ _)
    have hdelta : distortionDelta (r - 1 + 1) = 1 / 5 := by
      rw [hpred]
      exact distortionDelta_of_three_lt (by omega : 3 < r)
    rw [hdelta, hevent] at hc2
    change stageCost A s Q (r - 1) hQ ≤
      secondMoment (stageDistribution A s Q hQ (r - 1))
        (momentStageBadSet A s Q r hQ) /
          (4 * (1 / 5) * (1 - (1 / 5)))
    exact hc2
  have hsurvivalStep : muNext =
      muPrev - stageCost A s Q (r - 1) hQ := by
    simpa [muPrev, muNext, hpred] using
      (stageSurvival_succ A s Q (r - 1) hQ)
  have hstageCost : muPrev - muNext ≤
      M2 / (4 * (1 / 5) * (1 - (1 / 5))) := by
    linarith [hcost, hsurvivalStep]
  have hp : (1 : ℝ) < stagePrime r := by
    exact_mod_cast stagePrime_one_lt (by omega : 0 < r)
  have hmuNext : 0 < muNext :=
    nextRemaining_pos_of_secondMoment hp (by norm_num) (by norm_num)
      hmuPrev hfPrevPos.le hvalid hstageCost hmoment
  have hfNextEq : fNext =
      stageF fiveSmoothKappa A s Q 3 r hQ :=
    guardedStageF_eq_of_survival_pos A s Q r hQ hmuNext
  have hbalance : fNext * muNext =
      fPrev * muPrev * sieveFactor (stagePrime r) (1 / 5) := by
    rw [hfNextEq, hfPrevEq]
    exact stageF_balance A s Q r hQ hr hmuPrev hmuNext
  have hstep := oneStep_of_secondMoment hp (by norm_num) (by norm_num)
    hmuPrev hfPrevPos.le hvalid hstageCost hmoment hbalance
  refine ⟨?_, hstep.2⟩
  exact (guardedStageF_pos_of_survival_pos A s Q r hQ (by omega) hmuNext).le

/-! ## Completion -/

/-- A minimal covering subfamily cannot have pairwise divisibility-
incomparable moduli. -/
theorem no_minimal_antichain_cover
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hminimal : IsMinimalCover A s)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) : False := by
  let Q := commonPeriod A
  let hQ : Q ≠ 0 := (commonPeriod_pos A).ne'
  let f : ℕ → ℝ := fun r ↦ guardedStageF A s Q r hQ
  have hnpp : ∀ i ∈ s, ¬ IsPrimePow (A.get i).modulus :=
    no_prime_power_modulus_of_minimal_antichain_cover A s hminimal hanti
  have hseed := stageF_three_le_fifty_one_twentieth
    A s Q hQ hminimal hanti
  have hf3eq : f 3 = stageF fiveSmoothKappa A s Q 3 3 hQ := by
    exact guardedStageF_eq_of_survival_pos A s Q 3 hQ hseed.1
  have hf3pos : 0 < f 3 := by
    rw [hf3eq]
    exact stageF_pos_of_survival_pos A s Q 3 hQ (by omega) hseed.1
  have hf3 : f 3 ≤ 51 / 20 := by
    rw [hf3eq]
    exact hseed.2
  have hfinite : ∀ r, 4 ≤ r → r ≤ 10000 →
      0 ≤ f (r - 1) →
      lossRatio (stagePrime r) (1 / 5) (f (r - 1)) < 1 →
        0 ≤ f r ∧
          f r ≤ recurrenceMap (stagePrime r) (1 / 5) (f (r - 1)) := by
    intro r hr hrtop hfprev hvalid
    exact guardedStageF_step A s Q r hQ hr hanti hfprev hvalid
  have htail : ∀ j < stageHorizon Q - 10000,
      0 ≤ f (10000 + j) →
      lossRatio (stagePrime (10000 + j + 1)) (1 / 5)
          (f (10000 + j)) < 1 →
        0 ≤ f (10000 + j + 1) ∧
          f (10000 + j + 1) ≤
            recurrenceMap (stagePrime (10000 + j + 1)) (1 / 5)
              (f (10000 + j)) := by
    intro j hj hfprev hvalid
    exact guardedStageF_step A s Q (10000 + j + 1) hQ (by omega)
      hanti (by simpa [f] using hfprev) (by simpa [f] using hvalid)
  have hsurvival := conditional_stage_recurrence_survival_to_horizon
    Q f hf3pos.le hf3 hfinite htail
  have hfHorizon : 0 ≤ f (stageHorizon Q) := by
    have hzero := hsurvival.2.2.1 (stageHorizon Q - 10000) le_rfl
    simpa [stageHorizon] using hzero
  have hpositive : 0 < stageSurvival A s Q (stageHorizon Q) hQ :=
    survival_pos_of_guardedStageF_nonneg A s Q (stageHorizon Q) hQ hfHorizon
  exact (positive_survival_at_horizon_not_coversIndices A s
    (by simpa [Q, hQ] using hpositive)) hminimal.1

end

end Erdos586
