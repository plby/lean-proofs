import ErdosProblems.Erdos888.SquarefreeBlocks
import ErdosProblems.Erdos888.CoreEstimate
import ErdosProblems.Erdos888.CoreFibers
import ErdosProblems.Erdos888.PrimeEstimates
import ErdosProblems.Erdos888.DyadicSums
import ErdosProblems.Erdos888.CoreBridgeBlocks
import ErdosProblems.Erdos888.CoreBridgePrime
import ErdosProblems.Erdos888.CoreBridgeDyadic
import ErdosProblems.Erdos888.CoreBridgeDecomp
import ErdosProblems.Erdos888.CoreBridgeReindex
import ErdosProblems.Erdos888.CoreBridgeScale
import ErdosProblems.Erdos888.BlockMajorant

/-!
# The linear core term in the squarefree block estimate

This file bridges the exact, set-dependent dyadic block cover to the
unconditional squarefree-core sum.  The summand is the linear term
`2 T(i,j) N(j)` in the coloured Kővári--Sós--Turán estimate.  Only the
canonical occupied blocks are summed; in particular every index pair
satisfies `i ≤ j`.
-/

open Filter Asymptotics
open scoped BigOperators

namespace Erdos888
namespace CoreBridge

noncomputable section

/-- The exact `2 T N` contribution over the canonical occupied blocks of
the squarefree block encoding. -/
def coreBlockSum (A : Finset ℕ) : ℝ :=
  ∑ ij ∈ occupiedBlockIndices A,
    2 * ((squarefreeBlockCoreSet A ij.1 ij.2).card : ℝ) *
      ((dyadicPrimeBlock ij.2).card : ℝ)

theorem coreBlockSum_nonneg (A : Finset ℕ) : 0 ≤ coreBlockSum A := by
  unfold coreBlockSum
  positivity

theorem coreBlockSum_eq_regrouping_source (A : Finset ℕ) (n : ℕ) :
    coreBlockSum A = CoreBridgeBlocks.coreBlockSum A n := rfl

theorem coreBlockSum_le_regroupedCoreSum {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) :
    coreBlockSum A ≤ CoreBridgeBlocks.regroupedCoreSum n := by
  rw [coreBlockSum_eq_regrouping_source A n]
  exact CoreBridgeBlocks.coreBlockSum_le_regroupedCoreSum hA

/-- The disjoint-union prime estimate collapses the right-block sum.  The
constant is uniform in the ambient parameter, the core, and both dyadic
indices. -/
theorem exists_forall_regroupedCoreSum_le_scaleWeightSum :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      CoreBridgeBlocks.regroupedCoreSum n ≤
        C * CoreBridgeScale.scaleWeightSum n := by
  obtain ⟨C, hCpos, hC⟩ :=
    CoreBridgePrime.exists_forall_sum_card_dyadicPrimeBlock_le_real_scale
  refine ⟨2 * C, mul_pos (by norm_num) hCpos, fun n ↦ ?_⟩
  unfold CoreBridgeBlocks.regroupedCoreSum
  calc
    (∑ i ∈ CoreBridgeBlocks.coreScaleIndexSet n,
        ∑ c ∈ CoreBridgeBlocks.coreScaleCoreSet n i,
          2 * ∑ j ∈ CoreBridgeBlocks.rightIndexSet n i c,
            ((dyadicPrimeBlock j).card : ℝ)) ≤
        ∑ i ∈ CoreBridgeBlocks.coreScaleIndexSet n,
          ∑ c ∈ CoreBridgeBlocks.coreScaleCoreSet n i,
            (2 * C) * CoreBridgeScale.scaleWeight n c i := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro c hc
      have hcData := CoreBridgeBlocks.mem_coreScaleCoreSet.mp hc
      have hcpos : 0 < c := by omega
      have hXpos : 0 < 2 ^ i := by positivity
      have hden : c * 2 ^ i ≤ n := by
        calc
          c * 2 ^ i ≤ c * 2 ^ (2 * i) := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ n := hcData.2.2.2.1
      have hquot : 1 ≤ n / (c * 2 ^ i) := by
        exact (Nat.le_div_iff_mul_le (Nat.mul_pos hcpos hXpos)).2
          (by simpa using hden)
      have hroom : ∀ j ∈ CoreBridgeBlocks.rightIndexSet n i c,
          c * 2 ^ i * 2 ^ j ≤ n := by
        intro j hj
        exact (CoreBridgeBlocks.mem_rightIndexSet.mp hj).2.2
      have hp := hC (CoreBridgeBlocks.rightIndexSet n i c) c (2 ^ i) n
        hcpos hXpos hquot hroom
      calc
        2 * ∑ j ∈ CoreBridgeBlocks.rightIndexSet n i c,
            ((dyadicPrimeBlock j).card : ℝ) ≤
            2 * (C * (((n : ℝ) / ((c : ℝ) * (2 ^ i : ℕ))) /
              lambda ((n : ℝ) / ((c : ℝ) * (2 ^ i : ℕ))))) := by
          gcongr
        _ = (2 * C) * CoreBridgeScale.scaleWeight n c i := by
          rw [CoreBridgeScale.scaleWeight, if_pos]
          · norm_num
            ring
          · exact ⟨hcData.2.2.1, hcData.2.2.2.1, hcData.2.2.2.2⟩
    _ = (2 * C) * CoreBridgeScale.scaleWeightSum n := by
      simp_rw [← Finset.mul_sum]
      congr 1
      rw [CoreBridgeScale.scaleWeightSum, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      unfold CoreBridgeBlocks.coreScaleCoreSet
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro c hc
      unfold CoreBridgeScale.scaleWeight
      split_ifs <;> rfl

/-- The set-independent triangular `2 T N` sum used by the final assembly is
exactly the same finite triple sum as `regroupedCoreSum`. -/
theorem universalCoreTerm_eq_regroupedCoreSum (n : ℕ) :
    universalCoreTerm n = CoreBridgeBlocks.regroupedCoreSum n := by
  rw [← CoreBridgeBlocks.scalePairCoreSum_eq_regroupedCoreSum]
  unfold universalCoreTerm triangularBlockIndices
  rw [Finset.sum_filter]
  unfold CoreBridgeBlocks.scalePairCoreSum
  apply Finset.sum_congr rfl
  intro ij hij
  have hi := (Finset.mem_product.mp hij).1
  have hj := (Finset.mem_product.mp hij).2
  change (if ij.1 ≤ ij.2 then
      2 * ((blockCoreCandidates n ij.1 ij.2).card : ℝ) *
        ((dyadicPrimeBlock ij.2).card : ℝ)
    else 0) =
      ∑ _c ∈ (CoreBridgeBlocks.coreScaleCoreSet n ij.1).filter
          (fun c ↦ ij.2 ∈ CoreBridgeBlocks.rightIndexSet n ij.1 c),
        2 * ((dyadicPrimeBlock ij.2).card : ℝ)
  by_cases hord : ij.1 ≤ ij.2
  · rw [if_pos hord]
    have hsets : blockCoreCandidates n ij.1 ij.2 =
        (CoreBridgeBlocks.coreScaleCoreSet n ij.1).filter
          (fun c ↦ ij.2 ∈ CoreBridgeBlocks.rightIndexSet n ij.1 c) := by
      ext c
      rw [mem_blockCoreCandidates, Finset.mem_filter,
        CoreBridgeBlocks.mem_coreScaleCoreSet,
        CoreBridgeBlocks.mem_rightIndexSet]
      have hi' : ij.1 < Nat.log 2 n + 1 := by
        simpa [CoreBridgeBlocks.coreScaleIndexSet] using hi
      have hj' : ij.2 < Nat.log 2 n + 1 := by
        simpa [CoreBridgeBlocks.coreScaleIndexSet] using hj
      constructor
      · rintro ⟨hc1, hcn, _hord, hsf, hsize, hsmooth⟩
        refine ⟨⟨hc1, hcn, hsf, ?_, hsmooth⟩, hj', hord, hsize⟩
        have hpow : 2 ^ ij.1 ≤ 2 ^ ij.2 :=
          Nat.pow_le_pow_right (by norm_num) hord
        calc
          c * 2 ^ (2 * ij.1) = c * 2 ^ ij.1 * 2 ^ ij.1 := by
            rw [show 2 * ij.1 = ij.1 + ij.1 by omega, pow_add, mul_assoc]
          _ ≤ c * 2 ^ ij.1 * 2 ^ ij.2 :=
            Nat.mul_le_mul_left (c * 2 ^ ij.1) hpow
          _ ≤ n := hsize
      · rintro ⟨⟨hc1, hcn, hsf, _hsquare, hsmooth⟩,
          _hj, _hord, hsize⟩
        exact ⟨hc1, hcn, hord, hsf, hsize, hsmooth⟩
    rw [← hsets]
    simp
    ring
  · rw [if_neg hord]
    have hempty : (CoreBridgeBlocks.coreScaleCoreSet n ij.1).filter
        (fun c ↦ ij.2 ∈ CoreBridgeBlocks.rightIndexSet n ij.1 c) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨c, hc⟩
      exact hord (CoreBridgeBlocks.mem_rightIndexSet.mp
        (Finset.mem_filter.mp hc).2).2.1
    rw [hempty]
    simp

/-- The scale of the unconditional core-pair estimate, before the harmless
extra `log log n` factor in the final comparison function. -/
def coreScale (n : ℕ) : ℝ := (n : ℝ) / lambda (n : ℝ)

theorem eventually_coreScale_nonneg :
    ∀ᶠ n : ℕ in atTop, 0 ≤ coreScale n := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact div_nonneg (by positivity)
    (lambda_pos (by exact_mod_cast hn)).le

/-- `n / lambda(n)` is smaller than the target comparison scale once
`log log n ≥ 1`. -/
theorem coreScale_isBigO_scale : coreScale =O[atTop] scale := by
  refine IsBigO.of_bound 2 ?_
  have hlog := (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hloglog := (Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  filter_upwards [hlog, hloglog, eventually_ge_atTop 1] with n hnlog hnloglog hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlam : 0 < lambda (n : ℝ) := lambda_pos (by exact_mod_cast hn)
  have hrealLog : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hnlog
  have hlam_ge : Real.log (n : ℝ) ≤ lambda (n : ℝ) := by
    rw [lambda_eq_one_add_log hnpos.ne']
    linarith
  have hcore : 0 ≤ coreScale n := div_nonneg hnpos.le hlam.le
  have hscale : 0 ≤ scale n := by
    rw [scale]
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hcore,
    abs_of_nonneg hscale]
  calc
    coreScale n = (n : ℝ) / lambda (n : ℝ) := rfl
    _ ≤ (n : ℝ) / Real.log (n : ℝ) :=
      div_le_div_of_nonneg_left hnpos.le hrealLog hlam_ge
    _ ≤ scale n := by
      rw [scale]
      have hnloglog0 : 0 ≤ Real.log (Real.log (n : ℝ)) :=
        zero_le_one.trans hnloglog
      calc
        (n : ℝ) / Real.log (n : ℝ) =
            ((n : ℝ) / Real.log (n : ℝ)) * 1 := by ring
        _ ≤ ((n : ℝ) / Real.log (n : ℝ)) *
            Real.log (Real.log (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hnloglog
            (div_nonneg hnpos.le hrealLog.le)
        _ = (n : ℝ) * Real.log (Real.log (n : ℝ)) /
            Real.log (n : ℝ) := by ring
    _ ≤ 2 * scale n := by linarith

/-- The analytic majorant after separating the core `c = 1` and writing
every nontrivial squarefree core as `c = d r`, with `r` its largest prime
factor.  The fixed constant `4` accommodates the factor-two dyadic endpoint
loss in `r < 2X`. -/
def corePairMajorant (n : ℕ) : ℝ :=
  coreScale n + (n : ℝ) * CoreEstimate.squarefreeCorePairSum 4 n

theorem corePairMajorant_isBigO_coreScale :
    corePairMajorant =O[atTop] coreScale := by
  have hpair := CoreFibers.squarefreeCorePairSum_isBigO 4 (by omega)
  have hmul' :
      (fun n : ℕ ↦ (n : ℝ) * CoreEstimate.squarefreeCorePairSum 4 n)
        =O[atTop] coreScale := by
    obtain ⟨C, hC⟩ := hpair.bound
    refine IsBigO.of_bound C ?_
    filter_upwards [hC] with n hn
    calc
      ‖(n : ℝ) * CoreEstimate.squarefreeCorePairSum 4 n‖ =
          ‖(n : ℝ)‖ * ‖CoreEstimate.squarefreeCorePairSum 4 n‖ :=
        norm_mul _ _
      _ ≤ ‖(n : ℝ)‖ *
          (C * ‖1 / CoreEstimate.logWeight (n : ℝ)‖) :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ = C * ‖coreScale n‖ := by
        simp only [coreScale, CoreEstimate.logWeight,
          div_eq_mul_inv, norm_mul, one_mul]
        ring
  exact (isBigO_refl coreScale atTop).add hmul'

theorem corePairMajorant_isBigO_scale :
    corePairMajorant =O[atTop] scale :=
  corePairMajorant_isBigO_coreScale.trans coreScale_isBigO_scale

theorem squarefreeCorePairSum_four_nonneg (n : ℕ) :
    0 ≤ CoreEstimate.squarefreeCorePairSum 4 n := by
  rw [← CoreBridgeReindex.sum_eligibleCorePairs_eq]
  exact Finset.sum_nonneg fun z hz ↦
    CoreBridgeReindex.corePairWeight_nonneg_of_mem hz

theorem coreScale_nonneg (n : ℕ) : 0 ≤ coreScale n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp [coreScale, lambda]
  · exact div_nonneg (by positivity)
      (lambda_pos (by exact_mod_cast hn)).le

theorem corePairMajorant_nonneg (n : ℕ) : 0 ≤ corePairMajorant n := by
  exact add_nonneg (coreScale_nonneg n)
    (mul_nonneg (by positivity) (squarefreeCorePairSum_four_nonneg n))

theorem scaleWeightSum_nonneg (n : ℕ) :
    0 ≤ CoreBridgeScale.scaleWeightSum n := by
  unfold CoreBridgeScale.scaleWeightSum
  exact Finset.sum_nonneg fun c hc ↦
    Finset.sum_nonneg fun i hi ↦ CoreBridgeScale.scaleWeight_nonneg

/-- The right-prime disjoint-union estimate, packaged as a Big-O relation. -/
theorem regroupedCoreSum_isBigO_scaleWeightSum :
    CoreBridgeBlocks.regroupedCoreSum =O[atTop]
      CoreBridgeScale.scaleWeightSum := by
  obtain ⟨C, hCpos, hC⟩ :=
    exists_forall_regroupedCoreSum_le_scaleWeightSum
  refine IsBigO.of_bound C (Eventually.of_forall fun n ↦ ?_)
  rw [Real.norm_of_nonneg (by
      unfold CoreBridgeBlocks.regroupedCoreSum
      positivity),
    Real.norm_of_nonneg (scaleWeightSum_nonneg n)]
  exact hC n

/-- The dyadic `X`-sum and largest-prime reindexing absorb the complete
scale-weight sum into the unconditional core-pair majorant. -/
theorem scaleWeightSum_isBigO_corePairMajorant :
    CoreBridgeScale.scaleWeightSum =O[atTop] corePairMajorant := by
  refine IsBigO.of_bound 8 ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hscale := CoreBridgeScale.scaleWeightSum_le hn
  have hreindex := CoreBridgeReindex.dyadicCoreSum_le n
  have hmul :
      4 * (n : ℝ) * CoreBridgeReindex.dyadicCoreSum n ≤
        8 * (n : ℝ) * CoreEstimate.squarefreeCorePairSum 4 n := by
    calc
      4 * (n : ℝ) * CoreBridgeReindex.dyadicCoreSum n ≤
          4 * (n : ℝ) *
            (2 * CoreEstimate.squarefreeCorePairSum 4 n) :=
        mul_le_mul_of_nonneg_left hreindex (by positivity)
      _ = 8 * (n : ℝ) * CoreEstimate.squarefreeCorePairSum 4 n := by ring
  have hpoint : CoreBridgeScale.scaleWeightSum n ≤
      8 * corePairMajorant n := by
    calc
      CoreBridgeScale.scaleWeightSum n ≤
          4 * coreScale n +
            4 * (n : ℝ) * CoreBridgeReindex.dyadicCoreSum n := by
        rw [coreScale]
        convert hscale using 1
        ring
      _ ≤ 4 * coreScale n +
          8 * (n : ℝ) * CoreEstimate.squarefreeCorePairSum 4 n :=
        add_le_add le_rfl hmul
      _ ≤ 8 * corePairMajorant n := by
        unfold corePairMajorant
        have hc := coreScale_nonneg n
        have hp : 0 ≤ (n : ℝ) * CoreEstimate.squarefreeCorePairSum 4 n :=
          mul_nonneg (Nat.cast_nonneg _)
          (squarefreeCorePairSum_four_nonneg n)
        nlinarith
  rw [Real.norm_of_nonneg (scaleWeightSum_nonneg n),
    Real.norm_of_nonneg (corePairMajorant_nonneg n)]
  exact hpoint

theorem regroupedCoreSum_isBigO_scale :
    CoreBridgeBlocks.regroupedCoreSum =O[atTop] scale :=
  regroupedCoreSum_isBigO_scaleWeightSum.trans
    (scaleWeightSum_isBigO_corePairMajorant.trans
      corePairMajorant_isBigO_scale)

/-- Unconditional analytic estimate for the exact universal `S₂` term
consumed by the upper-bound assembly. -/
theorem universalCoreTerm_isBigO_scale :
    universalCoreTerm =O[atTop] scale := by
  rw [show universalCoreTerm = CoreBridgeBlocks.regroupedCoreSum from
    funext universalCoreTerm_eq_regroupedCoreSum]
  exact regroupedCoreSum_isBigO_scale

end
end CoreBridge
end Erdos888
