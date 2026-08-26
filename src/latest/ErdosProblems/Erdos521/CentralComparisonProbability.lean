/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Summable disagreement probability for the actual central root count and the capped window sum.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.CentralComparisonCover
import ErdosProblems.Erdos521.BinCappedError
import ErdosProblems.Erdos521.EndpointAlmostSure

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators

theorem eventually_binComparisonException_probability :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop, ∀ k ∈ mainBinSet j,
      sequenceLaw.real (binComparisonException j k) ≤ C * (j : ℝ) ^ (-4 : ℝ) := by
  obtain ⟨C₀, hC₀, hlocal⟩ := eventually_bin_capped_disagreement
  let C := C₀ + fineGridSmallBallConstant
  refine ⟨C, add_pos hC₀ fineGridSmallBallConstant_pos, ?_⟩
  filter_upwards [hlocal, eventually_mainBin_zero_error_four] with j hj hz
  intro k hk
  have hroot := hj k hk
  have hzero := hz k hk (dyadicPoint k) ⟨le_rfl, dyadicPoint_mono (Nat.le_succ k)⟩
  have h : sequenceLaw.real (binComparisonException j k) ≤
      sequenceLaw.real {ε | intervalRootCount ε (2 ^ j) (dyadicPoint k) (dyadicPoint (k + 1)) ≠
        min (windowGridSignChanges ε (dyadicCoefficientWindow (2 ^ j) k (windowWidthScale j))
          (dyadicFineGrid j k) (fineGridLength j)) (windowCapScale j)} +
      sequenceLaw.real {ε | powerSum ε (2 ^ j + 1) (dyadicPoint k) = 0} := measureReal_union_le _ _
  dsimp only [C]
  linarith

theorem eventually_central_disagreement_probability :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
      sequenceLaw.real {ε | centralRootCount ε j ≠ centralCappedCount ε j} ≤ C * (j : ℝ) ^ (-3 : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ := eventually_binComparisonException_probability
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlocal, eventually_ge_atTop 9] with j hj hj₉
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hmono : sequenceLaw.real {ε | centralRootCount ε j ≠ centralCappedCount ε j} ≤
      sequenceLaw.real (⋃ k ∈ mainBinSet j, binComparisonException j k) :=
    ENNReal.toReal_mono (measure_ne_top sequenceLaw _) (measure_mono_ae (central_disagreement_ae_cover hj₉))
  have hsum := Finset.sum_le_sum hj
  have hsum' : (∑ k ∈ mainBinSet j, sequenceLaw.real (binComparisonException j k)) ≤
      ((mainBinSet j).card : ℝ) * (C * (j : ℝ) ^ (-4 : ℝ)) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
  have hpow : (j : ℝ) * (j : ℝ) ^ (-4 : ℝ) = (j : ℝ) ^ (-3 : ℝ) := by
    calc
      _ = (j : ℝ) ^ (1 : ℝ) * (j : ℝ) ^ (-4 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hjpos]; norm_num
  calc
    _ ≤ ∑ k ∈ mainBinSet j, sequenceLaw.real (binComparisonException j k) :=
      hmono.trans (measureReal_biUnion_finset_le _ _)
    _ ≤ ((mainBinSet j).card : ℝ) * (C * (j : ℝ) ^ (-4 : ℝ)) := hsum'
    _ ≤ (j : ℝ) * (C * (j : ℝ) ^ (-4 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast mainBinSet_card_le j) (by positivity)
    _ = C * (j : ℝ) ^ (-3 : ℝ) := by rw [← mul_assoc, mul_comm (j : ℝ) C, mul_assoc, hpow]

theorem ae_eventually_centralRootCount_eq_capped :
    ∀ᵐ ε ∂sequenceLaw, ∀ᶠ j : ℕ in atTop, centralRootCount ε j = centralCappedCount ε j := by
  obtain ⟨C, _, hprob⟩ := eventually_central_disagreement_probability
  have hs : Summable (fun j ↦ sequenceLaw.real {ε | centralRootCount ε j ≠ centralCappedCount ε j}) := by
    have hp : Summable (fun j : ℕ ↦ (j : ℝ) ^ (-3 : ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
    apply (hp.mul_left C).of_norm_bounded_eventually_nat
    filter_upwards [hprob] with j hj
    simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using hj
  have h := ae_eventually_notMem_of_summable_real sequenceLaw
    (fun j ↦ {ε | centralRootCount ε j ≠ centralCappedCount ε j}) hs
  simpa only [Set.mem_ofPred_eq, not_not] using h

end Erdos521
