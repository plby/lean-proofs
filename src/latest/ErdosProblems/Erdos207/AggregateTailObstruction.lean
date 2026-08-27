/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SharpScheduledAbsorberFailure

/-!
# Scaling obstruction for the coarse aggregate failure certificate

The inequalities here concern an upper bound, not the actual failure
probability.  They preserve a genuine obstruction to instantiating the
quadratic corridor with that upper bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem aggregatePairExactBankExtensionCoefficient_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    {q j : ℕ} (B : TripleSystemOn V) (hq : 5 ≤ q) (hj : 3 ≤ j) :
    0 < aggregatePairExactBankExtensionCoefficient q j B := by
  classical
  let r : (Icc 5 q : Finset ℕ) := ⟨5, mem_Icc.mpr ⟨le_rfl, hq⟩⟩
  let K : subsetsUpToCard B q := ⟨∅, by simp⟩
  have hterm : 0 < (j - 2) * (2 ^ (r.1 ^ 3) * (r.1 + 1)) := by
    have : 0 < j - 2 := by omega
    positivity
  have hinner : (j - 2) * (2 ^ (r.1 ^ 3) * (r.1 + 1)) ≤
      ∑ _K : subsetsUpToCard B q,
        (j - 2) * (2 ^ (r.1 ^ 3) * (r.1 + 1)) :=
    single_le_sum (f := fun _K : subsetsUpToCard B q ↦
      (j - 2) * (2 ^ (r.1 ^ 3) * (r.1 + 1)))
        (fun _ _ ↦ Nat.zero_le _) (mem_univ K)
  unfold aggregatePairExactBankExtensionCoefficient
  exact hterm.trans_le (hinner.trans
    (single_le_sum (f := fun r : (Icc 5 q : Finset ℕ) ↦
      ∑ _K : subsetsUpToCard B q,
        (j - 2) * (2 ^ (r.1 ^ 3) * (r.1 + 1)))
          (fun _ _ ↦ Nat.zero_le _) (mem_univ r)))

theorem aggregatePairTwoAwayThreatExtensionCoefficient_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (B : TripleSystemOn V) (hq : 5 ≤ q) :
    0 < aggregatePairTwoAwayThreatExtensionCoefficient q B := by
  classical
  let j : IndexedThreatOrder q := ⟨3, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  unfold aggregatePairTwoAwayThreatExtensionCoefficient
  exact (aggregatePairExactBankExtensionCoefficient_pos B hq
    (show 3 ≤ j.1 from le_rfl)).trans_le
      (single_le_sum (f := fun j : IndexedThreatOrder q ↦
        aggregatePairExactBankExtensionCoefficient q j.1 B)
          (fun _ _ ↦ Nat.zero_le _) (mem_univ j))

theorem one_le_aggregatePairTwoAwayTail
    (q s K : ℕ) (kappa : ℝ≥0) (hkappa : (K + 1 : ℕ) ≤ kappa) :
    1 ≤ aggregatePairTwoAwayTail q s K kappa := by
  have hfactorial : (1 : ℝ≥0) ≤ twoAwayMomentJointConstant q s := by
    exact_mod_cast Nat.factorial_pos (twoAwayMomentUnionCutoff q s)
  have htwo : (1 : ℝ≥0) ≤ 2 ^ twoAwayMomentUnionCutoff q s :=
    one_le_pow₀ (by norm_num)
  have hbase : ((K + 1 : ℕ) : ℝ≥0) ≤
      2 ^ twoAwayMomentUnionCutoff q s * kappa :=
    hkappa.trans (le_mul_of_one_le_left zero_le htwo)
  unfold aggregatePairTwoAwayTail
  apply (one_le_div (by positivity)).2
  exact (pow_le_pow_left' hbase s).trans
    (le_mul_of_one_le_left zero_le hfactorial)

theorem one_le_sharpScheduledAbsorberPhaseFailure
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M n sPair sGlobal sInc Kpair Kglobal Kinc I : ℕ)
    (H : SimpleGraph V) (X : Finset V) (B : TripleSystemOn V)
    (scale : ℝ≥0) (thetaPair aPair vPair : ℝ)
    (hq : 5 ≤ q) (hscale : 1 ≤ scale)
    (hpair : 0 < Fintype.card (PairOn V))
    (hK : Kinc ≤ (Fintype.card V) ^ 2) :
    1 ≤ sharpScheduledAbsorberPhaseFailure q M n sPair sGlobal sInc
      Kpair Kglobal Kinc I H X B scale thetaPair aPair vPair := by
  have hcoeff : (1 : ℝ≥0) ≤ aggregatePairTwoAwayThreatExtensionCoefficient q B := by
    exact_mod_cast aggregatePairTwoAwayThreatExtensionCoefficient_pos B hq
  have hscalePow : 1 ≤ scale ^ q := one_le_pow₀ hscale
  have hK' : ((Kinc + 1 : ℕ) : ℝ≥0) ≤ (Fintype.card V + 1 : ℝ≥0) ^ 2 := by
    have : Kinc + 1 ≤ (Fintype.card V + 1) ^ 2 := by
      calc
        Kinc + 1 ≤ (Fintype.card V) ^ 2 + 1 := Nat.add_le_add_right hK 1
        _ ≤ (Fintype.card V) ^ 2 + 1 + 2 * Fintype.card V := Nat.le_add_right _ _
        _ = (Fintype.card V + 1) ^ 2 := by ring
    exact_mod_cast this
  have htail : 1 ≤ aggregatePairTwoAwayTail q sInc Kinc
      (scale ^ q * ((aggregatePairTwoAwayThreatExtensionCoefficient q B : ℕ) *
        (Fintype.card V + 1 : ℝ≥0) ^ 2)) := by
    apply one_le_aggregatePairTwoAwayTail
    exact hK'.trans ((le_mul_of_one_le_left zero_le hcoeff).trans
      (le_mul_of_one_le_left zero_le hscalePow))
  have hpair' : (1 : ℝ≥0) ≤ Fintype.card (PairOn V) := by exact_mod_cast hpair
  have hterm := one_le_mul_of_one_le_of_one_le hpair' htail
  exact hterm.trans (by
    unfold sharpScheduledAbsorberPhaseFailure
    exact (le_add_of_nonneg_left (by positivity)).trans
      (le_add_of_nonneg_right (by positivity)))

theorem canonical_aggregate_cutoff_le_ambient_square
    {T K outside n : ℕ} (hT : 3 ≤ T) (hout : outside ≤ n)
    (hcut : T ^ 102 * K ≤ 8 * outside ^ 2) : K ≤ n ^ 2 := by
  have hpower : 8 ≤ T ^ 102 := by
    calc
      8 ≤ 3 ^ (102 : ℕ) := by norm_num
      _ ≤ T ^ 102 := Nat.pow_le_pow_left hT 102
  have h8 : 8 * K ≤ 8 * outside ^ 2 :=
    (Nat.mul_le_mul_right K hpower).trans hcut
  have hK : K ≤ outside ^ 2 := by omega
  exact hK.trans (Nat.pow_le_pow_left hout 2)

/-- In the nontrivial ambient range, the canonical small aggregate cutoff
forces the five-event bound to be at least one. -/
theorem canonical_sharpScheduledAbsorberPhaseFailure_not_lt_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (q M n sPair sGlobal sInc Kpair Kglobal Kinc I : ℕ)
    (H : SimpleGraph V) (X : Finset V) (B : TripleSystemOn V)
    (scale : ℝ≥0) (thetaPair aPair vPair : ℝ)
    (hq : 5 ≤ q) (hscale : 1 ≤ scale) (hn : 2 ≤ Fintype.card V)
    {T outside : ℕ} (hT : 3 ≤ T) (hout : outside ≤ Fintype.card V)
    (hcut : T ^ 102 * Kinc ≤ 8 * outside ^ 2) :
    ¬ sharpScheduledAbsorberPhaseFailure q M n sPair sGlobal sInc
      Kpair Kglobal Kinc I H X B scale thetaPair aPair vPair < 1 := by
  obtain ⟨v, w, hvw⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card V by omega)
  let P : PairOn V := ⟨{v, w}, by simp [hvw]⟩
  have hpair : 0 < Fintype.card (PairOn V) :=
    Fintype.card_pos_iff.mpr ⟨P⟩
  exact not_lt_of_ge (one_le_sharpScheduledAbsorberPhaseFailure
    q M n sPair sGlobal sInc Kpair Kglobal Kinc I H X B scale
    thetaPair aPair vPair hq hscale hpair
      (canonical_aggregate_cutoff_le_ambient_square hT hout hcut))

end

end Erdos207
