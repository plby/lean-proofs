import ErdosProblems.Erdos1148.OrbitAtomBowenCover
import ErdosProblems.Erdos1148.CoveredCellCollision
import ErdosProblems.Erdos1148.PartialPartitionEntropy
import ErdosProblems.Erdos1148.FiniteOrbitEntropy

/-! # Entropy bounds for good orbit words from a forward pair bound -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Function

noncomputable def exceptionalStepCoverCost : ℝ := 33 ^ 3 * Real.exp 1

lemma exceptionalStepCoverCost_one_le : 1 ≤ exceptionalStepCoverCost := by
  have h := Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [exceptionalStepCoverCost]
  nlinarith

def GoodOrbitWord {N n : ℕ} (κ : ℝ) (w : Fin (n + 1) → Option (Fin N)) : Prop :=
  w 0 ≠ none ∧ (exceptionalWordStepCount w : ℝ) ≤ κ * (n + 1)

noncomputable instance goodOrbitWordDecidable {N n : ℕ} (κ : ℝ) :
    DecidablePred (GoodOrbitWord (N := N) (n := n) κ) := Classical.decPred _

lemma exceptionalStepCoverCost_pow_le_exp {N n : ℕ} {κ : ℝ}
    {w : Fin (n + 1) → Option (Fin N)} (hw : GoodOrbitWord κ w) :
    exceptionalStepCoverCost ^ exceptionalWordStepCount w ≤
      Real.exp (κ * (n + 1) * Real.log exceptionalStepCoverCost) := by
  have hpos : 0 < exceptionalStepCoverCost := zero_lt_one.trans_le exceptionalStepCoverCost_one_le
  have hlog : 0 ≤ Real.log exceptionalStepCoverCost := Real.log_nonneg exceptionalStepCoverCost_one_le
  calc
    _ = Real.exp ((exceptionalWordStepCount w : ℝ) * Real.log exceptionalStepCoverCost) := by
      rw [Real.exp_nat_mul, Real.exp_log hpos]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw.2 hlog)

theorem FineModularPartition.orbitEntropy_lower_of_pair_bound (P : FineModularPartition)
    (μ : Measure ModularOrbitSpace) [IsProbabilityMeasure μ] {n : ℕ} (κ : ℝ)
    {B m : ℝ} (hB : (μ.prod μ).real (modularForwardBowenPairs (32 * P.radius) (n : ℝ)) ≤ B)
    (hm : 0 < m)
    (hsum : (∑ w : {w : Fin (n + 1) → Option (Fin P.size) // GoodOrbitWord κ w},
      μ.real (P.partition.orbitAtom modularTimeOne (n + 1) w.val)) = m) :
    -m * Real.log ((Real.exp (κ * (n + 1) * Real.log exceptionalStepCoverCost) * B) / m) ≤
      P.partition.orbitEntropy μ modularTimeOne (n + 1) := by
  classical
  let s := P.partition.orbitAtom modularTimeOne (n + 1)
  let p := GoodOrbitWord (N := P.size) (n := n) κ
  have hs : ∀ w : Subtype p, MeasurableSet (s w.val) :=
    fun w => P.partition.measurableSet_orbitAtom continuous_modularTimeOne.measurable _ w.val
  have hdisj : Pairwise (Disjoint on fun w : Subtype p => s w.val) := by
    intro v w hvw
    exact P.partition.pairwise_disjoint_orbitAtom modularTimeOne _
      (fun h => hvw (Subtype.ext h))
  have hcover (w : Subtype p) : ∃ (N : ℕ) (D : Fin N → Set ModularOrbitSpace),
      (N : ℝ) ≤ Real.exp (κ * (n + 1) * Real.log exceptionalStepCoverCost) ∧
      (∀ j, MeasurableSet (D j)) ∧ s w.val ⊆ ⋃ j, D j ∧
      ∀ j, D j ×ˢ D j ⊆ modularForwardBowenPairs (32 * P.radius) (n : ℝ) := by
    obtain ⟨N, D, hN, _, hmeas, hcov, hpair⟩ := P.orbitAtom_bowen_cover w.val w.property.1
    exact ⟨N, D, hN.trans (exceptionalStepCoverCost_pow_le_exp w.property), hmeas, hcov, hpair⟩
  have h := covered_cells_entropy_lower_bound μ (fun w : Subtype p => s w.val) hs hdisj
    (measurableSet_modularForwardBowenPairs _ _) (Real.exp_pos _).le hcover hB hm hsum
  exact h.trans (finitePartitionEntropy_subtype_le μ s p)

end Erdos1148.DukeArithmetic
