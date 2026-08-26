/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceGridFaceConvergence
import ErdosProblems.Erdos4b.SourceTensorMaynardBridge

/-!
# Unbounded variational quotients for finite rectangular families

This reuses the explicit nonsmooth family already proved in Base. The
new work is its approximation by finite simplex-supported grids.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory BoundedGaps.Maynard
open scoped BigOperators

theorem sourceGridFactors_integrable (K : ℕ) (A : ℝ) (n : ℕ)
    (j : Fin K → Fin (n + 1)) (i : Fin K) :
    IntegrableOn (sourceGridFactors K A n j i) (Set.Icc 0 1) :=
  ((sourceIntervalIndicator_integrable (sourceGridLower n (j i)) (sourceGridUpper n (j i))).const_mul
    (VariableMaynard.factor A ((K : ℝ) * sourceGridUpper n (j i)))).integrableOn

theorem sourceGridFactors_upper (K : ℕ) (A : ℝ) (n : ℕ)
    (j : Fin K → Fin (n + 1)) (i : Fin K) {t : ℝ} (ht : 1 < t) :
    sourceGridFactors K A n j i t = 0 := by
  have hn : t ∉ Set.Ioo (sourceGridLower n (j i)) (sourceGridUpper n (j i)) := by
    intro hh
    exact (not_lt_of_ge (sourceGridUpper_le_one n (j i))) (ht.trans hh.2)
  simp only [sourceGridFactors, sourceRectangleFactors, sourceIntervalIndicator,
    Set.indicator_of_notMem hn, mul_zero]

theorem sourceGridEnergy_eq (K : ℕ) (A : ℝ) (n : ℕ) :
    sourceTensorEnergy (sourceSimplexGrid K n) (sourceGridFactors K A n) =
      maynardI K (sourceGridValue K A n) :=
  sourceTensorEnergy_eq_maynardI _ _ (fun j _ i t ht ↦ sourceGridFactors_upper K A n j i ht)

theorem sourceGridFaceEnergy_eq (K : ℕ) (A : ℝ) (n : ℕ) (h : Fin K) :
    sourceTensorFaceEnergy (sourceSimplexGrid K n) (sourceGridFactors K A n) h =
      maynardJ K h (sourceGridValue K A n) :=
  sourceTensorFaceEnergy_eq_maynardJ _ _ (fun j _ i ↦ sourceGridFactors_integrable K A n j i)
    (fun j _ i t ht ↦ sourceGridFactors_upper K A n j i ht) h

theorem parameter_candidate_face_pos {r : ℕ} (hr : 8 ≤ r) (h : Fin (VariableMaynard.parameterK r)) :
    0 < maynardJ (VariableMaynard.parameterK r) h
      (VariableMaynard.candidate (VariableMaynard.parameterK r) (VariableMaynard.parameterA r)) := by
  have hrpos : 0 < r := by omega
  have hK := VariableMaynard.parameterK_pos r
  have hA := VariableMaynard.parameterA_pos hrpos
  have hKtwo : 2 ≤ VariableMaynard.parameterK r := by
    change 2 ≤ 2 ^ r
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) (show 1 ≤ r by omega)
  have hm := VariableMaynard.firstMoment_lt_quarter_of_log_lt hK hA
    (VariableMaynard.one_lt_parameterA_mul_parameterK hrpos) (VariableMaynard.parameter_log_upper hr)
  have hlower : 0 < (1 / 2 : ℝ) *
      VariableMaynard.shortMass (VariableMaynard.parameterK r) (VariableMaynard.parameterA r) ^ 2 *
      VariableMaynard.baseMass (VariableMaynard.parameterK r) (VariableMaynard.parameterA r) ^
        (VariableMaynard.parameterK r - 1) := by
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (VariableMaynard.shortMass_pos hK hA)))
      (pow_pos (VariableMaynard.baseMass_pos hK hA) _)
  exact hlower.trans (VariableMaynard.maynardJ_candidate_gt hKtwo hA hm h)

theorem exists_sourceGrid_ratio_gt (L : ℝ) :
    ∃ K : ℕ, ∃ A : ℝ, ∃ n : ℕ, 0 < K ∧ 0 < A ∧
      0 < sourceTensorEnergy (sourceSimplexGrid K n) (sourceGridFactors K A n) ∧
      (∀ h : Fin K, 0 < sourceTensorFaceEnergy (sourceSimplexGrid K n) (sourceGridFactors K A n) h) ∧
      L < (∑ h : Fin K, sourceTensorFaceEnergy (sourceSimplexGrid K n) (sourceGridFactors K A n) h) /
        sourceTensorEnergy (sourceSimplexGrid K n) (sourceGridFactors K A n) := by
  obtain ⟨r, hr⟩ := exists_nat_gt (max (8 : ℝ) (72 * L))
  have hr8 : 8 ≤ r := by exact_mod_cast ((le_max_left (8 : ℝ) (72 * L)).trans_lt hr).le
  have hLr : L < (r : ℝ) / 72 := by
    have hh := (le_max_right (8 : ℝ) (72 * L)).trans_lt hr
    linarith
  have hLcandidate := hLr.trans (VariableMaynard.parameter_ratio_gt hr8)
  have hK := VariableMaynard.parameterK_pos r
  have hA := VariableMaynard.parameterA_pos (show 0 < r by omega)
  obtain ⟨n, hnI, hnJ, hnL⟩ := exists_sourceGridValue_positive_and_ratio hK hA
    (parameter_candidate_face_pos hr8) hLcandidate
  refine ⟨VariableMaynard.parameterK r, VariableMaynard.parameterA r, n, hK, hA, ?_, ?_, ?_⟩
  · rwa [sourceGridEnergy_eq]
  · intro h
    rw [sourceGridFaceEnergy_eq]
    exact hnJ h
  · simpa only [sourceGridEnergy_eq, sourceGridFaceEnergy_eq, maynardRatio] using hnL

end

end Erdos4b
