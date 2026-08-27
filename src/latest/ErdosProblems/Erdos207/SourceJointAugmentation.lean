/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceJointConfigurationSampling
import ErdosProblems.Erdos207.SourceRandomFailurePolynomial

/-! # Simultaneous source augmentation from upper joint inclusion, without a coupling assumption -/

namespace Erdos207.SourceRandomConfigurationParameters

open Finset
open scoped NNReal

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j s : ℕ}
  {W : Vortex V ell} {delta a : ℝ≥0}

theorem joint_rootBad_probability_le (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L) :
    L.probability (SourceRandomRootBad W j a) ≤
      (sourceRandomRootIndex W j).card * ((2 : ℝ≥0) ^ s)⁻¹ := by
  classical
  unfold SourceRandomRootBad
  apply (L.probability_exists_le (sourceRandomRootIndex W j) _).trans
  calc
    _ ≤ ∑ _R ∈ sourceRandomRootIndex W j, ((2 : ℝ≥0) ^ s)⁻¹ := by
      apply sum_le_sum
      intro R hR
      by_cases hne : R.Nonempty
      · have hRcard : R.card ≤ j - 2 := (mem_subsetsUpToCard_iff.mp hR).2
        exact (L.probability_mono (fun _ h ↦ h.2)).trans (P.joint_root_failure L hjoint R hne hRcard)
      · simp only [hne, false_and, FiniteLaw.probability_false, zero_le]
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem joint_pairBad_probability_le (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    L.probability (SourceRandomPairBad W j F a) ≤
      (3 * Fintype.card (TripleOn V × TripleOn V) : ℕ) * ((2 : ℝ≥0) ^ s)⁻¹ := by
  classical
  unfold SourceRandomPairBad
  apply (L.probability_exists_le (univ : Finset (TripleOn V × TripleOn V)) _).trans
  calc
    _ ≤ ∑ _Q : TripleOn V × TripleOn V, 3 * ((2 : ℝ≥0) ^ s)⁻¹ := by
      apply sum_le_sum
      intro Q _hQ
      apply (L.probability_or_le _ _).trans
      apply (add_le_add le_rfl (L.probability_or_le _ _)).trans
      exact (add_le_add (P.joint_pair_failure L hjoint Q.1 Q.2)
        (add_le_add (P.joint_old_new_failure L hjoint F y z hF hdeltaY Q.1 Q.2)
          (P.joint_new_old_failure L hjoint F y z hF hdeltaY Q.1 Q.2))).trans_eq (by ring)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring

theorem joint_orderFourBad_probability_le (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L) :
    L.probability (SourceRandomOrderFourBad W j a) ≤
      Fintype.card (TripleOn V × VortexPairOn V) * ((2 : ℝ≥0) ^ s)⁻¹ := by
  classical
  by_cases hj : j = 4
  · have hevent : SourceRandomOrderFourBad W j a =
        (fun ω ↦ ∃ Q ∈ (univ : Finset (TripleOn V × VortexPairOn V)),
          a < ((W.terminalPairExtensions (sampleTerminalConfigurations W j ω) Q.1 Q.2).card : ℝ≥0)) := by
      funext ω
      apply propext
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hj, h⟩⟩
    rw [hevent]
    apply (L.probability_exists_le (univ : Finset (TripleOn V × VortexPairOn V)) _).trans
    calc
      _ ≤ ∑ _Q : TripleOn V × VortexPairOn V, ((2 : ℝ≥0) ^ s)⁻¹ := by
        apply sum_le_sum
        intro Q _hQ
        exact P.joint_order_four_failure L hjoint hj Q.1 Q.2
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]
  · have hevent : SourceRandomOrderFourBad W j a = (fun _ ↦ False) := by
      funext ω
      apply propext
      exact ⟨fun h ↦ hj h.1, False.elim⟩
    rw [hevent, FiniteLaw.probability_false]
    exact zero_le

theorem joint_goodCounts_failure_probability (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    L.probability (fun omega ↦ ¬ SourceRandomCountsGood W j F a omega) ≤
      sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hcover : L.probability (fun omega ↦ ¬ SourceRandomCountsGood W j F a omega) ≤
      L.probability (fun omega ↦ SourceRandomRootBad W j a omega ∨ SourceRandomPairBad W j F a omega ∨
        SourceRandomOrderFourBad W j a omega) :=
    L.probability_mono (fun omega hbad ↦ not_sourceRandomCountsGood_covered W F a omega hbad)
  apply hcover.trans
  apply (L.probability_or_le _ _).trans
  apply (add_le_add le_rfl (L.probability_or_le _ _)).trans
  apply (add_le_add (P.joint_rootBad_probability_le L hjoint)
    (add_le_add (P.joint_pairBad_probability_le L hjoint F y z hF hdeltaY)
      (P.joint_orderFourBad_probability_le L hjoint))).trans_eq
  simp only [sourceRandomFailureCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem joint_augmentation_failure_probability (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    L.probability (fun ω ↦ ¬ SourceVortexWellSpread W j
      (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a)) ≤
        sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hcover : L.probability (fun ω ↦ ¬ SourceVortexWellSpread W j
      (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a)) ≤
      L.probability (fun ω ↦ SourceRandomRootBad W j a ω ∨ SourceRandomPairBad W j F a ω ∨
        SourceRandomOrderFourBad W j a ω) := by
    apply L.probability_mono
    intro ω hbad
    apply not_sourceRandomCountsGood_covered W F a ω
    exact fun hgood ↦ hbad (hgood.sourceWellSpread hF)
  apply hcover.trans
  apply (L.probability_or_le _ _).trans
  apply (add_le_add le_rfl (L.probability_or_le _ _)).trans
  apply (add_le_add (P.joint_rootBad_probability_le L hjoint)
    (add_le_add (P.joint_pairBad_probability_le L hjoint F y z hF hdeltaY)
      (P.joint_orderFourBad_probability_le L hjoint))).trans_eq
  simp only [sourceRandomFailureCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem joint_augmentation_failure_probability_polynomial
    (P : SourceRandomConfigurationParameters W j delta a s)
    (L : FiniteLaw (TripleSystemOn V → Bool)) (hjoint : HasSourceConfigurationJointBound W j delta L)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    L.probability (fun ω ↦ ¬ SourceVortexWellSpread W j
      (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a)) ≤
        ((j + 3) * (Fintype.card V + 1) ^ (3 * j + 6) : ℕ) * ((2 : ℝ≥0) ^ s)⁻¹ := by
  apply (P.joint_augmentation_failure_probability L hjoint F y z hF hdeltaY).trans
  apply mul_le_mul_of_nonneg_right _ zero_le
  exact_mod_cast sourceRandomFailureCoefficient_le_polynomial W j P.order

end

end Erdos207.SourceRandomConfigurationParameters
