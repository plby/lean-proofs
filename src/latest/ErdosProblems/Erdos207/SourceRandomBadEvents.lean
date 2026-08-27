/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRandomGoodCounts

/-! # Finite bad-event families for simultaneous source augmentation -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def SourceRandomRootBad
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (a : ℝ≥0) (ω : TripleSystemOn V → Bool) : Prop :=
  ∃ R ∈ sourceRandomRootIndex W j, R.Nonempty ∧
    a * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card) <
      ((familyExtensions (sampleTerminalConfigurations W j ω) R).card : ℝ≥0)

def SourceRandomPairBad
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (F : ForbiddenFamilyOn V) (a : ℝ≥0) (ω : TripleSystemOn V → Bool) : Prop :=
  ∃ Q ∈ (univ : Finset (TripleOn V × TripleOn V)),
    (a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
      ((distinctEqualRemainderPairs (sampleTerminalConfigurations W j ω) Q.1 Q.2).card : ℝ≥0)) ∨
    (a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
      ((crossDistinctConfigurationPairs F (sampleTerminalConfigurations W j ω) Q.1 Q.2).card : ℝ≥0)) ∨
    (a * (W.terminalSize : ℝ≥0) ^ (j - 4) <
      ((crossDistinctConfigurationPairs (sampleTerminalConfigurations W j ω) F Q.1 Q.2).card : ℝ≥0))

def SourceRandomOrderFourBad
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (a : ℝ≥0) (ω : TripleSystemOn V → Bool) : Prop :=
  j = 4 ∧ ∃ Q ∈ (univ : Finset (TripleOn V × VortexPairOn V)),
    a < ((W.terminalPairExtensions (sampleTerminalConfigurations W j ω) Q.1 Q.2).card : ℝ≥0)

theorem not_sourceRandomCountsGood_covered
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (a : ℝ≥0) (ω : TripleSystemOn V → Bool)
    (h : ¬ SourceRandomCountsGood W j F a ω) :
    SourceRandomRootBad W j a ω ∨ SourceRandomPairBad W j F a ω ∨ SourceRandomOrderFourBad W j a ω := by
  classical
  by_contra hbad
  apply h
  refine ⟨?_, ?_, ?_⟩
  · intro R hR hne
    by_contra hfail
    exact hbad (Or.inl ⟨R, hR, hne, lt_of_not_ge hfail⟩)
  · intro T T'
    refine ⟨?_, ?_, ?_⟩
    · by_contra hfail
      exact hbad (Or.inr (Or.inl ⟨(T, T'), mem_univ _, Or.inl (lt_of_not_ge hfail)⟩))
    · by_contra hfail
      exact hbad (Or.inr (Or.inl ⟨(T, T'), mem_univ _, Or.inr (Or.inl (lt_of_not_ge hfail))⟩))
    · by_contra hfail
      exact hbad (Or.inr (Or.inl ⟨(T, T'), mem_univ _, Or.inr (Or.inr (lt_of_not_ge hfail))⟩))
  · intro hj T Q
    by_contra hfail
    exact hbad (Or.inr (Or.inr ⟨hj, (T, Q), mem_univ _, lt_of_not_ge hfail⟩))

namespace SourceRandomConfigurationParameters

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j s : ℕ}
  {W : Vortex V ell} {delta a : ℝ≥0}

theorem rootBad_probability_le (P : SourceRandomConfigurationParameters W j delta a s) :
    P.law.probability (SourceRandomRootBad W j a) ≤
      (sourceRandomRootIndex W j).card * ((2 : ℝ≥0) ^ s)⁻¹ := by
  classical
  unfold SourceRandomRootBad
  apply (P.law.probability_exists_le (sourceRandomRootIndex W j) _).trans
  calc
    _ ≤ ∑ _R ∈ sourceRandomRootIndex W j, ((2 : ℝ≥0) ^ s)⁻¹ := by
      apply sum_le_sum
      intro R hR
      by_cases hne : R.Nonempty
      · have hRcard : R.card ≤ j - 2 := (mem_subsetsUpToCard_iff.mp hR).2
        exact (P.law.probability_mono (fun _ h ↦ h.2)).trans (P.root_failure R hne hRcard)
      · simp only [hne, false_and, FiniteLaw.probability_false, zero_le]
    _ = _ := by simp only [sum_const, nsmul_eq_mul]

theorem pairBad_probability_le (P : SourceRandomConfigurationParameters W j delta a s)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    P.law.probability (SourceRandomPairBad W j F a) ≤
      (3 * Fintype.card (TripleOn V × TripleOn V) : ℕ) * ((2 : ℝ≥0) ^ s)⁻¹ := by
  classical
  unfold SourceRandomPairBad
  apply (P.law.probability_exists_le (univ : Finset (TripleOn V × TripleOn V)) _).trans
  calc
    _ ≤ ∑ _Q : TripleOn V × TripleOn V, 3 * ((2 : ℝ≥0) ^ s)⁻¹ := by
      apply sum_le_sum
      intro Q _hQ
      apply (P.law.probability_or_le _ _).trans
      apply (add_le_add le_rfl (P.law.probability_or_le _ _)).trans
      exact (add_le_add (P.pair_failure Q.1 Q.2)
        (add_le_add (P.old_new_failure F y z hF hdeltaY Q.1 Q.2)
          (P.new_old_failure F y z hF hdeltaY Q.1 Q.2))).trans_eq (by ring)
    _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]; ring

theorem orderFourBad_probability_le (P : SourceRandomConfigurationParameters W j delta a s) :
    P.law.probability (SourceRandomOrderFourBad W j a) ≤
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
    apply (P.law.probability_exists_le (univ : Finset (TripleOn V × VortexPairOn V)) _).trans
    calc
      _ ≤ ∑ _Q : TripleOn V × VortexPairOn V, ((2 : ℝ≥0) ^ s)⁻¹ := by
        apply sum_le_sum
        intro Q _hQ
        exact P.order_four_failure hj Q.1 Q.2
      _ = _ := by simp only [sum_const, card_univ, nsmul_eq_mul]
  · have hevent : SourceRandomOrderFourBad W j a = (fun _ ↦ False) := by
      funext ω
      apply propext
      exact ⟨fun h ↦ hj h.1, False.elim⟩
    rw [hevent, FiniteLaw.probability_false]
    exact zero_le

end SourceRandomConfigurationParameters

end

end Erdos207
