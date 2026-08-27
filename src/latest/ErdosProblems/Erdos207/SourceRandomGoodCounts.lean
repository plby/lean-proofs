/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRandomMixedSampling

/-! # The finite good-count event for source random augmentation -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceRandomRootIndex
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) : Finset (TripleSystemOn V) :=
  subsetsUpToCard (triplesSupportedOn (W.U (Fin.last ell))) (j - 2)

def SourceRandomCountsGood
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (F : ForbiddenFamilyOn V) (a : ℝ≥0)
    (ω : TripleSystemOn V → Bool) : Prop :=
  (∀ R ∈ sourceRandomRootIndex W j, R.Nonempty →
    ((familyExtensions (sampleTerminalConfigurations W j ω) R).card : ℝ≥0) ≤
      a * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card)) ∧
  (∀ T T' : TripleOn V,
    ((distinctEqualRemainderPairs (sampleTerminalConfigurations W j ω) T T').card : ℝ≥0) ≤
      a * (W.terminalSize : ℝ≥0) ^ (j - 4) ∧
    ((crossDistinctConfigurationPairs F (sampleTerminalConfigurations W j ω) T T').card : ℝ≥0) ≤
      a * (W.terminalSize : ℝ≥0) ^ (j - 4) ∧
    ((crossDistinctConfigurationPairs (sampleTerminalConfigurations W j ω) F T T').card : ℝ≥0) ≤
      a * (W.terminalSize : ℝ≥0) ^ (j - 4)) ∧
  (j = 4 → ∀ (T : TripleOn V) (Q : VortexPairOn V),
    ((W.terminalPairExtensions (sampleTerminalConfigurations W j ω) T Q).card : ℝ≥0) ≤ a)

theorem familyExtensions_sample_eq_empty_of_not_terminal_root
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (R : TripleSystemOn V) (ω : TripleSystemOn V → Bool)
    (hR : ¬ R ⊆ triplesSupportedOn (W.U (Fin.last ell))) :
    familyExtensions (sampleTerminalConfigurations W j ω) R = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro C hC
  have hm := mem_familyExtensions_iff.mp hC
  have hcandidate := (mem_filter.mp hm.1).1
  exact hR (hm.2.trans ((mem_terminalRandomConfigurations_iff W C).mp hcandidate).1)

theorem SourceRandomCountsGood.sourceWellSpread
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z a : ℝ≥0}
    {ω : TripleSystemOn V → Bool} (hgood : SourceRandomCountsGood W j F a ω)
    (hF : SourceVortexWellSpread W j F y z) :
    SourceVortexWellSpread W j (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a) := by
  apply hF.union_terminal_of_count_bounds a
    ((terminalRandomConfigurations_isTerminal W).mono (filter_subset _ _))
    (fun C hC ↦ terminalRandomConfigurations_uniform W C (mem_filter.mp hC).1)
  · intro R hR hRcard
    by_cases hsub : R ⊆ triplesSupportedOn (W.U (Fin.last ell))
    · exact hgood.1 R (mem_subsetsUpToCard_iff.mpr ⟨hsub, hRcard⟩) hR
    · change ((familyExtensions (sampleTerminalConfigurations W j ω) R).card : ℝ≥0) ≤ _
      rw [familyExtensions_sample_eq_empty_of_not_terminal_root (j := j) W R ω hsub]
      simp
  · intro T T'
    have hcover : ((W.profiledDistinctEqualRemainderPairs (F ∪ sampleTerminalConfigurations W j ω) T T' 0).card : ℝ≥0) ≤
        (W.profiledDistinctEqualRemainderPairs F T T' 0).card +
        (distinctEqualRemainderPairs (sampleTerminalConfigurations W j ω) T T').card +
        (crossDistinctConfigurationPairs F (sampleTerminalConfigurations W j ω) T T').card +
        (crossDistinctConfigurationPairs (sampleTerminalConfigurations W j ω) F T T').card := by
      exact_mod_cast card_profiledDistinctPairs_union_le_four W F (sampleTerminalConfigurations W j ω) T T'
    obtain ⟨hpair, hleft, hright⟩ := hgood.2.1 T T'
    apply hcover.trans
    calc
      _ ≤ ((W.profiledDistinctEqualRemainderPairs F T T' 0).card : ℝ≥0) +
          a * (W.terminalSize : ℝ≥0) ^ (j - 4) + a * (W.terminalSize : ℝ≥0) ^ (j - 4) +
          a * (W.terminalSize : ℝ≥0) ^ (j - 4) :=
        add_le_add (add_le_add (add_le_add le_rfl hpair) hleft) hright
      _ = _ := by ring
  · intro hj T Q _hQ
    exact hgood.2.2 hj T Q

end

end Erdos207
