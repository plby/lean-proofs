/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalProfileAugmentation

/-! # Deterministic source well-spreadness after controlled terminal augmentation -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.union_terminal_of_count_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hF : SourceVortexWellSpread W j F y z) (a : ℝ≥0)
    (hG : IsTerminalConfigurationFamily W G)
    (hGsize : ∀ C ∈ G, C.card = j - 2 ∧ IsPackingOn C)
    (hroots : ∀ R : TripleSystemOn V, R.Nonempty → R.card ≤ j - 2 →
      ((familyExtensions G R).card : ℝ≥0) ≤ a * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card))
    (hpairs : ∀ T T' : TripleOn V,
      ((W.profiledDistinctEqualRemainderPairs (F ∪ G) T T' 0).card : ℝ≥0) ≤
        (W.profiledDistinctEqualRemainderPairs F T T' 0).card +
          3 * a * (W.terminalSize : ℝ≥0) ^ (j - 4))
    (horder4 : j = 4 → ∀ (T : TripleOn V) (P : VortexPairOn V), ¬ P.1 ⊆ T.1 →
      ((W.terminalPairExtensions G T P).card : ℝ≥0) ≤ a) :
    SourceVortexWellSpread W j (F ∪ G) (y + a) (z + 3 * a) := by
  have ha : a ≤ 3 * a := by
    calc
      a ≤ a + (a + a) := le_self_add
      _ = _ := by ring
  have hz : z ≤ z + 3 * a := le_self_add
  refine ⟨hF.order, hF.terminal_nonempty, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    rcases mem_union.mp hC with h | h
    · exact hF.uniform C h
    · exact hGsize C h
  · intro R t hR hRcard
    by_cases ht : t = 0
    · subst t
      have hsub : ((W.profiledExtensions (F ∪ G) R 0).card : ℝ≥0) ≤
          (W.profiledExtensions F R 0).card + (familyExtensions G R).card := by
        rw [W.profiledExtensions_union, hG.profiledExtensions_zero]
        exact_mod_cast card_union_le (W.profiledExtensions F R 0) (familyExtensions G R)
      have hold := hF.extensions R 0 hR hRcard
      rw [W.sourceProfileScale_zero] at hold ⊢
      calc
        _ ≤ ((W.profiledExtensions F R 0).card : ℝ≥0) + (familyExtensions G R).card := hsub
        _ ≤ z * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card) +
            a * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card) := add_le_add hold (hroots R hR hRcard)
        _ = (z + a) * (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j R.card) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add le_rfl ha) zero_le
    · rw [W.profiledExtensions_union, hG.profiledExtensions_eq_empty R t ht, union_empty]
      exact (hF.extensions R t hR hRcard).trans (mul_le_mul_of_nonneg_right hz zero_le)
  · intro T T' t
    by_cases ht : t = 0
    · subst t
      have hold := hF.equal_remainders T T' 0
      rw [W.sourceProfileScale_zero] at hold ⊢
      calc
        _ ≤ ((W.profiledDistinctEqualRemainderPairs F T T' 0).card : ℝ≥0) +
            3 * a * (W.terminalSize : ℝ≥0) ^ (j - 4) := hpairs T T'
        _ ≤ z * (W.terminalSize : ℝ≥0) ^ (j - 4) + 3 * a * (W.terminalSize : ℝ≥0) ^ (j - 4) :=
          add_le_add hold le_rfl
        _ = _ := by ring
    · rw [profiledDistinctPairs_union_eq_of_nonzero W F G T T' t ht hG]
      exact (hF.equal_remainders T T' t).trans (mul_le_mul_of_nonneg_right hz zero_le)
  · intro hj4 T P hP
    have hsub : ((W.terminalPairExtensions (F ∪ G) T P).card : ℝ≥0) ≤
        (W.terminalPairExtensions F T P).card + (W.terminalPairExtensions G T P).card := by
      rw [W.terminalPairExtensions_union]
      exact_mod_cast card_union_le (W.terminalPairExtensions F T P) (W.terminalPairExtensions G T P)
    exact hsub.trans ((add_le_add (hF.order_four_pair hj4 T P hP) (horder4 hj4 T P hP)).trans
      (add_le_add le_rfl ha))
  · intro T t
    by_cases ht : t = 0
    · subst t
      have hsub : ((W.profiledExtensions (F ∪ G) {T} 0).card : ℝ≥0) ≤
          (W.profiledExtensions F {T} 0).card + (familyExtensions G {T}).card := by
        rw [W.profiledExtensions_union, hG.profiledExtensions_zero]
        exact_mod_cast card_union_le (W.profiledExtensions F {T} 0) (familyExtensions G {T})
      have hold := hF.singleton_extensions T 0
      have hnew := hroots {T} (by simp) (by have hj := hF.order; simp; omega)
      simp only [card_singleton, vortexRootExponent_one] at hnew
      rw [W.sourceProfileScale_zero] at hold ⊢
      exact hsub.trans ((add_le_add hold hnew).trans_eq (by ring))
    · rw [W.profiledExtensions_union, hG.profiledExtensions_eq_empty {T} t ht, union_empty]
      exact (hF.singleton_extensions T t).trans (mul_le_mul_of_nonneg_right le_self_add zero_le)

end

end Erdos207
