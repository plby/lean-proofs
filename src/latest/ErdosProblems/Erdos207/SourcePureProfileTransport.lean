/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PureProfileAugmentation

/-! # Source well-spreadness transport without coefficient inflation -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceProfiledExtensions_bound_of_pure_augmentation
    {V : Type*} [Fintype V] [DecidableEq V] {ell0 ell1 j d : ℕ}
    (W0 : Vortex V ell0) (W1 : Vortex V ell1) (F Fsup : ForbiddenFamilyOn V) (i : Fin ell1)
    (hsize : W0.terminalSize = (W1.U i.castSucc).card)
    (hterminal : 0 < W1.terminalSize)
    (hlevel : ∀ T, W1.level T = i.castSucc → W0.level T = Fin.last ell0)
    (huniform : ∀ E ∈ Fsup, E.card = j - 2)
    (hnew : ∀ E ∈ Fsup \ F, ∀ T ∈ E, W1.level T = i.castSucc)
    (R : TripleSystemOn V) (c : ℝ≥0) (hdf : d ≤ j - 2 - R.card)
    (hold : ∀ t, ((W1.profiledExtensions F R t).card : ℝ≥0) ≤ c * W1.sourceProfileScale d t)
    (hcurrent : ((W0.profiledExtensions Fsup R 0).card : ℝ≥0) ≤ c * W0.sourceProfileScale d 0)
    (t : VortexProfile ell1) :
    ((W1.profiledExtensions Fsup R t).card : ℝ≥0) ≤ c * W1.sourceProfileScale d t := by
  by_cases ht : t = vortexPureProfile i (j - 2 - R.card)
  · subst t
    have hcount : ((W1.profiledExtensions Fsup R (vortexPureProfile i (j - 2 - R.card))).card : ℝ≥0) ≤
        (W0.profiledExtensions Fsup R 0).card := by
      exact_mod_cast card_le_card (profiledExtensions_pure_subset_zero W0 W1 Fsup i hlevel huniform R)
    rw [W0.sourceProfileScale_zero, hsize] at hcurrent
    exact (hcount.trans hcurrent).trans (mul_le_mul_of_nonneg_left
      (W1.levelSize_pow_le_sourceProfileScale_pure i d _ hterminal hdf) zero_le)
  · have hcount : ((W1.profiledExtensions Fsup R t).card : ℝ≥0) ≤ (W1.profiledExtensions F R t).card := by
      exact_mod_cast card_le_card (profiledExtensions_subset_old_of_not_pure W1 F Fsup i huniform hnew R t ht)
    exact hcount.trans (hold t)

theorem SourceVortexWellSpread.transport_outer_augmentation
    {V : Type*} [Fintype V] [DecidableEq V] {ell0 ell1 j : ℕ}
    {W0 : Vortex V ell0} {W1 : Vortex V ell1} {F Fsup : ForbiddenFamilyOn V}
    {y z y' z' : ℝ≥0} (i : Fin ell1)
    (hold : SourceVortexWellSpread W1 j F y z)
    (hcurrent : SourceVortexWellSpread W0 j Fsup y' z')
    (hy : y ≤ y') (hz : z ≤ z')
    (hsize : W0.terminalSize = (W1.U i.castSucc).card)
    (hlevel : ∀ T, W1.level T = i.castSucc → W0.level T = Fin.last ell0)
    (hnew : ∀ E ∈ Fsup \ F, ∀ T ∈ E, W1.level T = i.castSucc) :
    SourceVortexWellSpread W1 j Fsup y' z' := by
  have hOld := hold.mono hy hz
  have huniform : ∀ E ∈ Fsup, E.card = j - 2 := fun E hE ↦ (hcurrent.uniform E hE).1
  refine ⟨hcurrent.order, hold.terminal_nonempty, hcurrent.uniform, ?_, ?_, ?_, ?_⟩
  · intro R t hR hRcard
    have hdf : j - vortexRootExponent j R.card ≤ j - 2 - R.card := by
      have := add_two_le_vortexRootExponent j R.card
      omega
    exact sourceProfiledExtensions_bound_of_pure_augmentation W0 W1 F Fsup i hsize
      hold.terminal_nonempty hlevel huniform hnew R z' hdf
      (fun t ↦ hOld.extensions R t hR hRcard) (hcurrent.extensions R 0 hR hRcard) t
  · intro T T' t
    by_cases ht : t = vortexPureProfile i (j - 3)
    · subst t
      have hcount : ((W1.profiledDistinctEqualRemainderPairs Fsup T T' (vortexPureProfile i (j - 3))).card : ℝ≥0) ≤
          (W0.profiledDistinctEqualRemainderPairs Fsup T T' 0).card := by
        exact_mod_cast card_le_card (profiledDistinctPairs_pure_subset_zero W0 W1 Fsup i hlevel huniform T T')
      have hbound := hcurrent.equal_remainders T T' 0
      rw [W0.sourceProfileScale_zero, hsize] at hbound
      exact (hcount.trans hbound).trans (mul_le_mul_of_nonneg_left
        (W1.levelSize_pow_le_sourceProfileScale_pure i (j - 4) (j - 3) hold.terminal_nonempty (by omega)) zero_le)
    · have hcount : ((W1.profiledDistinctEqualRemainderPairs Fsup T T' t).card : ℝ≥0) ≤
          (W1.profiledDistinctEqualRemainderPairs F T T' t).card := by
        exact_mod_cast card_le_card (profiledDistinctPairs_subset_old_of_not_pure W1 F Fsup i huniform hnew T T' t ht)
      exact hcount.trans (hOld.equal_remainders T T' t)
  · intro hj T P hP
    have hcount : ((W1.terminalPairExtensions Fsup T P).card : ℝ≥0) ≤ (W1.terminalPairExtensions F T P).card := by
      exact_mod_cast card_le_card (terminalPairExtensions_subset_old_of_new_outer W1 F Fsup i hnew T P)
    exact hcount.trans (hOld.order_four_pair hj T P hP)
  · intro T t
    have hdf : j - 3 ≤ j - 2 - ({T} : TripleSystemOn V).card := by simp only [card_singleton]; omega
    exact sourceProfiledExtensions_bound_of_pure_augmentation W0 W1 F Fsup i hsize
      hold.terminal_nonempty hlevel huniform hnew {T} y' hdf
      (hOld.singleton_extensions T) (hcurrent.singleton_extensions T 0) t

end

end Erdos207
