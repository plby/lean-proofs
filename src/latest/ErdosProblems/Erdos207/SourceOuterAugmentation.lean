/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceAugmentationCounts
import ErdosProblems.Erdos207.PureProfileAugmentation
import ErdosProblems.Erdos207.ProfiledDistinctUnionCount

/-! # Later-prefix augmentation using only the added-family count increments -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem profiledExtensions_outer_union_bound
    {V : Type*} [Fintype V] [DecidableEq V] {ell j d n : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (i : Fin ell)
    (hn : n = (W.U i.castSucc).card) (hterminal : 0 < W.terminalSize)
    (huniform : ∀ E ∈ G, E.card = j - 2)
    (hshell : ∀ E ∈ G, ∀ T ∈ E, W.level T = i.castSucc)
    (R : TripleSystemOn V) (c a : ℝ≥0) (hdf : d ≤ j - 2 - R.card)
    (hold : ∀ t, ((W.profiledExtensions F R t).card : ℝ≥0) ≤ c * W.sourceProfileScale d t)
    (hnew : ((familyExtensions G R).card : ℝ≥0) ≤ a * (n : ℝ≥0) ^ d)
    (t : VortexProfile ell) :
    ((W.profiledExtensions (F ∪ G) R t).card : ℝ≥0) ≤ (c + a) * W.sourceProfileScale d t := by
  by_cases ht : t = vortexPureProfile i (j - 2 - R.card)
  · subst t
    have hsub : W.profiledExtensions G R (vortexPureProfile i (j - 2 - R.card)) ⊆ familyExtensions G R := by
      intro E hE
      have hh := (W.mem_profiledExtensions_iff G R _ E).mp hE
      exact mem_familyExtensions_iff.mpr ⟨hh.1, hh.2.1⟩
    have hcount : ((W.profiledExtensions G R (vortexPureProfile i (j - 2 - R.card))).card : ℝ≥0) ≤
        (familyExtensions G R).card := by exact_mod_cast card_le_card hsub
    have hscale : (n : ℝ≥0) ^ d ≤ W.sourceProfileScale d (vortexPureProfile i (j - 2 - R.card)) := by
      rw [hn]
      exact W.levelSize_pow_le_sourceProfileScale_pure i d _ hterminal hdf
    have hadded := (hcount.trans hnew).trans (mul_le_mul_of_nonneg_left hscale zero_le)
    rw [W.profiledExtensions_union]
    have hu : (((W.profiledExtensions F R (vortexPureProfile i (j - 2 - R.card))) ∪
        (W.profiledExtensions G R (vortexPureProfile i (j - 2 - R.card)))).card : ℝ≥0) ≤
        (W.profiledExtensions F R (vortexPureProfile i (j - 2 - R.card))).card +
        (W.profiledExtensions G R (vortexPureProfile i (j - 2 - R.card))).card := by
      exact_mod_cast card_union_le _ _
    exact hu.trans ((add_le_add (hold _) hadded).trans_eq (by ring))
  · have hsub := profiledExtensions_subset_old_of_not_pure W ∅ G i huniform
      (fun E hE T hT ↦ hshell E (mem_sdiff.mp hE).1 T hT) R t ht
    have hempty : W.profiledExtensions G R t = ∅ := by
      apply subset_empty.mp
      simpa only [Vortex.profiledExtensions, filter_empty] using hsub
    rw [W.profiledExtensions_union, hempty, union_empty]
    exact (hold t).trans (mul_le_mul_of_nonneg_right le_self_add zero_le)

theorem SourceAugmentationCounts.outer_sourceWellSpread
    {V : Type*} [Fintype V] [DecidableEq V] {ell j n : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z a : ℝ≥0}
    (hcounts : SourceAugmentationCounts j n F G a)
    (hF : SourceVortexWellSpread W j F y z) (i : Fin ell)
    (hn : n = (W.U i.castSucc).card)
    (hshell : ∀ E ∈ G, ∀ T ∈ E, W.level T = i.castSucc) :
    SourceVortexWellSpread W j (F ∪ G) (y + a) (z + 3 * a) := by
  have huniform : ∀ E ∈ F ∪ G, E.card = j - 2 ∧ IsPackingOn E := by
    intro E hE
    exact (mem_union.mp hE).elim (hF.uniform E) (hcounts.uniform E)
  have hnew : ∀ E ∈ (F ∪ G) \ F, ∀ T ∈ E, W.level T = i.castSucc := by
    intro E hE T hT
    have hh := mem_sdiff.mp hE
    exact hshell E ((mem_union.mp hh.1).resolve_left hh.2) T hT
  have ha : a ≤ 3 * a := by
    calc
      a ≤ a + (a + a) := le_self_add
      _ = _ := by ring
  refine ⟨hF.order, hF.terminal_nonempty, huniform, ?_, ?_, ?_, ?_⟩
  · intro R t hR hRcard
    have hdf : j - vortexRootExponent j R.card ≤ j - 2 - R.card := by
      have := add_two_le_vortexRootExponent j R.card
      omega
    have hbound := profiledExtensions_outer_union_bound W F G i hn hF.terminal_nonempty
      (fun E hE ↦ (hcounts.uniform E hE).1) hshell R z a hdf
      (fun t ↦ hF.extensions R t hR hRcard) (hcounts.roots R hR hRcard) t
    exact hbound.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl ha) zero_le)
  · intro T T' t
    by_cases ht : t = vortexPureProfile i (j - 3)
    · subst t
      have hscale : (n : ℝ≥0) ^ (j - 4) ≤ W.sourceProfileScale (j - 4) (vortexPureProfile i (j - 3)) := by
        rw [hn]
        exact W.levelSize_pow_le_sourceProfileScale_pure i (j - 4) (j - 3) hF.terminal_nonempty (by omega)
      have hadded := mul_le_mul_of_nonneg_left hscale (show 0 ≤ a from zero_le)
      have hcover : ((W.profiledDistinctEqualRemainderPairs (F ∪ G) T T' (vortexPureProfile i (j - 3))).card : ℝ≥0) ≤
          (W.profiledDistinctEqualRemainderPairs F T T' (vortexPureProfile i (j - 3))).card +
          (distinctEqualRemainderPairs G T T').card + (crossDistinctConfigurationPairs F G T T').card +
          (crossDistinctConfigurationPairs G F T T').card := by
        exact_mod_cast card_profiledDistinctPairs_union_le_four_profile W F G T T' (vortexPureProfile i (j - 3))
      exact hcover.trans ((add_le_add
        (add_le_add (add_le_add (hF.equal_remainders T T' _) ((hcounts.pairs T T').trans hadded))
          ((hcounts.old_new T T').trans hadded)) ((hcounts.new_old T T').trans hadded)).trans_eq (by ring))
    · have hcount : ((W.profiledDistinctEqualRemainderPairs (F ∪ G) T T' t).card : ℝ≥0) ≤
          (W.profiledDistinctEqualRemainderPairs F T T' t).card := by
        exact_mod_cast card_le_card (profiledDistinctPairs_subset_old_of_not_pure W F (F ∪ G) i
          (fun E hE ↦ (huniform E hE).1) hnew T T' t ht)
      exact (hcount.trans (hF.equal_remainders T T' t)).trans (mul_le_mul_of_nonneg_right le_self_add zero_le)
  · intro hj T P hP
    have hcount : ((W.terminalPairExtensions (F ∪ G) T P).card : ℝ≥0) ≤ (W.terminalPairExtensions F T P).card := by
      exact_mod_cast card_le_card (terminalPairExtensions_subset_old_of_new_outer W F (F ∪ G) i hnew T P)
    exact (hcount.trans (hF.order_four_pair hj T P hP)).trans le_self_add
  · intro T t
    have hRcard : ({T} : TripleSystemOn V).card ≤ j - 2 := by
      have := hF.order
      simp only [card_singleton]
      omega
    have hroot := hcounts.roots {T} (singleton_nonempty T) hRcard
    simp only [card_singleton, vortexRootExponent_one] at hroot
    exact profiledExtensions_outer_union_bound W F G i hn hF.terminal_nonempty
      (fun E hE ↦ (hcounts.uniform E hE).1) hshell {T} y a
      (by simp only [card_singleton]; omega) (hF.singleton_extensions T) hroot t

end

end Erdos207
