/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceVortexWellSpread

/-! # Restricting fixed source families to a deterministic shell -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.of_subset
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ} {W : Vortex V ell}
    {F G : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (hGF : G ⊆ F) :
    SourceVortexWellSpread W j G y z := by
  have hext (R : TripleSystemOn V) (t : VortexProfile ell) :
      W.profiledExtensions G R t ⊆ W.profiledExtensions F R t := by
    intro E hE
    have hh := (W.mem_profiledExtensions_iff G R t E).mp hE
    exact (W.mem_profiledExtensions_iff F R t E).mpr ⟨hGF hh.1, hh.2⟩
  refine ⟨h.order, h.terminal_nonempty, fun E hE ↦ h.uniform E (hGF hE), ?_, ?_, ?_, ?_⟩
  · intro R t hR hcard
    exact (show ((W.profiledExtensions G R t).card : ℝ≥0) ≤
        (W.profiledExtensions F R t).card by exact_mod_cast card_le_card (hext R t)).trans
      (h.extensions R t hR hcard)
  · intro T T' t
    apply le_trans _ (h.equal_remainders T T' t)
    exact_mod_cast card_le_card (show W.profiledDistinctEqualRemainderPairs G T T' t ⊆
        W.profiledDistinctEqualRemainderPairs F T T' t from fun p hp ↦ by
      have hh := (W.mem_profiledDistinctEqualRemainderPairs_iff G T T' t p).mp hp
      exact (W.mem_profiledDistinctEqualRemainderPairs_iff F T T' t p).mpr
        ⟨hGF hh.1, hGF hh.2.1, hh.2.2⟩)
  · intro hj T P hP
    apply le_trans _ (h.order_four_pair hj T P hP)
    exact_mod_cast card_le_card (show W.terminalPairExtensions G T P ⊆ W.terminalPairExtensions F T P from
      fun E hE ↦ by
        have hh := (W.mem_terminalPairExtensions_iff G T P E).mp hE
        exact (W.mem_terminalPairExtensions_iff F T P E).mpr ⟨hGF hh.1, hh.2⟩)
  · intro T t
    exact (show ((W.profiledExtensions G {T} t).card : ℝ≥0) ≤
        (W.profiledExtensions F {T} t).card by exact_mod_cast card_le_card (hext {T} t)).trans
      (h.singleton_extensions T t)

end

end Erdos207
