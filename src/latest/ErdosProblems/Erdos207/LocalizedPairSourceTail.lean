/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedPairSourceCode

/-! # Generalized pair-threat tails, retaining the prior-law error -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_sourcePinnedEdgeCodes_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j : ℕ) (e : Sym2 V)
    (huniform : ∀ E ∈ F, E.card = j - 2) :
    (sourcePinnedEdgeCodes W F T j e).card ≤ 2 ^ j * (Fintype.card V + 1) ^ (3 * j) :=
  (card_le_card (filter_subset _ _)).trans
    (card_sourceNibbleCodes_le_polynomial W F T 4 j huniform)

theorem localizedPair_source_tail_additive
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j s : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hF : SourceVortexWellSpread W j F y z) (T : TripleOn V) (P : PairOn V)
    (w : ℝ≥0) (hw : 1 ≤ w) (L : FiniteLaw Ω) (J : Ω → ForbiddenFamilyOn V)
    (available old selected : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦
      (∀ U ∈ available x, W.level U = Fin.last ell) ∧ Disjoint (available x) (old x) ∧
      ∀ C ∈ J x, C ⊆ available x ∧ ∃ E ∈ F, C ⊆ E ∧ E \ C ⊆ old x))
    (A epsilon K : ℝ≥0) (hK : 0 < K)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ s * (j - 4) →
      L.probability (fun x ↦ H ⊆ old x ∪ selected x) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon) :
    L.probability (fun x ↦ K ≤ selectedCount
      (fun u : PairTwoAwayThreatWitness V (J x) T P ↦ pairTwoAwayThreatRemainder u) (selected x)) ≤
      A * (((boundedIntersectionMomentCoefficient (j - 4) s : ℝ≥0) *
        (sourceNibbleMomentCoefficient ell j w * z)) / K) ^ s +
      epsilon * (((2 : ℝ≥0) ^ j * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j)) / K) ^ s := by
  obtain ⟨e, he, heP⟩ := pairOn_exists_nondiagonal_edge P
  let rem := fun u : sourcePinnedEdgeCodes W F T j e ↦ u.1.2
  let chosen := fun x ↦ old x ∪ selected x
  let X := fun x ↦ selectedCount
    (fun u : PairTwoAwayThreatWitness V (J x) T P ↦ pairTwoAwayThreatRemainder u) (selected x)
  have hdom : L.SupportedOn (fun x ↦ X x ≤ selectedCount rem (chosen x)) := by
    intro x hx
    have hs := hstate x hx
    exact localizedPair_selectedCount_le_source W F (J x) T P (available x) (old x) (selected x)
      e he heP (fun E hE ↦ (hF.uniform E hE).1) hs.1 hs.2.1 hs.2.2
  have hcard : ∀ u, (rem u).card ≤ j - 4 := fun u ↦
    (sourceNibbleCode_data (mem_filter.mp u.2).1).2.2.2.1.le
  apply (dominatedConfigurationTailBound_additive L rem chosen X (vortexTripleWeight W w)
    A epsilon _ K hdom hcard (hF.pinned_edge_hasExtensionBound T e w hw) hK hjoint).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  apply div_le_div_of_nonneg_right _ zero_le
  rw [Fintype.card_coe]
  exact_mod_cast card_sourcePinnedEdgeCodes_le_polynomial W F T j e (fun E hE ↦ (hF.uniform E hE).1)

end

end Erdos207
