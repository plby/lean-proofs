/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCommonExtension

/-! # The generalized common-threat tail for a pair of fixed source orders -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localizedCommon_source_tail_additive
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell q r s t : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (hr : r ≤ q) (hs : s ≤ q) (hidentical : r = s → F = G)
    (T T' : TripleOn V) (w : ℝ≥0) (hw : 1 ≤ w)
    (L : FiniteLaw Ω) (J J' : Ω → ForbiddenFamilyOn V) (S : Ω → GreedyStateOn V)
    (available old : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦ Disjoint (available x) (old x) ∧
      (∀ U ∈ available x, W.level U = Fin.last ell) ∧
      (∀ C ∈ J x, C ⊆ available x ∧ ∃ E ∈ F, C ⊆ E ∧ E \ C ⊆ old x) ∧
      (∀ C ∈ J' x, C ⊆ available x ∧ ∃ E ∈ G, C ⊆ E ∧ E \ C ⊆ old x)))
    (A epsilon K : ℝ≥0) (hK : 0 < K)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ t * (2 * q) →
      L.probability (fun x ↦ H ⊆ old x ∪ (S x).chosen) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon) :
    L.probability (fun x ↦ K ≤ ((greedyCommonThreatPairs (J x) (J' x) (S x) T T').card : ℝ≥0)) ≤
      A * (((boundedIntersectionMomentCoefficient (2 * q) t : ℝ≥0) *
        sourceCommonMomentCoefficient ell q r w z z') / K) ^ t +
      epsilon * (((q + 1 : ℝ≥0) * (Fintype.card V + 1 : ℝ≥0) ^ (6 * q)) / K) ^ t := by
  let rem := fun u : sourceCommonThreats W F G T T' ↦ u.1.remainder
  let selected := fun x ↦ old x ∪ (S x).chosen
  let X := fun x ↦ ((greedyCommonThreatPairs (J x) (J' x) (S x) T T').card : ℝ≥0)
  have hdom : L.SupportedOn (fun x ↦ X x ≤ selectedCount rem (selected x)) := by
    intro x hx
    have hd := hstate x hx
    exact localizedCommonThreatPairs_card_le_source W F G (J x) (J' x) (S x) T T'
      (available x) (old x) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
  have hcard : ∀ u, (rem u).card ≤ 2 * q := by
    intro u
    have hc := u.1.remainder_card
    have hf := (hF.uniform u.1.first u.1.first_mem).1
    have hg := (hG.uniform u.1.second u.1.second_mem).1
    dsimp only [rem]
    omega
  apply (dominatedConfigurationTailBound_additive L rem selected X (vortexTripleWeight W w)
    A epsilon _ K hdom hcard (sourceCommon_hasExtensionBound hF hG hr hs hidentical T T' w hw)
    hK hjoint).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  apply div_le_div_of_nonneg_right _ zero_le
  rw [Fintype.card_coe]
  exact_mod_cast card_sourceCommonThreats_le_polynomial W F G T T'
    (fun E hE ↦ (hF.uniform E hE).1) (fun E hE ↦ (hG.uniform E hE).1) hr hs

end

end Erdos207
