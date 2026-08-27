/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedOmissionCode

/-! # The first actual generalized-nibble crude tail from fixed source well-spreadness -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localizedRooted_source_tail_additive
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j j' c s : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hF : SourceVortexWellSpread W j' F y z) (Q : TripleSystemOn V) (hQ : Q.card = 2)
    (hc : c + 5 ≤ j) (hjj : j ≤ j') (w : ℝ≥0) (hw : 1 ≤ w)
    (L : FiniteLaw Ω) (J processF : Ω → ForbiddenFamilyOn V) (S : Ω → GreedyStateOn V)
    (available old : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦ GreedyInvariant (processF x) (S x) ∧
      (∀ T ∈ (S x).available, W.level T = Fin.last ell) ∧ Disjoint (available x) (old x) ∧
      J x ⊆ localForbiddenConfigurations F (available x) (old x) j))
    (A epsilon K : ℝ≥0) (hK : 0 < K)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ s * (j' - j + c) →
      L.probability (fun x ↦ H ⊆ old x ∪ (S x).chosen) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon) :
    let f := j' - j + c
    let kappa := (((f + 1) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ (j' - 2) * z) * w ^ f *
      (W.terminalSize : ℝ≥0) ^ (j - c - 5)
    L.probability (fun x ↦ K ≤ ((greedyRootedConfigurationClass (J x) (S x) Q c).card : ℝ≥0)) ≤
      A * (((boundedIntersectionMomentCoefficient f s : ℝ≥0) * kappa) / K) ^ s +
        epsilon * (((2 : ℝ≥0) ^ j' * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j')) / K) ^ s := by
  dsimp only
  let rem := fun u : terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) (j' - j + c) ↦ u.1.2
  let selected := fun x ↦ old x ∪ (S x).chosen
  let X := fun x ↦ ((greedyRootedConfigurationClass (J x) (S x) Q c).card : ℝ≥0)
  have hdom : L.SupportedOn (fun x ↦ X x ≤ selectedCount rem (selected x)) := by
    intro x hx
    have hs := hstate x hx
    exact localizedRooted_card_le_source_selectedCount W F (J x) (processF x) (S x) Q (available x) (old x)
      (by omega) hjj (fun E hE ↦ (hF.uniform E hE).1) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have hcard : ∀ u, (rem u).card ≤ j' - j + c := fun u ↦
    (mem_terminalRemainderChoices_iff.mp (mem_terminalOmissionCodes_iff.mp u.2).2).2.1.le
  have hfit : Q.card + (j' - j + c) + 3 ≤ j' := by rw [hQ]; omega
  have hexp : j' - Q.card - 3 - (j' - j + c) = j - c - 5 := by rw [hQ]; omega
  have hkappa := hF.root_omission_hasExtensionBound Q (by omega) hfit w hw
  rw [hexp] at hkappa
  apply (dominatedConfigurationTailBound_additive L rem selected X (vortexTripleWeight W w)
    A epsilon _ K hdom hcard hkappa hK hjoint).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  apply div_le_div_of_nonneg_right _ zero_le
  rw [Fintype.card_coe]
  exact_mod_cast card_sourceRootOmissionCodes_le_polynomial W F Q j' (j' - j + c)
    (fun E hE ↦ (hF.uniform E hE).1)

end

end Erdos207
