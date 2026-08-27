/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRootOmissionExtension
import ErdosProblems.Erdos207.SourceNibbleWitnessCard
import ErdosProblems.Erdos207.AdditiveConfigurationMoment

/-! # Source root-omission moments with polynomial control of the additive error -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem card_uniform_source_family_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] (F : ForbiddenFamilyOn V) (j : ℕ)
    (huniform : ∀ E ∈ F, E.card = j - 2) : F.card ≤ (Fintype.card V + 1) ^ (3 * j) := by
  have hsub : F ⊆ (univ : Finset (TripleOn V)).powersetCard (j - 2) :=
    fun E hE ↦ mem_powersetCard.mpr ⟨subset_univ E, huniform E hE⟩
  have hF : F.card ≤ (Fintype.card (TripleOn V)) ^ (j - 2) :=
    (card_le_card hsub).trans (by
      simpa only [card_powersetCard, card_univ] using Nat.choose_le_pow (Fintype.card (TripleOn V)) (j - 2))
  have htri : Fintype.card (TripleOn V) ≤ Fintype.card V ^ 3 := by
    rw [show Fintype.card (TripleOn V) = Nat.choose (Fintype.card V) 3 from Fintype.card_finset_len 3]
    exact Nat.choose_le_pow _ _
  apply (hF.trans (Nat.pow_le_pow_left htri _)).trans
  rw [← pow_mul]
  apply (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
  exact Nat.pow_le_pow_right (by omega) (by omega)

theorem card_sourceRootOmissionCodes_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (Q : TripleSystemOn V) (j f : ℕ)
    (huniform : ∀ E ∈ F, E.card = j - 2) :
    (terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f).card ≤
      2 ^ j * (Fintype.card V + 1) ^ (3 * j) := by
  have hcard : ∀ E ∈ familyExtensions F Q, (E \ Q).card ≤ j - 2 := by
    intro E hE
    exact (card_le_card sdiff_subset).trans_eq (huniform E (mem_familyExtensions_iff.mp hE).1)
  have hF : (familyExtensions F Q).card ≤ (Fintype.card V + 1) ^ (3 * j) :=
    (card_le_card (filter_subset _ _)).trans (card_uniform_source_family_le_polynomial F j huniform)
  apply (card_terminalOmissionCodes_le W (familyExtensions F Q) (fun E ↦ E \ Q) f (j - 2) hcard).trans
  simpa only [mul_comm] using Nat.mul_le_mul hF (Nat.pow_le_pow_right (by omega) (Nat.sub_le j 2))

theorem SourceVortexWellSpread.root_omission_moment_additive
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j f s : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (Q : TripleSystemOn V)
    (hQ : 2 ≤ Q.card) (hfit : Q.card + f + 3 ≤ j) (w : ℝ≥0) (hw : 1 ≤ w)
    (L : FiniteLaw Ω) (selected : Ω → TripleSystemOn V) (C epsilon : ℝ≥0)
    (hjoint : ∀ A : TripleSystemOn V, A.card ≤ s * f →
      L.probability (fun x ↦ A ⊆ selected x) ≤ C * setWeight (vortexTripleWeight W w) A + epsilon) :
    let kappa := (((f + 1) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ (j - 2) * z) * w ^ f *
      (W.terminalSize : ℝ≥0) ^ (j - Q.card - 3 - f)
    L.expectation (fun x ↦ selectedCount
      (fun u : terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f ↦ u.1.2)
      (selected x) ^ s) ≤
      C * ((boundedIntersectionMomentCoefficient f s : ℝ≥0) * kappa) ^ s +
        epsilon * ((2 : ℝ≥0) ^ j * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j)) ^ s := by
  dsimp only
  have hcard : ∀ u : terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) f,
      u.1.2.card ≤ f := fun u ↦
    (mem_terminalRemainderChoices_iff.mp (mem_terminalOmissionCodes_iff.mp u.2).2).2.1.le
  apply (configurationMomentBound_additive L _ selected (vortexTripleWeight W w) C epsilon _
    hcard (h.root_omission_hasExtensionBound Q hQ hfit w hw) hjoint).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  rw [Fintype.card_coe]
  exact_mod_cast card_sourceRootOmissionCodes_le_polynomial W F Q j f (fun E hE ↦ (h.uniform E hE).1)

end

end Erdos207
