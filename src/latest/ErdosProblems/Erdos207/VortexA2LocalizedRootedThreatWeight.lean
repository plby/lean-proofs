/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexAbsorberSingletonCount
import ErdosProblems.Erdos207.LocalizedMasterUnionRootedThreatWeight

/-!
# Bank-independent localized rooted-threat extension bounds

The sharp A2 version of W1 has coefficient `O(|U_k|)`, independently of the
full absorber bank.  Summing the injective rooted-threat code contributes the
number of allowed third vertices in the next vortex level.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The all-root coefficient in the multiplier-at-least-one regime. -/
def localizedRootedThreatVortexA2LargeCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (W : Vortex V (m + 1)) (q M : ℕ) (c : ℝ≥0) (a : ℕ) : ℝ≥0 :=
  ∑ j : IndexedThreatOrder q,
    (((j.1 + 1) ^ (m + 1) *
      ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
        W.terminalSize) : ℕ) : ℝ≥0) * c ^ (j.1 - 2 - a)

/-- Uniform A2 extension bound for localized rooted threats when the vortex
multiplier is at least one. -/
theorem localizedRootedThreatRemainder_hasExtensionBound_vortex_A2_of_one_le
    {V : Type*} [Fintype V] [DecidableEq V] {m q M : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (c : ℝ≥0) (hc : 1 ≤ c)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ W.U 1, x ∉ X → x ∉ graphSupportFinset H)
    (houter : ∀ i : Fin (m + 1), 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
        localizedRootedThreatRemainder z)
      (vortexTripleWeight W c)
      ((U.card : ℝ≥0) *
        localizedRootedThreatVortexA2LargeCoefficient W q M c 0) := by
  intro A
  let p : TripleOn V → ℝ≥0 := vortexTripleWeight W c
  calc
    extensionWeight
        (fun z : LocalizedRootedThreatWitness V
            (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
          localizedRootedThreatRemainder z) p A ≤
      ∑ code : LocalizedIndexedRootedThreatCode V q B u v U,
        localizedIndexedRootedThreatCodeWeight p A code :=
      localizedRootedThreat_weight_le_code p A
    _ = ∑ T : LocalizedUniverseTriplesThroughPair V u v U,
        ∑ j : IndexedThreatOrder q,
          extensionWeight
            (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
            p (insert T.1.1 A) :=
      sum_localizedIndexedRootedThreatCodeWeight_eq p A
    _ ≤ ∑ _T : LocalizedUniverseTriplesThroughPair V u v U,
        localizedRootedThreatVortexA2LargeCoefficient W q M c A.card := by
      apply sum_le_sum
      intro T _hT
      unfold localizedRootedThreatVortexA2LargeCoefficient
      apply sum_le_sum
      intro j _hj
      by_cases hrootcard : (insert T.1.1 A).card ≤ j.1 - 2
      · have hsharp :=
          extensionWeight_absorberInduced_vortex_nonempty_le_sharpA2
            (q := q) (j := j.1) W H X B c hA2 hsep
              (mem_Icc.mp j.2).1 (mem_Icc.mp j.2).2
              houter hterminal hbank (insert T.1.1 A) (by simp) hrootcard
        apply hsharp.trans
        have hExp : j.1 - 2 - (insert T.1.1 A).card ≤
            j.1 - 2 - A.card := by
          have hinsert : A.card ≤ (insert T.1.1 A).card :=
            card_le_card (subset_insert _ _)
          omega
        simpa only [mul_comm] using
          mul_le_mul_left (pow_le_pow_right₀ hc hExp)
            ((((j.1 + 1) ^ (m + 1) *
              ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
                W.terminalSize) : ℕ) : ℝ≥0))
      · have hzero :
            extensionWeight
                (fun S : absorberInducedConfigurationsOn q j.1 B ↦ S.1)
                p (insert T.1.1 A) = 0 := by
          unfold extensionWeight
          apply sum_eq_zero
          intro S _hS
          rw [if_neg]
          intro hsub
          apply hrootcard
          calc
            (insert T.1.1 A).card ≤ S.1.card := card_le_card hsub
            _ = j.1 - 2 :=
              (mem_absorberInducedConfigurationsOn_iff.mp S.2).1
        rw [hzero]
        exact bot_le
    _ = (Fintype.card
          (LocalizedUniverseTriplesThroughPair V u v U) : ℝ≥0) *
        localizedRootedThreatVortexA2LargeCoefficient W q M c A.card := by
      rw [sum_const, card_univ]
      simp only [nsmul_eq_mul]
    _ ≤ (U.card : ℝ≥0) *
        localizedRootedThreatVortexA2LargeCoefficient W q M c A.card := by
      gcongr
      exact_mod_cast card_localizedUniverseTriplesThroughPair_le V huv U
    _ ≤ (U.card : ℝ≥0) *
        localizedRootedThreatVortexA2LargeCoefficient W q M c 0 := by
      gcongr
      unfold localizedRootedThreatVortexA2LargeCoefficient
      apply sum_le_sum
      intro j _hj
      have hExp : j.1 - 2 - A.card ≤ j.1 - 2 - 0 := by omega
      simpa only [mul_comm] using
        mul_le_mul_left (pow_le_pow_right₀ hc hExp)
          ((((j.1 + 1) ^ (m + 1) *
            ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
              W.terminalSize) : ℕ) : ℝ≥0))

/-- A2-sharp localized extension bound for the exact master-union weight at
a positive vortex endpoint. -/
theorem localizedRootedThreatRemainder_hasExtensionBound_masterUnion_A2
    {V : Type*} [Fintype V] [DecidableEq V] {ell q M : ℕ}
    (W : Vortex V ell) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (i : Fin ell) (p : ℝ≥0) (hp : p ≤ 1)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ W.U 1, x ∉ X → x ∉ graphSupportFinset H)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
        localizedRootedThreatRemainder z)
      (masterUnionTriangleWeight W i.succ p)
      ((U.card : ℝ≥0) *
        localizedRootedThreatVortexA2LargeCoefficient
          (W.prefix i.succ) q M 2 0) := by
  have houter : ∀ j : Fin (i.val + 1),
      0 < ((W.prefix i.succ).U j.castSucc).card := by
    intro j
    exact card_pos.mpr (hnonempty _)
  have hterminal : 0 < (W.prefix i.succ).terminalSize := by
    rw [W.prefix_terminalSize i.succ]
    exact card_pos.mpr (hnonempty i.succ)
  have hsepPrefix : ∀ x ∈ (W.prefix i.succ).U 1,
      x ∉ X → x ∉ graphSupportFinset H := by
    intro x hx hxX
    have hemb : vortexPrefixEmbedding i.succ
        (1 : Fin (i.succ.val + 1)) = (1 : Fin (ell + 1)) := by
      have hsrc : ((1 : Fin (i.succ.val + 1)).val) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by
          have hisucc : 0 < i.succ.val := by
            simp only [Fin.val_succ]
            omega
          omega)
      have htgt : ((1 : Fin (ell + 1)).val) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by
          have hi : 0 < ell := Nat.zero_lt_of_lt i.isLt
          omega)
      apply Fin.ext
      rw [vortexPrefixEmbedding_val, hsrc, htgt]
    exact hsep x (by simpa only [Vortex.prefix_U, hemb] using hx) hxX
  have hbankPrefix : (subsetsUpToCard B q).card ≤
      ((W.prefix i.succ).U 0).card := by
    have hemb : vortexPrefixEmbedding i.succ
        (0 : Fin (i.succ.val + 1)) = (0 : Fin (ell + 1)) := by
      apply Fin.ext
      rfl
    simpa only [Vortex.prefix_U, hemb] using hbank
  apply (localizedRootedThreatRemainder_hasExtensionBound_vortex_A2_of_one_le
    (W.prefix i.succ) H X B 2 (by norm_num) hA2 hsepPrefix
      houter hterminal hbankPrefix huv U).mono_weight
  exact masterUnionTriangleWeight_le_prefix_vortex_two
    W i.succ p hp hnonempty

/-- A2-sharp localized extension bound after adding one ambient-inverse
point weight.  This is the binomial weight needed when a master packing is
selected before the last preliminary stage. -/
theorem localizedRootedThreatRemainder_hasExtensionBound_masterUnion_add_ambient_A2
    {V : Type*} [Fintype V] [DecidableEq V] {ell q M : ℕ}
    (W : Vortex V ell) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (i : Fin ell) (p : ℝ≥0) (hp : p ≤ 1)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ W.U 1, x ∉ X → x ∉ graphSupportFinset H)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
        localizedRootedThreatRemainder z)
      (fun T ↦ masterUnionTriangleWeight W i.succ p T +
        (Fintype.card V : ℝ≥0)⁻¹)
      ((U.card : ℝ≥0) *
        localizedRootedThreatVortexA2LargeCoefficient
          (W.prefix i.succ) q M 3 0) := by
  have houter : ∀ j : Fin (i.val + 1),
      0 < ((W.prefix i.succ).U j.castSucc).card := by
    intro j
    exact card_pos.mpr (hnonempty _)
  have hterminal : 0 < (W.prefix i.succ).terminalSize := by
    rw [W.prefix_terminalSize i.succ]
    exact card_pos.mpr (hnonempty i.succ)
  have hsepPrefix : ∀ x ∈ (W.prefix i.succ).U 1,
      x ∉ X → x ∉ graphSupportFinset H := by
    intro x hx hxX
    have hemb : vortexPrefixEmbedding i.succ
        (1 : Fin (i.succ.val + 1)) = (1 : Fin (ell + 1)) := by
      have hsrc : ((1 : Fin (i.succ.val + 1)).val) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by
          have hisucc : 0 < i.succ.val := by
            simp only [Fin.val_succ]
            omega
          omega)
      have htgt : ((1 : Fin (ell + 1)).val) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by
          have hi : 0 < ell := Nat.zero_lt_of_lt i.isLt
          omega)
      apply Fin.ext
      rw [vortexPrefixEmbedding_val, hsrc, htgt]
    exact hsep x (by simpa only [Vortex.prefix_U, hemb] using hx) hxX
  have hbankPrefix : (subsetsUpToCard B q).card ≤
      ((W.prefix i.succ).U 0).card := by
    have hemb : vortexPrefixEmbedding i.succ
        (0 : Fin (i.succ.val + 1)) = (0 : Fin (ell + 1)) := by
      apply Fin.ext
      rfl
    simpa only [Vortex.prefix_U, hemb] using hbank
  apply (localizedRootedThreatRemainder_hasExtensionBound_vortex_A2_of_one_le
    (W.prefix i.succ) H X B 3 (by norm_num) hA2 hsepPrefix
      houter hterminal hbankPrefix huv U).mono_weight
  exact masterUnionTriangleWeight_add_ambient_le_prefix_vortex_three
    W i.succ p hp hnonempty

end

end Erdos207
