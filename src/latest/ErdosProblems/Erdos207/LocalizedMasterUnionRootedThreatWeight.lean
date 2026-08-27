/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StructuredInitialData
import ErdosProblems.Erdos207.VortexLocalizedRootedThreatWeight
import ErdosProblems.Erdos207.VortexFullTerminalMoment
import ErdosProblems.Erdos207.RelativeExtensionMonotonicity
import ErdosProblems.Erdos207.StrongWellDistributedUnion

/-!
# Localized rooted threats for the first master-union weight

The initial master weight is the sum of the ambient initial density and the
truncated later-stage density.  On the vortex prefix ending at the current
level, both summands are at most the reciprocal of the prefix-level set.
Thus the master weight is pointwise dominated by the prefix vortex weight
with multiplier two.  Combining this observation with the localized rooted
threat count gives the quantitative input required at the first compressed
transition.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Computing a triangle level in the prefix and embedding it back into the
full vortex gives the full level truncated at the endpoint of the prefix. -/
lemma Vortex.prefix_level_embedding_eq_truncatedLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (T : TripleOn V) :
    vortexPrefixEmbedding k ((W.prefix k).level T) =
      W.truncatedLevel k T := by
  apply le_antisymm
  · apply le_min
    · apply W.le_level_of_subset T
      simpa only [Vortex.prefix_U] using (W.prefix k).subset_at_level T
    · change ((W.prefix k).level T).val ≤ k.val
      omega
  · let t : Fin (k.val + 1) :=
      ⟨(W.truncatedLevel k T).val, by
        have ht := W.truncatedLevel_le k T
        omega⟩
    have htEmbed : vortexPrefixEmbedding k t = W.truncatedLevel k T := by
      apply Fin.ext
      rfl
    have htSubset : T.1 ⊆ (W.prefix k).U t := by
      change T.1 ⊆ W.U (vortexPrefixEmbedding k t)
      rw [htEmbed]
      exact (W.subset_iff_le_level T (W.truncatedLevel k T)).mpr
        (min_le_left _ _)
    have htLevel : t ≤ (W.prefix k).level T :=
      (W.prefix k).le_level_of_subset T t htSubset
    change t.val ≤ ((W.prefix k).level T).val at htLevel
    change (W.truncatedLevel k T).val ≤
      ((W.prefix k).level T).val
    simpa only [t] using htLevel

lemma Vortex.prefix_U_level_eq_truncatedLevel
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (T : TripleOn V) :
    (W.prefix k).U ((W.prefix k).level T) =
      W.U (W.truncatedLevel k T) := by
  change W.U (vortexPrefixEmbedding k ((W.prefix k).level T)) = _
  rw [W.prefix_level_embedding_eq_truncatedLevel k T]

/-- The master-union point weight at a prefix endpoint is dominated by the
vortex weight with multiplier two on that prefix. -/
theorem masterUnionTriangleWeight_one_le_prefix_vortex_two
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1))
    (hnonempty : ∀ j, (W.U j).Nonempty) (T : TripleOn V) :
    masterUnionTriangleWeight W k 1 T ≤
      vortexTripleWeight (W.prefix k) 2 T := by
  have hcard : (W.U (W.truncatedLevel k T)).card ≤ Fintype.card V := by
    rw [← card_univ]
    exact card_le_card (subset_univ _)
  have hden : (0 : ℝ≥0) < (W.U (W.truncatedLevel k T)).card := by
    exact_mod_cast card_pos.mpr (hnonempty (W.truncatedLevel k T))
  have hinv : (Fintype.card V : ℝ≥0)⁻¹ ≤
      ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ := by
    apply inv_anti₀ hden
    exact_mod_cast hcard
  unfold masterUnionTriangleWeight vortexTripleWeight
  rw [W.prefix_U_level_eq_truncatedLevel k T]
  calc
    (Fintype.card V : ℝ≥0)⁻¹ +
          1 / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) ≤
        ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ +
          ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ := by
      simpa only [one_div] using add_le_add hinv le_rfl
    _ = 2 / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) := by
      rw [div_eq_mul_inv, show (2 : ℝ≥0) = 1 + 1 by norm_num]
      ring

/-- The same domination with an arbitrary later-stage multiplier at most
one. -/
theorem masterUnionTriangleWeight_le_prefix_vortex_two
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0) (hp : p ≤ 1)
    (hnonempty : ∀ j, (W.U j).Nonempty) (T : TripleOn V) :
    masterUnionTriangleWeight W k p T ≤
      vortexTripleWeight (W.prefix k) 2 T := by
  have hcard : (W.U (W.truncatedLevel k T)).card ≤ Fintype.card V := by
    rw [← card_univ]
    exact card_le_card (subset_univ _)
  have hden : (0 : ℝ≥0) < (W.U (W.truncatedLevel k T)).card := by
    exact_mod_cast card_pos.mpr (hnonempty (W.truncatedLevel k T))
  have hinv : (Fintype.card V : ℝ≥0)⁻¹ ≤
      ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ := by
    apply inv_anti₀ hden
    exact_mod_cast hcard
  have hpdiv : p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) ≤
      ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ := by
    rw [← one_div]
    gcongr
  unfold masterUnionTriangleWeight vortexTripleWeight
  rw [W.prefix_U_level_eq_truncatedLevel k T]
  calc
    (Fintype.card V : ℝ≥0)⁻¹ +
          p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) ≤
        ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ +
          ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ :=
      add_le_add hinv hpdiv
    _ = 2 / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) := by
      rw [div_eq_mul_inv, show (2 : ℝ≥0) = 1 + 1 by norm_num]
      ring

/-- After adding one further ambient inverse factor, the master-union
weight is dominated by multiplier three on the endpoint prefix. -/
theorem masterUnionTriangleWeight_add_ambient_le_prefix_vortex_three
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0) (hp : p ≤ 1)
    (hnonempty : ∀ j, (W.U j).Nonempty) (T : TripleOn V) :
    masterUnionTriangleWeight W k p T + (Fintype.card V : ℝ≥0)⁻¹ ≤
      vortexTripleWeight (W.prefix k) 3 T := by
  have hcard : (W.U (W.truncatedLevel k T)).card ≤ Fintype.card V := by
    rw [← card_univ]
    exact card_le_card (subset_univ _)
  have hden : (0 : ℝ≥0) < (W.U (W.truncatedLevel k T)).card := by
    exact_mod_cast card_pos.mpr (hnonempty (W.truncatedLevel k T))
  have hinv : (Fintype.card V : ℝ≥0)⁻¹ ≤
      ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ := by
    apply inv_anti₀ hden
    exact_mod_cast hcard
  have htwo := masterUnionTriangleWeight_le_prefix_vortex_two
    W k p hp hnonempty T
  unfold vortexTripleWeight at htwo ⊢
  rw [W.prefix_U_level_eq_truncatedLevel k T] at htwo ⊢
  calc
    masterUnionTriangleWeight W k p T + (Fintype.card V : ℝ≥0)⁻¹ ≤
        2 / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) +
          ((W.U (W.truncatedLevel k T)).card : ℝ≥0)⁻¹ :=
      add_le_add htwo hinv
    _ = 3 / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) := by
      rw [div_eq_mul_inv, show (3 : ℝ≥0) = 2 + 1 by norm_num]
      ring

/-- The ambient inverse term in every master-union point weight gives a
uniform lower bound for all products of bounded cardinality. -/
theorem ambientInversePow_le_setWeight_masterUnion
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0)
    (hnonempty : (W.U k).Nonempty) (K : ℕ)
    (T : TripleSystemOn V) (hcard : T.card ≤ K) :
    (Fintype.card V : ℝ≥0)⁻¹ ^ K ≤
      setWeight (masterUnionTriangleWeight W k p) T := by
  have hVcard : 1 ≤ Fintype.card V := by
    have hVposNat : 0 < Fintype.card V :=
      Fintype.card_pos_iff.mpr ⟨hnonempty.choose⟩
    omega
  have hVpos : (0 : ℝ≥0) < Fintype.card V := by
    exact_mod_cast (show 0 < Fintype.card V by omega)
  have hinv : (Fintype.card V : ℝ≥0)⁻¹ ≤ 1 :=
    (inv_le_one₀ hVpos).2 (by exact_mod_cast hVcard)
  calc
    (Fintype.card V : ℝ≥0)⁻¹ ^ K ≤
        (Fintype.card V : ℝ≥0)⁻¹ ^ T.card :=
      pow_le_pow_right_of_le_one' hinv hcard
    _ = setWeight (fun _ : TripleOn V ↦
          (Fintype.card V : ℝ≥0)⁻¹) T := by
      simp only [setWeight, prod_const]
    _ ≤ setWeight (masterUnionTriangleWeight W k p) T := by
      apply setWeight_mono_pointwise
      intro S
      unfold masterUnionTriangleWeight
      exact le_add_of_nonneg_right zero_le

/-- Explicit localized rooted extension bound for the exact initial
master-union point weight. -/
theorem localizedRootedThreatRemainder_hasExtensionBound_masterUnion_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (k : Fin (ell + 1)) (hnonempty : ∀ j, (W.U j).Nonempty)
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
        localizedRootedThreatRemainder z)
      (masterUnionTriangleWeight W k 1)
      ((U.card : ℝ≥0) *
        localizedRootedThreatVortexLargeCoefficient
          (W.prefix k) q B 2 0) := by
  have houter : ∀ i : Fin k.val,
      0 < ((W.prefix k).U i.castSucc).card := by
    intro i
    exact card_pos.mpr (hnonempty _)
  have hterminal : 0 < (W.prefix k).terminalSize := by
    rw [W.prefix_terminalSize k]
    exact card_pos.mpr (hnonempty k)
  apply (localizedRootedThreatRemainder_hasExtensionBound_vortex_of_one_le
    (W.prefix k) B 2 (by norm_num) houter hterminal huv U).mono_weight
  exact masterUnionTriangleWeight_one_le_prefix_vortex_two W k hnonempty

/-- Explicit localized rooted extension bound for every master-union point
weight whose later-stage multiplier is at most one. -/
theorem localizedRootedThreatRemainder_hasExtensionBound_masterUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (k : Fin (ell + 1)) (p : ℝ≥0) (hp : p ≤ 1)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    {u v : V} (huv : u ≠ v) (U : Finset V) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v U ↦
        localizedRootedThreatRemainder z)
      (masterUnionTriangleWeight W k p)
      ((U.card : ℝ≥0) *
        localizedRootedThreatVortexLargeCoefficient
          (W.prefix k) q B 2 0) := by
  have houter : ∀ i : Fin k.val,
      0 < ((W.prefix k).U i.castSucc).card := by
    intro i
    exact card_pos.mpr (hnonempty _)
  have hterminal : 0 < (W.prefix k).terminalSize := by
    rw [W.prefix_terminalSize k]
    exact card_pos.mpr (hnonempty k)
  apply (localizedRootedThreatRemainder_hasExtensionBound_vortex_of_one_le
    (W.prefix k) B 2 (by norm_num) houter hterminal huv U).mono_weight
  exact masterUnionTriangleWeight_le_prefix_vortex_two W k p hp hnonempty

/-- Explicit full rooted-threat extension bound for a master-union point
weight with later multiplier at most one. -/
theorem rootedThreatRemainder_hasExtensionBound_masterUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell q : ℕ} (W : Vortex V ell) (B : TripleSystemOn V)
    (k : Fin (ell + 1)) (p : ℝ≥0) (hp : p ≤ 1)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    {u v : V} (huv : u ≠ v) :
    HasExtensionBound
      (fun z : RootedThreatWitness V
          (absorberErdosForbiddenConfigurationsOn q B) u v ↦
        rootedThreatRemainder z)
      (masterUnionTriangleWeight W k p)
      ((Fintype.card V : ℝ≥0) *
        indexedRootedThreatVortexLargeCoefficient
          (W.prefix k) q B 2 0) := by
  have houter : ∀ i : Fin k.val,
      0 < ((W.prefix k).U i.castSucc).card := by
    intro i
    exact card_pos.mpr (hnonempty _)
  have hterminal : 0 < (W.prefix k).terminalSize := by
    rw [W.prefix_terminalSize k]
    exact card_pos.mpr (hnonempty k)
  apply (rootedThreatRemainder_hasExtensionBound_vortex_noFour_of_one_le
    (W.prefix k) B 2 (by norm_num) houter hterminal huv).mono_weight
  exact masterUnionTriangleWeight_le_prefix_vortex_two W k p hp hnonempty

end

end Erdos207
