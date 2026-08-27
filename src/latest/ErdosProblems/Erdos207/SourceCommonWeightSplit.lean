/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCommonGoodWeight
import ErdosProblems.Erdos207.SourceCommonExceptionalWeight

/-! # The exhaustive common-threat split with nonuniform vortex weights -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceCommonExceptionalWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (H : TripleSystemOn V) (w : ℝ≥0) : ℝ≥0 :=
  ∑ u : CommonThreatWitness F G T T',
    if W.level u.bridge = Fin.last ell ∧ H = ∅ ∧ u.first.erase T = u.second.erase T' then
      setWeight (vortexTripleWeight W w) (u.remainder \ H) else 0

theorem sourceCommonGoodWeight_sum
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (H : TripleSystemOn V) (r s : ℕ) (w : ℝ≥0) :
    sourceCommonGoodWeight W F G T T' H r s w =
      ∑ u : CommonThreatWitness F G T T',
        if W.level u.bridge = Fin.last ell ∧ H ⊆ u.remainder ∧ (u.exposureCode H).IsGood H r s then
          setWeight (vortexTripleWeight W w) (u.remainder \ H) else 0 := by
  simp only [sourceCommonGoodWeight, sourceCommonThreats, filter_filter, sum_filter]

theorem sourceCommonGoodWeight_swap_eq
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (H : TripleSystemOn V) (r s : ℕ) (w : ℝ≥0) :
    sourceCommonGoodWeight W G F T' T H s r w =
      ∑ u : CommonThreatWitness F G T T',
        if W.level u.bridge = Fin.last ell ∧ H ⊆ u.remainder ∧ (u.swap.exposureCode H).IsGood H s r then
          setWeight (vortexTripleWeight W w) (u.remainder \ H) else 0 := by
  rw [sourceCommonGoodWeight_sum]
  calc
    _ = ∑ u : CommonThreatWitness F G T T',
        if W.level u.swap.bridge = Fin.last ell ∧ H ⊆ u.swap.remainder ∧ (u.swap.exposureCode H).IsGood H s r then
          setWeight (vortexTripleWeight W w) (u.swap.remainder \ H) else 0 :=
      ((CommonThreatWitness.swapEquiv F G T T').sum_comp _).symm
    _ = _ := by simp only [CommonThreatWitness.swap_remainder]; rfl

theorem sourceCommon_extension_le_split
    {V : Type*} [Fintype V] [DecidableEq V] {ell r s : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (H : TripleSystemOn V) (w : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) :
    extensionWeight (fun u : sourceCommonThreats W F G T T' ↦ u.1.remainder) (vortexTripleWeight W w) H ≤
      sourceCommonGoodWeight W F G T T' H r s w + sourceCommonGoodWeight W G F T' T H s r w +
        sourceCommonExceptionalWeight W F G T T' H w := by
  classical
  rw [sourceCommonGoodWeight_swap_eq W F G T T' H r s w, sourceCommonGoodWeight_sum]
  unfold extensionWeight sourceCommonExceptionalWeight
  rw [← Finset.sum_subtype (sourceCommonThreats W F G T T')
    (p := fun u ↦ u ∈ sourceCommonThreats W F G T T') (fun _ ↦ Iff.rfl)
    (fun u ↦ if H ⊆ u.remainder then setWeight (vortexTripleWeight W w) (u.remainder \ H) else 0)]
  rw [sourceCommonThreats, sum_filter, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro u _hu
  by_cases hterm : W.level u.bridge = Fin.last ell
  · simp only [hterm, if_true, true_and]
    by_cases hH : H ⊆ u.remainder
    · simp only [hH, if_true, true_and]
      rcases u.good_or_swap_good_or_equal_remainders H r s hH
        (hF u.first u.first_mem) (hG u.second u.second_mem) with h | h | h
      · rw [if_pos h]
        exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
      · rw [if_pos h]
        exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
      · rw [if_pos (show H = ∅ ∧ u.first.erase T = u.second.erase T' from ⟨h.1, h.2.2⟩)]
        exact le_add_of_nonneg_left zero_le
    · simp only [hH, if_false, false_and]
      exact zero_le
  · simp only [hterm, if_false, false_and, zero_add, le_refl]

theorem sourceCommonExceptionalWeight_same_family
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hF : SourceVortexWellSpread W j F y z) (T T' : TripleOn V) (H : TripleSystemOn V) (w : ℝ≥0) :
    sourceCommonExceptionalWeight W F F T T' H w ≤
      (((j - 3) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ (j - 3) * z) * w ^ (j - 4) := by
  classical
  by_cases hH : H = ∅
  · subst H
    have heq : sourceCommonExceptionalWeight W F F T T' ∅ w =
        ∑ u : sourceExceptionalCommonThreats W F T T', setWeight (vortexTripleWeight W w) u.1.remainder := by
      rw [← Finset.sum_subtype (sourceExceptionalCommonThreats W F T T')
        (p := fun u ↦ u ∈ sourceExceptionalCommonThreats W F T T') (fun _ ↦ Iff.rfl)
        (fun u ↦ setWeight (vortexTripleWeight W w) u.remainder)]
      simp only [sourceCommonExceptionalWeight, sourceExceptionalCommonThreats, sourceCommonThreats,
        filter_filter, sum_filter, true_and, sdiff_empty]
    rw [heq]
    exact hF.exceptional_common_weight_le T T' w
  · simp only [sourceCommonExceptionalWeight, hH, false_and, and_false, if_false, sum_const_zero, zero_le]

theorem sourceCommonExceptionalWeight_zero_of_orders_ne
    {V : Type*} [Fintype V] [DecidableEq V] {ell r s : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (H : TripleSystemOn V) (w : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) (hrs : r ≠ s) :
    sourceCommonExceptionalWeight W F G T T' H w = 0 := by
  classical
  have hnot : ∀ u : CommonThreatWitness F G T T', u.first.erase T ≠ u.second.erase T' := by
    intro u heq
    have hc := congrArg Finset.card heq
    rw [card_erase_of_mem u.first_root, card_erase_of_mem u.second_root,
      hF u.first u.first_mem, hG u.second u.second_mem] at hc
    have hf : 0 < u.first.card := card_pos.mpr ⟨T, u.first_root⟩
    have hg : 0 < u.second.card := card_pos.mpr ⟨T', u.second_root⟩
    rw [hF u.first u.first_mem] at hf
    rw [hG u.second u.second_mem] at hg
    exact hrs (by omega)
  simp only [sourceCommonExceptionalWeight, hnot, and_false, if_false, sum_const_zero]

end

end Erdos207
