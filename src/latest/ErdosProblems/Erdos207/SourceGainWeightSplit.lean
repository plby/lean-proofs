/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainGoodWeight
import ErdosProblems.Erdos207.SourceGainReverseGoodWeight
import ErdosProblems.Erdos207.SourceGainExceptionalWeight

/-! # Exhaustive source-correct splitting of gain-defect extension weights -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceGainExceptionalWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ)
    (H : TripleSystemOn V) (w : ℝ≥0) : ℝ≥0 :=
  ∑ u ∈ sourceGainExceptionalClass W F G T a H, setWeight (vortexTripleWeight W w) (u.remainder \ H)

theorem sourceGain_extension_le_split
    {V : Type*} [Fintype V] [DecidableEq V] {ell r s a : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V)
    (H : TripleSystemOn V) (w : ℝ≥0) (ha : 1 ≤ a)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) :
    extensionWeight (fun u : sourceGainDefects W F G T a ↦ u.1.remainder) (vortexTripleWeight W w) H ≤
      sourceGainGoodWeight W F G T a H r s w + sourceGainReverseGoodWeight W F G T a H r s w +
        sourceGainExceptionalWeight W F G T a H w := by
  classical
  unfold extensionWeight
  rw [← Finset.sum_subtype (sourceGainDefects W F G T a)
    (p := fun u ↦ u ∈ sourceGainDefects W F G T a) (fun _ ↦ Iff.rfl)
    (fun u ↦ if H ⊆ u.remainder then setWeight (vortexTripleWeight W w) (u.remainder \ H) else 0)]
  simp only [sourceGainGoodWeight, sourceGainReverseGoodWeight, sourceGainExceptionalWeight,
    sourceGainDefects, sourceGainExceptionalClass, gainDefectExceptionalClass, filter_filter, sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro u _hu
  by_cases hterm : ∀ U ∈ u.omittedRoot, W.level U = Fin.last ell
  · have ht : (∀ U ∈ u.omittedRoot, W.level U = Fin.last ell) ↔ True := iff_true_intro hterm
    simp only [ht, if_true, true_and, and_true]
    by_cases hH : H ⊆ u.remainder
    · simp only [hH, if_true, true_and]
      rcases u.exposure_three_way_split H hH ha r s
        (hF u.first u.first_mem) (hG u.second u.second_mem) with h | h | h
      · have hg : (u.exposureCode H).IsGood H r s := h
        rw [if_pos hg]
        exact (le_add_of_nonneg_right zero_le).trans (le_add_of_nonneg_right zero_le)
      · rw [if_pos h]
        exact (le_add_of_nonneg_left zero_le).trans (le_add_of_nonneg_right zero_le)
      · have he : u.ForwardExceptional H ∧ H.card = 1 ∧ T ∉ u.second ∧ u.second \ H = u.first.erase T :=
          ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩
        rw [if_pos he]
        exact le_add_of_nonneg_left zero_le
    · simp only [hH, if_false, false_and, zero_add, le_refl]
  · simp only [hterm, if_false, false_and, and_false, zero_add, le_refl]

theorem sourceGainExceptionalWeight_zero_of_orders_ne
    {V : Type*} [Fintype V] [DecidableEq V] {ell r s a : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V)
    (H : TripleSystemOn V) (w : ℝ≥0)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) (hrs : r ≠ s) :
    sourceGainExceptionalWeight W F G T a H w = 0 := by
  classical
  have hempty : sourceGainExceptionalClass W F G T a H = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hd := (mem_filter.mp (mem_filter.mp hu).1).2
    exact hrs (u.equal_remainders_orders_eq H hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.2
      r s (hF u.first u.first_mem) (hG u.second u.second_mem))
  rw [sourceGainExceptionalWeight, hempty, sum_empty]

theorem sourceGainExceptionalWeight_same_family
    {V : Type*} [Fintype V] [DecidableEq V] {ell j a : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hF : SourceVortexWellSpread W j F y z) (ha : 1 ≤ a)
    (T : TripleOn V) (H : TripleSystemOn V) (w : ℝ≥0) (hw : 1 ≤ w) :
    sourceGainExceptionalWeight W F F T a H w ≤
      ((((j + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ j * z * w ^ j) *
        (W.terminalSize : ℝ≥0) ^ (a - 1) := by
  rw [sourceGainExceptionalWeight, Finset.sum_subtype (sourceGainExceptionalClass W F F T a H)
    (p := fun u ↦ u ∈ sourceGainExceptionalClass W F F T a H) (fun _ ↦ Iff.rfl)]
  exact hF.exceptional_gain_weight_le ha T H w hw

def sourceGainMomentCoefficient (ell q r : ℕ) (w z z' : ℝ≥0) : ℝ≥0 :=
  sourceCommonGoodCoefficient ell q w z z' + sourceGainReverseGoodCoefficient ell q w z z' +
    (((r + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ r * z * w ^ r

theorem sourceGain_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell q r s a : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (hr : r ≤ q) (hs : s ≤ q) (hidentical : r = s → F = G) (ha : 1 ≤ a)
    (T : TripleOn V) (w : ℝ≥0) (hw : 1 ≤ w) :
    HasExtensionBound (fun u : sourceGainDefects W F G T a ↦ u.1.remainder) (vortexTripleWeight W w)
      (sourceGainMomentCoefficient ell q r w z z' * (W.terminalSize : ℝ≥0) ^ (a - 1)) := by
  intro H
  have he : sourceGainExceptionalWeight W F G T a H w ≤
      ((((r + 1) ^ ell : ℕ) : ℝ≥0) * (2 : ℝ≥0) ^ r * z * w ^ r) *
        (W.terminalSize : ℝ≥0) ^ (a - 1) := by
    by_cases hrs : r = s
    · rw [← hidentical hrs]
      exact sourceGainExceptionalWeight_same_family hF ha T H w hw
    · rw [sourceGainExceptionalWeight_zero_of_orders_ne W F G T H w
        (fun E hE ↦ (hF.uniform E hE).1) (fun E hE ↦ (hG.uniform E hE).1) hrs]
      exact zero_le
  apply (sourceGain_extension_le_split W F G T H w ha
    (fun E hE ↦ (hF.uniform E hE).1) (fun E hE ↦ (hG.uniform E hE).1)).trans
  have hb := add_le_add (add_le_add (sourceGainGoodWeight_le hF hG hr hs ha T H w hw)
    (sourceGainReverseGoodWeight_le hF hG hr hs ha T H w hw)) he
  simpa only [sourceGainMomentCoefficient, add_mul] using hb

end

end Erdos207
