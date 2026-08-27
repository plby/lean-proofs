/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCommonWeightSplit

/-! # Complete source common-threat extension bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceCommonMomentCoefficient (ell q r : ℕ) (w z z' : ℝ≥0) : ℝ≥0 :=
  sourceCommonGoodCoefficient ell q w z z' + sourceCommonGoodCoefficient ell q w z' z +
    (((r - 3) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ (r - 3) * z) * w ^ (r - 4)

theorem sourceCommon_hasExtensionBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell q r s : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (hr : r ≤ q) (hs : s ≤ q) (hidentical : r = s → F = G)
    (T T' : TripleOn V) (w : ℝ≥0) (hw : 1 ≤ w) :
    HasExtensionBound (fun u : sourceCommonThreats W F G T T' ↦ u.1.remainder)
      (vortexTripleWeight W w) (sourceCommonMomentCoefficient ell q r w z z') := by
  intro H
  have hexception : sourceCommonExceptionalWeight W F G T T' H w ≤
      (((r - 3) ^ ell : ℕ) : ℝ≥0) * ((2 : ℝ≥0) ^ (r - 3) * z) * w ^ (r - 4) := by
    by_cases hrs : r = s
    · rw [← hidentical hrs]
      exact sourceCommonExceptionalWeight_same_family hF T T' H w
    · rw [sourceCommonExceptionalWeight_zero_of_orders_ne W F G T T' H w
        (fun E hE ↦ (hF.uniform E hE).1) (fun E hE ↦ (hG.uniform E hE).1) hrs]
      exact zero_le
  exact (sourceCommon_extension_le_split W F G T T' H w
    (fun E hE ↦ (hF.uniform E hE).1) (fun E hE ↦ (hG.uniform E hE).1)).trans
      (add_le_add (add_le_add (sourceCommonGoodWeight_le hF hG hr hs T T' H w hw)
        (sourceCommonGoodWeight_le hG hF hs hr T' T H w hw)) hexception)

def sourceCommonCardEmbedding
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V) :
    sourceCommonThreats W F G T T' ↪ Σ p : F ×ˢ G, p.1.1 where
  toFun u := ⟨⟨(u.1.first, u.1.second), mem_product.mpr ⟨u.1.first_mem, u.1.second_mem⟩⟩,
    ⟨u.1.bridge, u.1.bridge_first⟩⟩
  inj' := by
    intro u v huv
    have hfirst := congrArg (fun p ↦ p.1.1.1) huv
    have hsecond := congrArg (fun p ↦ p.1.1.2) huv
    have hbridge := congrArg (fun p ↦ p.2.1) huv
    apply Subtype.ext
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    cases u
    cases v
    simp_all

theorem card_sourceCommonThreats_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell r : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (hF : ∀ E ∈ F, E.card = r - 2) :
    (sourceCommonThreats W F G T T').card ≤ F.card * G.card * (r - 2) := by
  calc
    _ = Fintype.card (sourceCommonThreats W F G T T') := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Σ p : F ×ˢ G, p.1.1) := Fintype.card_le_of_embedding (sourceCommonCardEmbedding W F G T T')
    _ = ∑ p : F ×ˢ G, p.1.1.card := by simp
    _ = ∑ _p : F ×ˢ G, (r - 2) := by
      apply sum_congr rfl
      intro p _hp
      exact hF p.1.1 (mem_product.mp p.2).1
    _ = _ := by simp

theorem card_sourceCommonThreats_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] {ell q r s : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T T' : TripleOn V)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2)
    (hr : r ≤ q) (hs : s ≤ q) :
    (sourceCommonThreats W F G T T').card ≤ (q + 1) * (Fintype.card V + 1) ^ (6 * q) := by
  have hf := card_uniform_source_family_le_polynomial F r hF
  have hg := card_uniform_source_family_le_polynomial G s hG
  have hf' : F.card ≤ (Fintype.card V + 1) ^ (3 * q) :=
    hf.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 3 hr))
  have hg' : G.card ≤ (Fintype.card V + 1) ^ (3 * q) :=
    hg.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 3 hs))
  apply (card_sourceCommonThreats_le W F G T T' hF).trans
  calc
    _ ≤ ((Fintype.card V + 1) ^ (3 * q) * (Fintype.card V + 1) ^ (3 * q)) * (q + 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hf' hg') (by omega)
    _ = _ := by rw [← pow_add, show 3 * q + 3 * q = 6 * q by omega, mul_comm]

end

end Erdos207
