/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainWeightSplit

/-! # Polynomial code counts for the generalized gain-defect error term -/

namespace Erdos207

open Finset

noncomputable section

def sourceGainCardEmbedding
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ) :
    sourceGainDefects W F G T a ↪ Σ p : F ×ˢ G, p.1.1.powerset where
  toFun u := ⟨⟨(u.1.first, u.1.second), mem_product.mpr ⟨u.1.first_mem, u.1.second_mem⟩⟩,
    ⟨u.1.omitted, mem_powerset.mpr (u.1.omitted_subset.trans (erase_subset _ _))⟩⟩
  inj' := by
    intro u v huv
    have hf := congrArg (fun p ↦ p.1.1.1) huv
    have hs := congrArg (fun p ↦ p.1.1.2) huv
    have ho := congrArg (fun p ↦ p.2.1) huv
    apply Subtype.ext
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    cases u
    cases v
    simp_all

theorem card_sourceGainDefects_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell r : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ)
    (hF : ∀ E ∈ F, E.card = r - 2) :
    (sourceGainDefects W F G T a).card ≤ F.card * G.card * 2 ^ (r - 2) := by
  calc
    _ = Fintype.card (sourceGainDefects W F G T a) := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Σ p : F ×ˢ G, p.1.1.powerset) := Fintype.card_le_of_embedding (sourceGainCardEmbedding W F G T a)
    _ = ∑ p : F ×ˢ G, 2 ^ p.1.1.card := by simp only [Fintype.card_sigma, Fintype.card_coe, card_powerset]
    _ = ∑ _p : F ×ˢ G, 2 ^ (r - 2) := by
      apply sum_congr rfl
      intro p _hp
      rw [hF p.1.1 (mem_product.mp p.2).1]
    _ = _ := by simp

theorem card_sourceGainDefects_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] {ell q r s : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ)
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2)
    (hr : r ≤ q) (hs : s ≤ q) :
    (sourceGainDefects W F G T a).card ≤ 2 ^ q * (Fintype.card V + 1) ^ (6 * q) := by
  have hf := card_uniform_source_family_le_polynomial F r hF
  have hg := card_uniform_source_family_le_polynomial G s hG
  have hf' : F.card ≤ (Fintype.card V + 1) ^ (3 * q) :=
    hf.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 3 hr))
  have hg' : G.card ≤ (Fintype.card V + 1) ^ (3 * q) :=
    hg.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 3 hs))
  apply (card_sourceGainDefects_le W F G T a hF).trans
  calc
    _ ≤ ((Fintype.card V + 1) ^ (3 * q) * (Fintype.card V + 1) ^ (3 * q)) * 2 ^ q :=
      Nat.mul_le_mul (Nat.mul_le_mul hf' hg') (Nat.pow_le_pow_right (by omega) (by omega))
    _ = _ := by rw [← pow_add, show 3 * q + 3 * q = 6 * q by omega, mul_comm]

end

end Erdos207
