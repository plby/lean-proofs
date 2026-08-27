/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceVortexWeight

/-! # Terminal omissions with exact source profile weights -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def terminalRemainderChoices
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (f : ℕ) : Finset (TripleSystemOn V) :=
  (C.powersetCard f).filter fun A ↦ ∀ T ∈ C \ A, W.level T = Fin.last ell

theorem mem_terminalRemainderChoices_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell f : ℕ}
    {W : Vortex V ell} {C A : TripleSystemOn V} :
    A ∈ terminalRemainderChoices W C f ↔
      A ⊆ C ∧ A.card = f ∧ ∀ T ∈ C \ A, W.level T = Fin.last ell := by
  simp only [terminalRemainderChoices, mem_filter, mem_powersetCard, and_assoc]

theorem Vortex.outerProfile_eq_of_terminal_sdiff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) {C A : TripleSystemOn V} (hAC : A ⊆ C)
    (hterminal : ∀ T ∈ C \ A, W.level T = Fin.last ell) :
    W.outerProfile A = W.outerProfile C := by
  funext i
  change (A ∩ W.trianglesAtLevel i.castSucc).card =
    (C ∩ W.trianglesAtLevel i.castSucc).card
  congr 1
  ext T
  simp only [mem_inter, W.mem_trianglesAtLevel_iff]
  constructor
  · exact fun h ↦ ⟨hAC h.1, h.2⟩
  · intro h
    refine ⟨?_, h.2⟩
    by_contra hTA
    have heq := (hterminal T (mem_sdiff.mpr ⟨h.1, hTA⟩)).symm.trans h.2
    have hv := congrArg Fin.val heq
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega

def terminalOmissionCodes
    {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α] {ell : ℕ}
    (W : Vortex V ell) (I : Finset α) (C : α → TripleSystemOn V) (f : ℕ) :
    Finset (α × TripleSystemOn V) :=
  I.biUnion fun x ↦ (terminalRemainderChoices W (C x) f).image fun A ↦ (x, A)

theorem mem_terminalOmissionCodes_iff
    {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α] {ell f : ℕ}
    {W : Vortex V ell} {I : Finset α} {C : α → TripleSystemOn V}
    {x : α × TripleSystemOn V} :
    x ∈ terminalOmissionCodes W I C f ↔
      x.1 ∈ I ∧ x.2 ∈ terminalRemainderChoices W (C x.1) f := by
  rcases x with ⟨x, A⟩
  simp only [terminalOmissionCodes, mem_biUnion, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨y, hy, B, hB, hyx, hBA⟩
    subst y
    subst B
    exact ⟨hy, hB⟩
  · rintro ⟨hx, hA⟩
    exact ⟨x, hx, A, hA, rfl, rfl⟩

theorem card_terminalOmission_profile_le
    {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α] {ell f m : ℕ}
    (W : Vortex V ell) (I : Finset α) (C : α → TripleSystemOn V)
    (hcard : ∀ x ∈ I, (C x).card ≤ m) (t : VortexProfile ell) :
    ((terminalOmissionCodes W I C f).filter fun x ↦ W.outerProfile x.2 = t).card ≤
      2 ^ m * (I.filter fun x ↦ W.outerProfile (C x) = t).card := by
  let D := (terminalOmissionCodes W I C f).filter fun x ↦ W.outerProfile x.2 = t
  have hmap : D.image Prod.fst ⊆ I.filter (fun x ↦ W.outerProfile (C x) = t) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hx
    have ha' := mem_filter.mp ha
    have hm := mem_terminalOmissionCodes_iff.mp ha'.1
    have hc := mem_terminalRemainderChoices_iff.mp hm.2
    exact mem_filter.mpr ⟨hm.1,
      (W.outerProfile_eq_of_terminal_sdiff hc.1 hc.2.2).symm.trans ha'.2⟩
  have hfiber : ∀ x ∈ D.image Prod.fst, (D.filter fun a ↦ a.1 = x).card ≤ 2 ^ m := by
    intro x hx
    have hxI := (mem_filter.mp (hmap hx)).1
    calc
      _ ≤ ((C x).powerset).card := by
        apply card_le_card_of_injOn (f := Prod.snd)
        · intro a ha
          have hax := mem_filter.mp ha
          have hm := mem_terminalOmissionCodes_iff.mp (mem_filter.mp hax.1).1
          have hc := (mem_terminalRemainderChoices_iff.mp hm.2).1
          rw [hax.2] at hc
          exact mem_powerset.mpr hc
        · intro a ha b hb hab
          exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) hab
      _ = 2 ^ (C x).card := card_powerset _
      _ ≤ 2 ^ m := pow_le_pow_right' (by omega) (hcard x hxI)
  exact (card_le_mul_card_image D (2 ^ m) hfiber).trans
    (Nat.mul_le_mul_left _ (card_le_card hmap))

theorem terminalOmission_weight_le_of_profile_count
    {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α]
    {ell f m d : ℕ} (W : Vortex V ell) (I : Finset α)
    (C : α → TripleSystemOn V) (w b : ℝ≥0)
    (hn : 0 < W.terminalSize) (hcard : ∀ x ∈ I, (C x).card ≤ m)
    (hcount : ∀ t : VortexProfile ell,
      ((I.filter fun x ↦ W.outerProfile (C x) = t).card : ℝ≥0) ≤
        b * W.sourceProfileScale d t) :
    ∑ x ∈ terminalOmissionCodes W I C f, setWeight (vortexTripleWeight W w) x.2 ≤
      ((f + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ m * b) * w ^ f *
        (W.terminalSize : ℝ≥0) ^ d / (W.terminalSize : ℝ≥0) ^ f := by
  apply W.weight_sum_le_of_profile_count (terminalOmissionCodes W I C f) Prod.snd w
    ((2 : ℝ≥0) ^ m * b) hn
  · intro x hx
    exact (mem_terminalRemainderChoices_iff.mp (mem_terminalOmissionCodes_iff.mp hx).2).2.1
  · intro t
    have hc : (((terminalOmissionCodes W I C f).filter
        fun x ↦ W.outerProfile x.2 = t).card : ℝ≥0) ≤
        (2 : ℝ≥0) ^ m * (I.filter fun x ↦ W.outerProfile (C x) = t).card := by
      exact_mod_cast card_terminalOmission_profile_le W I C hcard t
    exact hc.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hcount t) (show (0 : ℝ≥0) ≤ 2 ^ m from zero_le))

end

end Erdos207
