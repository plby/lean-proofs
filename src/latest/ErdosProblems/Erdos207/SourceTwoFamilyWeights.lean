/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGeneralMomentWeights

/-! # Ordered two-family source-weight exposure -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceSecondRoots
    {V : Type*} [Fintype V] [DecidableEq V]
    (E Q' : TripleSystemOn V) (j' v' : ℕ) : Finset (TripleSystemOn V) :=
  (E ∪ Q').powerset.filter fun B ↦
    B.Nonempty ∧ B.card ≤ j' - 2 ∧ vortexRootExponent j' B.card = v'

theorem card_sourceSecondRoots_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (E Q' : TripleSystemOn V) (j' v' m : ℕ) (hE : E.card ≤ m) :
    (sourceSecondRoots E Q' j' v').card ≤ 2 ^ (m + Q'.card) := by
  calc
    _ ≤ ((E ∪ Q').powerset).card := card_filter_le _ _
    _ = 2 ^ (E ∪ Q').card := card_powerset _
    _ ≤ _ := pow_le_pow_right' (by omega)
      ((card_union_le E Q').trans (Nat.add_le_add_right hE _))

def sourceSecondRootWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F' : ForbiddenFamilyOn V) (E Q' : TripleSystemOn V)
    (j' v' b : ℕ) (w : ℝ≥0) : ℝ≥0 :=
  ∑ B ∈ sourceSecondRoots E Q' j' v', sourceRootOmissionWeight W F' B b w

theorem SourceVortexWellSpread.second_root_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j' v' b m : ℕ}
    {W : Vortex V ell} {F' : ForbiddenFamilyOn V} {y' z' : ℝ≥0}
    (h : SourceVortexWellSpread W j' F' y' z') (E Q' : TripleSystemOn V)
    (hE : E.card ≤ m) (w : ℝ≥0) :
    sourceSecondRootWeight W F' E Q' j' v' b w ≤
      (2 : ℝ≥0) ^ (m + Q'.card) *
        (((b + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z') * w ^ b *
          (W.terminalSize : ℝ≥0) ^ (j' - v') / (W.terminalSize : ℝ≥0) ^ b) := by
  let K : ℝ≥0 := ((b + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z') * w ^ b *
    (W.terminalSize : ℝ≥0) ^ (j' - v') / (W.terminalSize : ℝ≥0) ^ b
  have hterm : ∀ B ∈ sourceSecondRoots E Q' j' v',
      sourceRootOmissionWeight W F' B b w ≤ K := by
    intro B hB
    have hm := (mem_filter.mp hB).2
    simpa only [hm.2.2] using h.root_omission_weight_le B hm.1 hm.2.1 w (f := b)
  calc
    _ ≤ ∑ _B ∈ sourceSecondRoots E Q' j' v', K := sum_le_sum hterm
    _ = ((sourceSecondRoots E Q' j' v').card : ℝ≥0) * K := by simp
    _ ≤ (2 : ℝ≥0) ^ (m + Q'.card) * K := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast card_sourceSecondRoots_le E Q' j' v' m hE

theorem source_weight_bound_mul
    (n w u v : ℝ≥0) (a b d e : ℕ) :
    (u * w ^ a * n ^ d / n ^ a) * (v * w ^ b * n ^ e / n ^ b) =
      (u * v) * w ^ (a + b) * n ^ (d + e) / n ^ (a + b) := by
  simp only [div_eq_mul_inv, pow_add, mul_inv_rev]
  ring

def sourceTwoFamilySplitWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F F' : ForbiddenFamilyOn V) (Q Q' : TripleSystemOn V)
    (j' v' a b : ℕ) (w : ℝ≥0) : ℝ≥0 :=
  ∑ x ∈ terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) a,
    setWeight (vortexTripleWeight W w) x.2 *
      sourceSecondRootWeight W F' x.1 Q' j' v' b w

theorem sourceTwoFamilySplitWeight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' v' a b : ℕ}
    {W : Vortex V ell} {F F' : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z)
    (h' : SourceVortexWellSpread W j' F' y' z')
    (Q Q' : TripleSystemOn V) (hQ : Q.Nonempty) (hQcard : Q.card ≤ j - 2)
    (w : ℝ≥0) :
    sourceTwoFamilySplitWeight W F F' Q Q' j' v' a b w ≤
      ((((a + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j - 2) * z)) *
        ((2 : ℝ≥0) ^ (j - 2 + Q'.card) *
          (((b + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z')))) *
      w ^ (a + b) *
        (W.terminalSize : ℝ≥0) ^ ((j - vortexRootExponent j Q.card) + (j' - v')) /
        (W.terminalSize : ℝ≥0) ^ (a + b) := by
  let K : ℝ≥0 := (2 : ℝ≥0) ^ (j - 2 + Q'.card) *
    (((b + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z') * w ^ b *
      (W.terminalSize : ℝ≥0) ^ (j' - v') / (W.terminalSize : ℝ≥0) ^ b)
  have hsecond : ∀ x ∈ terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) a,
      sourceSecondRootWeight W F' x.1 Q' j' v' b w ≤ K := by
    intro x hx
    have hE := (mem_familyExtensions_iff.mp (mem_terminalOmissionCodes_iff.mp hx).1).1
    exact h'.second_root_weight_le x.1 Q' (le_of_eq (h.uniform x.1 hE).1) w
  calc
    _ ≤ ∑ x ∈ terminalOmissionCodes W (familyExtensions F Q) (fun E ↦ E \ Q) a,
        setWeight (vortexTripleWeight W w) x.2 * K := by
      exact sum_le_sum (fun x hx ↦ mul_le_mul_of_nonneg_left (hsecond x hx) zero_le)
    _ = sourceRootOmissionWeight W F Q a w * K := by
      unfold sourceRootOmissionWeight
      rw [sum_mul]
    _ ≤ (((a + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j - 2) * z) * w ^ a *
        (W.terminalSize : ℝ≥0) ^ (j - vortexRootExponent j Q.card) /
        (W.terminalSize : ℝ≥0) ^ a) * K :=
      mul_le_mul_of_nonneg_right (h.root_omission_weight_le Q hQ hQcard w) zero_le
    _ = _ := by
      dsimp only [K]
      simp only [div_eq_mul_inv, pow_add, mul_inv_rev]
      ring

def sourceTwoFamilyEnvelopeWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F F' : ForbiddenFamilyOn V) (Q Q' : TripleSystemOn V)
    (j' v' f : ℕ) (w : ℝ≥0) : ℝ≥0 :=
  ∑ a ∈ range (f + 1), sourceTwoFamilySplitWeight W F F' Q Q' j' v' a (f - a) w

theorem sourceTwoFamilyEnvelopeWeight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' v' f : ℕ}
    {W : Vortex V ell} {F F' : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z)
    (h' : SourceVortexWellSpread W j' F' y' z')
    (Q Q' : TripleSystemOn V) (hQ : Q.Nonempty) (hQcard : Q.card ≤ j - 2)
    (w : ℝ≥0) :
    sourceTwoFamilyEnvelopeWeight W F F' Q Q' j' v' f w ≤
      ((f + 1) ^ (2 * ell + 1) : ℕ) *
        (2 : ℝ≥0) ^ (2 * (j - 2) + (j' - 2) + Q'.card) * z * z' * w ^ f *
        (W.terminalSize : ℝ≥0) ^ ((j - vortexRootExponent j Q.card) + (j' - v')) /
        (W.terminalSize : ℝ≥0) ^ f := by
  let K : ℝ≥0 :=
    ((((f + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j - 2) * z)) *
      ((2 : ℝ≥0) ^ (j - 2 + Q'.card) *
        (((f + 1) ^ ell : ℕ) * ((2 : ℝ≥0) ^ (j' - 2) * z')))) *
    w ^ f * (W.terminalSize : ℝ≥0) ^
      ((j - vortexRootExponent j Q.card) + (j' - v')) / (W.terminalSize : ℝ≥0) ^ f
  have hterm : ∀ a ∈ range (f + 1),
      sourceTwoFamilySplitWeight W F F' Q Q' j' v' a (f - a) w ≤ K := by
    intro a ha
    have haf : a ≤ f := by have := mem_range.mp ha; omega
    have hb : f - a ≤ f := Nat.sub_le _ _
    have hbound := sourceTwoFamilySplitWeight_le h h' Q Q' hQ hQcard w
      (v' := v') (a := a) (b := f - a)
    rw [Nat.add_sub_of_le haf] at hbound
    apply hbound.trans
    dsimp only [K]
    gcongr
  calc
    _ ≤ ∑ _a ∈ range (f + 1), K := sum_le_sum hterm
    _ = (f + 1 : ℕ) * K := by simp
    _ = _ := by
      dsimp only [K]
      rw [show 2 * ell + 1 = ell + ell + 1 by omega,
        show 2 * (j - 2) + (j' - 2) + Q'.card =
          (j - 2) + (j - 2 + Q'.card) + (j' - 2) by omega]
      simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_one, pow_add, pow_one]
      ring

end

end Erdos207
