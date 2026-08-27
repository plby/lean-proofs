/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexExactBankSignedCount
import ErdosProblems.Erdos207.DistinctEqualRemainders
import ErdosProblems.Erdos207.VortexNibbleExponentSplit

/-! # Source-correct well-spreadness: signed profile factors and distinct configurations -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def Vortex.sourceProfileScale
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (R : ℕ) (t : VortexProfile ell) : ℝ≥0 :=
  (W.terminalSize : ℝ≥0) ^ R * W.profileScale t / (W.terminalSize : ℝ≥0) ^ t.mass

theorem Vortex.sourceProfileScale_mul_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (R : ℕ) (t : VortexProfile ell) (hterminal : 0 < W.terminalSize) :
    W.sourceProfileScale R t * (W.terminalSize : ℝ≥0) ^ t.mass =
      (W.terminalSize : ℝ≥0) ^ R * W.profileScale t := by
  have hpos : (0 : ℝ≥0) < W.terminalSize := by exact_mod_cast hterminal
  exact div_mul_cancel₀ _ (pow_ne_zero _ hpos.ne')

theorem Vortex.sourceProfileScale_of_mass_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell R : ℕ}
    (W : Vortex V ell) (t : VortexProfile ell) (hterminal : 0 < W.terminalSize) (hm : t.mass ≤ R) :
    W.sourceProfileScale R t = (W.terminalSize : ℝ≥0) ^ (R - t.mass) * W.profileScale t := by
  have hpos : (0 : ℝ≥0) < W.terminalSize := by exact_mod_cast hterminal
  unfold sourceProfileScale
  apply (div_eq_iff (pow_ne_zero _ hpos.ne')).mpr
  calc
    _ = (W.terminalSize : ℝ≥0) ^ ((R - t.mass) + t.mass) * W.profileScale t := by
      rw [Nat.sub_add_cancel hm]
    _ = _ := by rw [pow_add]; ring

theorem Vortex.le_mul_sourceProfileScale_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (d : ℕ) (t : VortexProfile ell) (a c : ℝ≥0)
    (hterminal : 0 < W.terminalSize) :
    a ≤ c * W.sourceProfileScale d t ↔
      a * (W.terminalSize : ℝ≥0) ^ t.mass ≤
        c * (W.terminalSize : ℝ≥0) ^ d * W.profileScale t := by
  have hpos : (0 : ℝ≥0) < W.terminalSize := by exact_mod_cast hterminal
  unfold sourceProfileScale
  rw [← mul_div_assoc, le_div_iff₀ (pow_pos hpos _), mul_assoc]

def Vortex.profiledDistinctEqualRemainderPairs
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T T' : TripleOn V) (t : VortexProfile ell) :
    Finset (TripleSystemOn V × TripleSystemOn V) :=
  (distinctEqualRemainderPairs F T T').filter fun p ↦ W.outerProfile (p.1.erase T) = t

@[simp] theorem Vortex.mem_profiledDistinctEqualRemainderPairs_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T T' : TripleOn V) (t : VortexProfile ell)
    (p : TripleSystemOn V × TripleSystemOn V) :
    p ∈ W.profiledDistinctEqualRemainderPairs F T T' t ↔
      p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ≠ p.2 ∧ T ∈ p.1 ∧ T' ∈ p.2 ∧ p.1.erase T = p.2.erase T' ∧
        W.outerProfile (p.1.erase T) = t := by
  simp only [profiledDistinctEqualRemainderPairs, mem_filter, mem_distinctEqualRemainderPairs_iff, and_assoc]

@[simp] theorem Vortex.profiledDistinctEqualRemainderPairs_self
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (t : VortexProfile ell) :
    W.profiledDistinctEqualRemainderPairs F T T t = ∅ := by
  simp only [profiledDistinctEqualRemainderPairs, distinctEqualRemainderPairs_self, filter_empty]

structure SourceVortexWellSpread
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) (F : ForbiddenFamilyOn V) (y z : ℝ≥0) : Prop where
  order : 4 ≤ j
  terminal_nonempty : 0 < W.terminalSize
  uniform : ∀ E ∈ F, E.card = j - 2 ∧ IsPackingOn E
  extensions : ∀ (R : TripleSystemOn V) (t : VortexProfile ell), R.Nonempty → R.card ≤ j - 2 →
    ((W.profiledExtensions F R t).card : ℝ≥0) ≤ z * W.sourceProfileScale (j - vortexRootExponent j R.card) t
  equal_remainders : ∀ (T T' : TripleOn V) (t : VortexProfile ell),
    ((W.profiledDistinctEqualRemainderPairs F T T' t).card : ℝ≥0) ≤ z * W.sourceProfileScale (j - 4) t
  order_four_pair : j = 4 → ∀ (T : TripleOn V) (P : VortexPairOn V), ¬ P.1 ⊆ T.1 →
    ((W.terminalPairExtensions F T P).card : ℝ≥0) ≤ z
  singleton_extensions : ∀ (T : TripleOn V) (t : VortexProfile ell),
    ((W.profiledExtensions F {T} t).card : ℝ≥0) ≤ y * W.sourceProfileScale (j - 3) t

theorem SourceVortexWellSpread.mono
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ} {W : Vortex V ell}
    {F : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (h : SourceVortexWellSpread W j F y z) (hy : y ≤ y') (hz : z ≤ z') :
    SourceVortexWellSpread W j F y' z' := by
  refine ⟨h.order, h.terminal_nonempty, h.uniform, ?_, ?_, ?_, ?_⟩
  · intro R t hR hcard
    exact (h.extensions R t hR hcard).trans (mul_le_mul_of_nonneg_right hz zero_le)
  · intro T T' t
    exact (h.equal_remainders T T' t).trans (mul_le_mul_of_nonneg_right hz zero_le)
  · intro hj T P hP
    exact (h.order_four_pair hj T P hP).trans hz
  · intro T t
    exact (h.singleton_extensions T t).trans (mul_le_mul_of_nonneg_right hy zero_le)

end

end Erdos207
