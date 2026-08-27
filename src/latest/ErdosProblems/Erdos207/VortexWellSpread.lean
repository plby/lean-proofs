/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.Vortex
import ErdosProblems.Erdos207.Prefix
import Mathlib.Algebra.BigOperators.Fin

/-!
# Well-spread forbidden families along a vortex

This file gives a coarse natural-exponent interface related to conditions
(W1)--(W4) in Kwan--Sah--Sawhney--Simkin. The source permits negative
terminal exponents, whereas this interface truncates their subtraction.
Consequently it must not be substituted for the exact signed-profile
estimates in the recursive weight cancellation. The checked statements
using this coarse interface remain valid as stated.
-/

namespace Erdos207

open Finset

noncomputable section

/-- A profile records the number of additional triangles at each nonterminal
vortex level. -/
abbrev VortexProfile (ell : ℕ) := Fin ell → ℕ

/-- A two-element vertex set, kept local to the vortex layer so this file
does not depend on the later absorber weight hierarchy. -/
abbrev VortexPairOn (V : Type*) [DecidableEq V] :=
  {s : Finset V // s.card = 2}

/-- Total number of triangles prescribed by a vortex profile. -/
def VortexProfile.mass {ell : ℕ} (t : VortexProfile ell) : ℕ :=
  ∑ i, t i

/-- The finite box of profiles whose coordinates are at most `r`. -/
def vortexProfileBox (ell r : ℕ) : Finset (VortexProfile ell) :=
  (univ : Finset (Fin ell → Fin (r + 1))).image fun t i ↦ (t i).val

@[simp]
lemma mem_vortexProfileBox_iff {ell r : ℕ} (t : VortexProfile ell) :
    t ∈ vortexProfileBox ell r ↔ ∀ i, t i ≤ r := by
  constructor
  · intro ht i
    obtain ⟨u, _hu, rfl⟩ := mem_image.mp ht
    exact Nat.le_of_lt_succ (u i).isLt
  · intro ht
    apply mem_image.mpr
    let u : Fin ell → Fin (r + 1) :=
      fun i ↦ ⟨t i, Nat.lt_succ_of_le (ht i)⟩
    refine ⟨u, mem_univ u, ?_⟩
    funext i
    rfl

@[simp]
lemma card_vortexProfileBox (ell r : ℕ) :
    (vortexProfileBox ell r).card = (r + 1) ^ ell := by
  unfold vortexProfileBox
  rw [card_image_iff.mpr]
  · simp
  · intro a _ha b _hb hab
    funext i
    apply Fin.ext
    exact congrFun hab i

/-- Product of the outer vortex sizes with the powers prescribed by a
profile. -/
def Vortex.profileScale
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (t : VortexProfile ell) : ℕ :=
  ∏ i, (W.U i.castSucc).card ^ t i

/-- The size of the terminal vortex set. -/
def Vortex.terminalSize
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) : ℕ :=
  (W.U (Fin.last ell)).card

/-- The KSSS exponent `v^r(R)`, expressed in terms of `|R|`. -/
def vortexRootExponent (r s : ℕ) : ℕ :=
  if s = 1 ∨ s = r - 2 then s + 2 else s + 3

@[simp]
lemma vortexRootExponent_one (r : ℕ) :
    vortexRootExponent r 1 = 3 := by
  simp [vortexRootExponent]

lemma vortexRootExponent_full {r s : ℕ} (hs : s = r - 2) :
    vortexRootExponent r s = s + 2 := by
  simp [vortexRootExponent, hs]

lemma vortexRootExponent_middle {r s : ℕ}
    (hs1 : s ≠ 1) (hsfull : s ≠ r - 2) :
    vortexRootExponent r s = s + 3 := by
  simp [vortexRootExponent, hs1, hsfull]

lemma add_two_le_vortexRootExponent (r s : ℕ) :
    s + 2 ≤ vortexRootExponent r s := by
  unfold vortexRootExponent
  split_ifs
  · exact le_rfl
  · omega

/-- The outer-level profile of a triangle family.  Terminal-level triangles
are deliberately omitted, exactly as in the products in (W1)--(W4). -/
def Vortex.outerProfile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) : VortexProfile ell :=
  fun i ↦ W.levelCount C i.castSucc

/-- Members of `F` extending `R` with a prescribed profile outside `R`. -/
def Vortex.profiledExtensions
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (R : TripleSystemOn V) (t : VortexProfile ell) :
    ForbiddenFamilyOn V :=
  F.filter fun E ↦ R ⊆ E ∧ W.outerProfile (E \ R) = t

@[simp]
lemma Vortex.mem_profiledExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (R : TripleSystemOn V) (t : VortexProfile ell)
    (E : TripleSystemOn V) :
    E ∈ W.profiledExtensions F R t ↔
      E ∈ F ∧ R ⊆ E ∧ W.outerProfile (E \ R) = t := by
  simp [Vortex.profiledExtensions]

/-- Ordered pairs of configurations which agree after deleting distinguished
triangles, with the common remainder having the prescribed outer profile. -/
def Vortex.profiledEqualRemainderPairs
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (T T' : TripleOn V) (t : VortexProfile ell) :
    Finset (TripleSystemOn V × TripleSystemOn V) :=
  (F ×ˢ F).filter fun p ↦
    T ∈ p.1 ∧ T' ∈ p.2 ∧
      p.1.erase T = p.2.erase T' ∧
      W.outerProfile (p.1.erase T) = t

@[simp]
lemma Vortex.mem_profiledEqualRemainderPairs_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (T T' : TripleOn V) (t : VortexProfile ell)
    (p : TripleSystemOn V × TripleSystemOn V) :
    p ∈ W.profiledEqualRemainderPairs F T T' t ↔
      p.1 ∈ F ∧ p.2 ∈ F ∧ T ∈ p.1 ∧ T' ∈ p.2 ∧
        p.1.erase T = p.2.erase T' ∧
        W.outerProfile (p.1.erase T) = t := by
  simp [Vortex.profiledEqualRemainderPairs, and_assoc]

/-- The order-four exceptional family in (W3): configurations containing
`T` whose other triangle is terminal and contains the prescribed pair. -/
def Vortex.terminalPairExtensions
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (T : TripleOn V) (P : VortexPairOn V) : ForbiddenFamilyOn V :=
  F.filter fun E ↦
    T ∈ E ∧ ∃ D ∈ E.erase T,
      W.level D = Fin.last ell ∧ P.1 ⊆ D.1

@[simp]
lemma Vortex.mem_terminalPairExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (T : TripleOn V) (P : VortexPairOn V) (E : TripleSystemOn V) :
    E ∈ W.terminalPairExtensions F T P ↔
      E ∈ F ∧ T ∈ E ∧ ∃ D ∈ E.erase T,
        W.level D = Fin.last ell ∧ P.1 ⊆ D.1 := by
  simp [Vortex.terminalPairExtensions, and_assoc]

/-- A diagonal-inclusive finite variant of KSSS well-spreadness.
The `equal_remainders` field bounds identical pairs as well as distinct
pairs, unlike source condition W2. Existing results with this stronger
hypothesis remain valid, but its coarse absorber coefficient must not be
used as the source's sharp off-diagonal coefficient. -/
structure VortexWellSpread
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (r : ℕ) (F : ForbiddenFamilyOn V)
    (y z : ℕ) : Prop where
  uniform : ∀ E ∈ F, E.card = r - 2 ∧ IsPackingOn E
  extensions : ∀ (R : TripleSystemOn V) (t : VortexProfile ell),
    R.Nonempty → R.card ≤ r - 2 →
    (W.profiledExtensions F R t).card ≤
      z * W.terminalSize ^
          (r - t.mass - vortexRootExponent r R.card) *
        W.profileScale t
  equal_remainders : ∀ (T T' : TripleOn V) (t : VortexProfile ell),
    (W.profiledEqualRemainderPairs F T T' t).card ≤
      z * W.terminalSize ^ (r - t.mass - 4) * W.profileScale t
  order_four_pair : r = 4 → ∀ (T : TripleOn V) (P : VortexPairOn V),
    ¬ P.1 ⊆ T.1 → (W.terminalPairExtensions F T P).card ≤ z
  singleton_extensions : ∀ (T : TripleOn V) (t : VortexProfile ell),
    (W.profiledExtensions F {T} t).card ≤
      y * W.terminalSize ^ (r - t.mass - 3) * W.profileScale t

lemma VortexWellSpread.mono
    {V : Type*} [Fintype V] [DecidableEq V] {ell r y z y' z' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    (h : VortexWellSpread W r F y z) (hy : y ≤ y') (hz : z ≤ z') :
    VortexWellSpread W r F y' z' := by
  refine ⟨h.uniform, ?_, ?_, ?_, ?_⟩
  · intro R t hR hRcard
    exact (h.extensions R t hR hRcard).trans (by gcongr)
  · intro T T' t
    exact (h.equal_remainders T T' t).trans (by gcongr)
  · intro hr T P hPT
    exact (h.order_four_pair hr T P hPT).trans hz
  · intro T t
    exact (h.singleton_extensions T t).trans (by gcongr)

/-- The outer-profile mass never exceeds the size of the family. -/
lemma Vortex.outerProfile_mass_le_card
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) :
    (W.outerProfile C).mass ≤ C.card := by
  have htotal := W.sum_levelCount C
  unfold VortexProfile.mass Vortex.outerProfile
  let f : Fin (ell + 1) → ℕ := fun i ↦ W.levelCount C i
  have hsub : (∑ i : Fin ell, f i.castSucc) ≤
      (∑ i : Fin ell, f i.castSucc) + f (Fin.last ell) :=
    Nat.le_add_right _ _
  rw [← Fin.sum_univ_castSucc] at hsub
  simpa only [f, htotal] using hsub

lemma Vortex.outerProfile_apply_le_card
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (i : Fin ell) :
    W.outerProfile C i ≤ C.card := by
  unfold Vortex.outerProfile Vortex.levelCount
  exact card_le_card inter_subset_left


end

end Erdos207
