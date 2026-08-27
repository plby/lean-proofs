/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.MasterIterationData
import ErdosProblems.Erdos207.VortexWellSpread
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Structured initial data for the KSSS iteration

This file formalizes Definition 10.3.  The power-law contraction and the
power-law well-spread error are rounded exactly as required to make their
finite cardinal bounds natural numbers.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The canonical embedding of a vortex prefix into all vortex levels. -/
def vortexPrefixEmbedding {ell : ℕ} (k : Fin (ell + 1)) :
    Fin (k.val + 1) ↪ Fin (ell + 1) where
  toFun i := ⟨i.val, lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) k.isLt⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun x : Fin (ell + 1) ↦ x.val) hij

@[simp]
lemma vortexPrefixEmbedding_val {ell : ℕ} (k : Fin (ell + 1))
    (i : Fin (k.val + 1)) :
    (vortexPrefixEmbedding k i).val = i.val := rfl

/-- The prefix `U₀ ⊇ ⋯ ⊇ Uₖ`, as a vortex of length `k`. -/
def Vortex.prefix
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) : Vortex V k.val where
  U i := W.U (vortexPrefixEmbedding k i)
  root := by
    rw [show vortexPrefixEmbedding k 0 = 0 by apply Fin.ext; rfl]
    exact W.root
  antitone := by
    intro i j hij
    apply W.antitone
    exact hij

@[simp]
lemma Vortex.prefix_U
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (i : Fin (k.val + 1)) :
    (W.prefix k).U i = W.U (vortexPrefixEmbedding k i) := rfl

lemma vortexPrefixEmbedding_last {ell : ℕ} (k : Fin (ell + 1)) :
    vortexPrefixEmbedding k (Fin.last k.val) = k := by
  apply Fin.ext
  rfl

@[simp]
lemma Vortex.prefix_terminalSize
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) :
    (W.prefix k).terminalSize = (W.U k).card := by
  simp [Vortex.terminalSize, vortexPrefixEmbedding_last]

/-- The integer vortex size prescribed by `⌊m^(1-ρ)⌋`. -/
def vortexShrinkTarget (rho : ℝ) (m : ℕ) : ℕ :=
  ⌊(m : ℝ) ^ (1 - rho)⌋₊

/-- The integer upper bound corresponding to the paper's `m^β` loss. -/
def vortexSpreadError (beta : ℝ) (m : ℕ) : ℕ :=
  ⌈(m : ℝ) ^ beta⌉₊

/-- Exact finite version of KSSS Definition 10.3.  `F r` is the family
`F_r`; `y` is the fixed `O_{q,ell}(1)` coefficient, while the second
well-spread coefficient is the rounded value `|U_k|^β`. -/
def IsStructuredInitialData
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ℕ → ForbiddenFamilyOn V)
    (q : ℕ) (rho beta : ℝ) (y : ℕ) : Prop :=
  (∀ i : Fin ell,
    (W.U i.succ).card = vortexShrinkTarget rho (W.U i.castSucc).card) ∧
  (∀ k : Fin (ell + 1), ∀ r : ℕ, 4 ≤ r → r ≤ q →
    VortexWellSpread (W.prefix k) r (F r) y
      (vortexSpreadError beta (W.U k).card))

/-- Structured data supplies the exact size recurrence at every step. -/
lemma IsStructuredInitialData.card_succ
    {V : Type*} [Fintype V] [DecidableEq V] {ell q y : ℕ}
    {W : Vortex V ell} {F : ℕ → ForbiddenFamilyOn V}
    {rho beta : ℝ}
    (h : IsStructuredInitialData W F q rho beta y) (i : Fin ell) :
    (W.U i.succ).card = vortexShrinkTarget rho (W.U i.castSucc).card :=
  h.1 i

/-- Structured data supplies well-spreadness on every truncated vortex. -/
lemma IsStructuredInitialData.wellSpread
    {V : Type*} [Fintype V] [DecidableEq V] {ell q y : ℕ}
    {W : Vortex V ell} {F : ℕ → ForbiddenFamilyOn V}
    {rho beta : ℝ}
    (h : IsStructuredInitialData W F q rho beta y)
    (k : Fin (ell + 1)) {r : ℕ} (hr4 : 4 ≤ r) (hrq : r ≤ q) :
    VortexWellSpread (W.prefix k) r (F r) y
      (vortexSpreadError beta (W.U k).card) :=
  h.2 k r hr4 hrq

end

end Erdos207
