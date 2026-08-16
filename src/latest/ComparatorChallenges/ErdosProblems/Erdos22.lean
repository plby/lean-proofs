/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter SimpleGraph Set Real
open scoped Topology BigOperators ENNReal NNReal

namespace Erdos22

syntax (name := answerSyntax22) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

attribute [local instance] Classical.propDecidable

/-! ## Two finite graph operations -/

/-- Add an independent set of `t` vertices and join it completely to the
`true` Boolean part of `G`. -/
def oneSidedExtension {W : Type*} (G : SimpleGraph (Bool × W)) (t : ℕ) :
    SimpleGraph ((Bool × W) ⊕ Fin t) where
  Adj
    | .inl u, .inl v => G.Adj u v
    | .inl u, .inr _ => u.1 = true
    | .inr _, .inl v => v.1 = true
    | .inr _, .inr _ => False
  symm.symm
    | .inl _, .inl _ => G.adj_symm
    | .inl _, .inr _ | .inr _, .inl _ => id
    | .inr _, .inr _ => id
  loopless.irrefl
    | .inl u => G.loopless.irrefl u
    | .inr _ => id

@[simp] lemma oneSidedExtension_adj_inl_inl {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u v : Bool × W) :
    (oneSidedExtension G t).Adj (.inl u) (.inl v) ↔ G.Adj u v := Iff.rfl

@[simp] lemma oneSidedExtension_adj_inl_inr {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u : Bool × W) (v : Fin t) :
    (oneSidedExtension G t).Adj (.inl u) (.inr v) ↔ u.1 = true := Iff.rfl

@[simp] lemma oneSidedExtension_adj_inr_inl {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u : Fin t) (v : Bool × W) :
    (oneSidedExtension G t).Adj (.inr u) (.inl v) ↔ v.1 = true := Iff.rfl

@[simp] lemma oneSidedExtension_not_adj_inr_inr {W : Type*}
    (G : SimpleGraph (Bool × W)) (t : ℕ) (u v : Fin t) :
    ¬(oneSidedExtension G t).Adj (.inr u) (.inr v) := id

/-- A uniform independent-fibre blowup. -/
def uniformBlowup {V : Type*} (G : SimpleGraph V) (q : ℕ) :
    SimpleGraph (V × Fin q) where
  Adj u v := G.Adj u.1 v.1
  symm.symm _ _ := G.adj_symm
  loopless.irrefl u := G.loopless.irrefl u.1

@[simp] lemma uniformBlowup_adj {V : Type*} (G : SimpleGraph V) (q : ℕ)
    (u v : V × Fin q) :
    (uniformBlowup G q).Adj u v ↔ G.Adj u.1 v.1 := Iff.rfl

/-- Add `r` isolated vertices to a uniform blowup. -/
abbrev paddedBlowup {V : Type*} (G : SimpleGraph V) (q r : ℕ) :
    SimpleGraph ((V × Fin q) ⊕ Fin r) := uniformBlowup G q ⊕g ⊥

/-! ## Clique-freeness of the one-sided extension -/

theorem erdos_22 : answer(True) ↔
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop,
      ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
        (G.indepNum : ℝ) ≤ ε * n ∧ (n : ℝ) ^ 2 / 8 ≤ G.edgeFinset.card := by
  sorry
