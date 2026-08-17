/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos565.Core
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Fractional triangle packings for Erdős Problem 76

This file deliberately works with an arbitrary feasible weight rather than an
LP maximum.  Both ingredients used in the resolution have stronger and more
convenient existential forms:

* Gruslys--Letzter construct red and blue feasible weights of the required
  combined size;
* Haxell--Rödl rounds every feasible weight with a uniform `o(n²)` loss.

This avoids putting real linear-programming duality in the trusted interface.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The load placed by `w` on a graph edge `e`.  Values of `w` away from the
triangle finset are intentionally ignored. -/
def fractionalEdgeLoad (G : SimpleGraph α) (w : Finset α → ℝ) (e : Sym2 α) : ℝ :=
  ∑ t ∈ (G.cliqueFinset 3).filter (fun t ↦ e ∈ t.sym2), w t

/-- Feasibility conditions for a fractional triangle packing. -/
def IsFractionalPacking (G : SimpleGraph α) (w : Finset α → ℝ) : Prop :=
  (∀ t ∈ G.cliqueFinset 3, 0 ≤ w t) ∧
    ∀ e ∈ G.edgeFinset, fractionalEdgeLoad G w e ≤ 1

/-- The total triangle weight of a fractional packing. -/
def fractionalSize (G : SimpleGraph α) (w : Finset α → ℝ) : ℝ :=
  ∑ t ∈ G.cliqueFinset 3, w t

/-- The covered-edge scaling used by Gruslys--Letzter. -/
def fractionalCoveredSize (G : SimpleGraph α) (w : Finset α → ℝ) : ℝ :=
  3 * fractionalSize G w

@[simp] lemma fractionalEdgeLoad_zero (G : SimpleGraph α) (e : Sym2 α) :
    fractionalEdgeLoad G (fun _ ↦ 0) e = 0 := by
  simp [fractionalEdgeLoad]

@[simp] lemma fractionalSize_zero (G : SimpleGraph α) :
    fractionalSize G (fun _ ↦ 0) = 0 := by
  simp [fractionalSize]

lemma isFractionalPacking_zero (G : SimpleGraph α) :
    IsFractionalPacking G (fun _ ↦ 0) := by
  constructor
  · simp
  · intro e he
    simp

lemma IsFractionalPacking.nonneg_on {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w) {t : Finset α} (ht : t ∈ G.cliqueFinset 3) :
    0 ≤ w t :=
  hw.1 t ht

lemma IsFractionalPacking.edgeLoad_le_one {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w) {e : Sym2 α} (he : e ∈ G.edgeFinset) :
    fractionalEdgeLoad G w e ≤ 1 :=
  hw.2 e he

lemma fractionalSize_nonneg {G : SimpleGraph α} {w : Finset α → ℝ}
    (hw : IsFractionalPacking G w) : 0 ≤ fractionalSize G w := by
  exact sum_nonneg fun t ht ↦ hw.1 t ht

/-- Exact problem-specific fractional statement.  Natural-number division is
`floor ((n-1)^2 / 4)`, and the factor `3` changes triangle weight to covered
edge weight. -/
def GruslysLetzterFractional : Prop :=
  ∀ n : ℕ, 26 ≤ n → ∀ G : SimpleGraph (Fin n),
    ∃ wR wB : Finset (Fin n) → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
        (((n - 1) ^ 2 / 4 : ℕ) : ℝ) ≤
          fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB

lemma GruslysLetzterFractional.apply (h : GruslysLetzterFractional)
    (n : ℕ) (hn : 26 ≤ n) (G : SimpleGraph (Fin n)) :
    ∃ wR wB : Finset (Fin n) → ℝ,
      IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
        (((n - 1) ^ 2 / 4 : ℕ) : ℝ) ≤
          fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB :=
  h n hn G

/-- Uniform arbitrary-weight form of the Haxell--Rödl rounding theorem for
triangles. -/
def HaxellRodlRounding : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    ∀ (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ),
        IsFractionalPacking G w →
          ∃ P : Finset (Finset (Fin n)),
          (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
            fractionalSize G w ≤ (P.card : ℝ) + η * (n : ℝ) ^ 2

lemma HaxellRodlRounding.eventually_apply (h : HaxellRodlRounding)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ),
        IsFractionalPacking G w →
          ∃ P : Finset (Finset (Fin n)),
            (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
              fractionalSize G w ≤ (P.card : ℝ) + η * (n : ℝ) ^ 2 :=
  h η hη

/-- The asymptotic weakening of the sharp Gruslys--Letzter fractional theorem.
It is already sufficient for the exact epsilon formulation of Problem 76. -/
def AsymptoticFractional : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n),
      ∃ wR wB : Finset (Fin n) → ℝ,
        IsFractionalPacking G wR ∧ IsFractionalPacking Gᶜ wB ∧
          (1 / 4 - δ) * (n : ℝ) ^ 2 ≤
            fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB

/-- The exact uniform epsilon formulation of the affirmative answer to
Erdős Problem 76. -/
def Resolution : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ G : SimpleGraph (Fin n),
      (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ (monoPackingNumber G : ℝ)

end

end Erdos76
