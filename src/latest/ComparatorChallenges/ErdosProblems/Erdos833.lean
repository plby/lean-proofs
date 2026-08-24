/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

variable {V : Type u} [Fintype V] [DecidableEq V]

namespace Erdos833

variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev Hypergraph (V : Type u) [Fintype V] [DecidableEq V] := Finset (Finset V)

variable {V : Type u} [Fintype V] [DecidableEq V]

def IsUniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

def Monochromatic {κ : Type*} (c : V → κ) (e : Finset V) : Prop :=
  ∀ x ∈ e, ∀ y ∈ e, c x = c y

def IsProper {κ : Type*} (H : Hypergraph V) (c : V → κ) : Prop :=
  ∀ e ∈ H, ¬ Monochromatic c e

def Colorable (H : Hypergraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProper H c

def HasChromaticNumber (H : Hypergraph V) (k : ℕ) : Prop :=
  Colorable H k ∧ ∀ q < k, ¬ Colorable H q

def degree (H : Hypergraph V) (v : V) : ℕ :=
  (H.filter fun e ↦ v ∈ e).card

theorem erdos_833 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (r : ℕ), 2 ≤ r → ∀ H : Hypergraph W,
          IsUniform H r → HasChromaticNumber H 3 →
            ∃ v : W, (1 + c) ^ r ≤ degree H v := by
  sorry

end Erdos833
