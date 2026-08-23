/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped BigOperators

noncomputable section


variable {V : Type u} [Fintype V] [DecidableEq V]

namespace Erdos833

variable {V : Type u} [Fintype V] [DecidableEq V]

open scoped Classical in
abbrev Hypergraph (V : Type u) [Fintype V] [DecidableEq V] := Finset (Finset V)

end Erdos833

namespace Erdos833

variable {V : Type u} [Fintype V] [DecidableEq V]

open scoped Classical in
def IsUniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

end Erdos833

namespace Erdos833

open scoped Classical in
def Monochromatic {κ : Type*} (c : V → κ) (e : Finset V) : Prop :=
  ∀ x ∈ e, ∀ y ∈ e, c x = c y

end Erdos833

namespace Erdos833

open scoped Classical in
def IsProper {κ : Type*} (H : Hypergraph V) (c : V → κ) : Prop :=
  ∀ e ∈ H, ¬ Monochromatic c e

end Erdos833

namespace Erdos833

open scoped Classical in
def Colorable (H : Hypergraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProper H c

end Erdos833

namespace Erdos833

open scoped Classical in
def HasChromaticNumber (H : Hypergraph V) (k : ℕ) : Prop :=
  Colorable H k ∧ ∀ q < k, ¬ Colorable H q

end Erdos833

namespace Erdos833

open scoped Classical in
def degree (H : Hypergraph V) (v : V) : ℕ :=
  (H.filter fun e ↦ v ∈ e).card

end Erdos833

namespace Erdos833

open scoped Classical in
theorem erdos_833 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (r : ℕ), 2 ≤ r → ∀ H : Hypergraph W,
          IsUniform H r → HasChromaticNumber H 3 →
            ∃ v : W, (1 + c) ^ r ≤ degree H v := by
  sorry

end Erdos833

end
