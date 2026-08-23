/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

namespace Erdos762

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.unusedSimpArgs false


open SimpleGraph

open scoped Classical in
def IsCochromaticColoring {V : Type*} (G : SimpleGraph V) {α : Type*} (c : V → α) : Prop :=
  ∀ i, G.IsClique (c ⁻¹' {i}) ∨ G.IsIndepSet (c ⁻¹' {i})
open scoped Classical in
def CochromaticColorable {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ c : V → Fin n, IsCochromaticColoring G c
open scoped Classical in
noncomputable def cochromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ :=
  sInf { n : ℕ∞ | ∃ m : ℕ, n = m ∧ CochromaticColorable G m }
open scoped Classical in
def erdos_762 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
  G.CliqueFree 5 →
  4 ≤ cochromaticNumber G →
  G.chromaticNumber ≤ cochromaticNumber G + 2
end Erdos762


open scoped Classical in
theorem Erdos762.not_erdos_762 :
    Not Erdos762.erdos_762
  := by
  sorry
