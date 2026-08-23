/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

noncomputable section


namespace Erdos834

open scoped Classical in
abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)

end Erdos834

namespace Erdos834

open scoped Classical in
def isUniformB {α : Type*} [DecidableEq α] (H : Hypergraph α) (r : ℕ) : Bool :=
  decide (∀ e ∈ H, e.card = r)

end Erdos834

namespace Erdos834

open scoped Classical in
def IsUniform {α : Type*} [DecidableEq α] (H : Hypergraph α) (r : ℕ) : Prop :=
  isUniformB H r = true

end Erdos834

namespace Erdos834

open scoped Classical in
def properColoringB {α κ : Type*} [DecidableEq α] [DecidableEq κ]
    (H : Hypergraph α) (c : α → κ) : Bool :=
  decide (∀ e ∈ H, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y)

end Erdos834

namespace Erdos834

open scoped Classical in
def colorableB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (k : ℕ) : Bool :=
  decide (∃ c : α → Fin k, properColoringB H c = true)

end Erdos834

namespace Erdos834

open scoped Classical in
def deleteVertex {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (v : α) : Hypergraph α :=
  H.filter (fun e ↦ v ∉ e)

end Erdos834

namespace Erdos834

open scoped Classical in
def chromaticThreeCriticalB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) : Bool :=
  colorableB H 3 &&
    !colorableB H 2 &&
    decide (∀ e ∈ H, colorableB (H.erase e) 2 = true) &&
    decide (∀ v, colorableB (deleteVertex H v) 2 = true)

end Erdos834

namespace Erdos834

open scoped Classical in
def ChromaticThreeCritical {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  chromaticThreeCriticalB H = true

end Erdos834

namespace Erdos834

open scoped Classical in
def degree {α : Type*} [DecidableEq α] (H : Hypergraph α) (v : α) : ℕ :=
  (H.filter (fun e ↦ v ∈ e)).card

end Erdos834

namespace Erdos834

open scoped Classical in
def minDegreeAtLeastB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (d : ℕ) : Bool :=
  decide (∀ v, d ≤ degree H v)

end Erdos834

namespace Erdos834

open scoped Classical in
def MinDegreeAtLeast {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) (d : ℕ) : Prop :=
  minDegreeAtLeastB H d = true

end Erdos834

namespace Erdos834

open scoped Classical in
def hitsB {α : Type*} [DecidableEq α]
    (H : Hypergraph α) (T : Finset α) : Bool :=
  decide (∀ e ∈ H, ∃ v ∈ e, v ∈ T)

end Erdos834

namespace Erdos834

open scoped Classical in
def transversalThreeCriticalB {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) : Bool :=
  let subsets := (Finset.univ : Finset α).powerset
  decide (∃ T ∈ subsets, T.card = 3 ∧ hitsB H T = true) &&
    !decide (∃ T ∈ subsets, T.card ≤ 2 ∧ hitsB H T = true) &&
    decide (∀ e ∈ H, ∃ T ∈ subsets,
      T.card ≤ 2 ∧ hitsB (H.erase e) T = true)

end Erdos834

namespace Erdos834

open scoped Classical in
def TransversalThreeCritical {α : Type*} [Fintype α] [DecidableEq α]
    (H : Hypergraph α) : Prop :=
  transversalThreeCriticalB H = true

end Erdos834

namespace Erdos834

open scoped Classical in
theorem erdos_834 :
    (∃ H : Hypergraph (Fin 9),
      IsUniform H 3 ∧ ChromaticThreeCritical H ∧ MinDegreeAtLeast H 7) ∧
    (∀ (α : Type) [Fintype α] [DecidableEq α] (H : Hypergraph α),
      IsUniform H 3 → TransversalThreeCritical H →
        ∃ v, degree H v ≤ 6) := by
  sorry

end Erdos834

end
