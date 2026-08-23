/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 780

Informal authors: Noga Alon, Peter Frankl, László Lovász
Formal authors: Aristotle Contributors

If the `r`-subsets of an `n`-element set are colored with `t` colors and
`k * r + (t - 1) * (k - 1) ≤ n`, one color contains `k` pairwise disjoint
edges.

Reference: https://www.erdosproblems.com/780
-/

namespace Erdos780

abbrev Edge (n r : ℕ) := {s : Finset (Fin n) // s.card = r}

def HasMonoMatching {n r t : ℕ} (c : Edge n r → Fin t) (k : ℕ) : Prop :=
  ∃ color : Fin t, ∃ e : Fin k → Edge n r,
    (∀ i, c (e i) = color) ∧
    ∀ i j : Fin k, i ≠ j → Disjoint (e i).1 (e j).1

/-- Send an edge along an injection of finite vertex sets. -/
def Edge.map {m n r : ℕ} (f : Fin m ↪ Fin n) (e : Edge m r) : Edge n r :=
  ⟨e.1.map f, (Finset.card_map f).trans e.2⟩

@[simp] theorem Edge.coe_map {m n r : ℕ} (f : Fin m ↪ Fin n) (e : Edge m r) :
    (Edge.map f e).1 = e.1.map f := rfl

/-- Restrict a coloring on `Fin n` to the copy of `Fin m` selected by `f`. -/
def restrictColor {m n r t : ℕ} (f : Fin m ↪ Fin n) (c : Edge n r → Fin t) :
    Edge m r → Fin t := fun e ↦ c (e.map f)

/-- A matching for the restriction is a matching for the original coloring. -/

theorem erdos_780 {n k r t : ℕ} (hr : 1 ≤ r) (ht : 1 ≤ t)
    (hn : k * r + (t - 1) * (k - 1) ≤ n) (c : Edge n r → Fin t) :
    HasMonoMatching c k := by
  sorry

end Erdos780
