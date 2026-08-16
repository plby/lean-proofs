import ErdosProblems.Erdos920.Container
import ErdosProblems.Erdos920.MarkedTree

/-!
# Turning tuple counts into marked-tree path counts

This file supplies the bookkeeping bridge used in the proof of the forward
independent tuple bound for the projective `D*` construction.  A chronological
tuple is sent to its reverse list, since the container development stores the
newest entry at the head of a history.  The map is injective.  Consequently,
once the images of the tuples are known to be paths with at most `w` unmarked
steps, `MarkedTree.card_boundedPaths_le` applies directly.

The final theorem specializes this observation to `Container.CanExtend`.
It deliberately keeps the marked predicate abstract: the projective
poor/popular argument is responsible for defining that predicate and proving
the two local branching bounds.
-/

namespace Erdos920.TupleBound

open Erdos920

noncomputable section

/-! ## The tuple-to-history injection -/

/-- A tuple in chronological order, represented in the reverse-history
convention used by `Container` and `MarkedTree`. -/
def tupleHistory {alpha : Type*} {m : ℕ} (x : Fin m → alpha) : List alpha :=
  (List.ofFn x).reverse

@[simp] theorem length_tupleHistory {alpha : Type*} {m : ℕ}
    (x : Fin m → alpha) : (tupleHistory x).length = m := by
  simp [tupleHistory]

/-- Reversing `List.ofFn` loses no information. -/
theorem tupleHistory_injective {alpha : Type*} {m : ℕ} :
    Function.Injective (tupleHistory : (Fin m → alpha) → List alpha) := by
  intro x y hxy
  apply List.ofFn_injective
  have := congrArg List.reverse hxy
  simpa [tupleHistory] using this

/-! ## The generic marked-tree bridge -/

variable {alpha : Type*} [DecidableEq alpha]

/-- Any finite collection of tuples which maps into the bounded-path finset
has cardinality at most the cardinality of that finset. -/
theorem card_tuples_le_boundedPaths
    {m w : ℕ}
    (tuples : Finset (Fin m → alpha))
    (children : List alpha → Finset alpha)
    (marked : List alpha → alpha → Bool)
    (hpath : ∀ x ∈ tuples,
      MarkedTree.IsPath children (tupleHistory x))
    (hunmarked : ∀ x ∈ tuples,
      (MarkedTree.pathSignature marked (tupleHistory x)).count false ≤ w) :
    tuples.card ≤ (MarkedTree.boundedPaths children marked m w).card := by
  classical
  refine Finset.card_le_card_of_injOn tupleHistory ?_ ?_
  · intro x hx
    exact (MarkedTree.mem_boundedPaths_iff children marked (tupleHistory x) m w).2
      ⟨hpath x hx, length_tupleHistory x, hunmarked x hx⟩
  · intro x _ y _ hxy
    exact tupleHistory_injective hxy

/-- The marked-tree estimate, already packaged for a finite set of tuples.
This is the main generic API used by the projective construction. -/
theorem card_tuples_le_of_markedTree
    {Delta h m w : ℕ}
    (tuples : Finset (Fin m → alpha))
    (children : List alpha → Finset alpha)
    (marked : List alpha → alpha → Bool)
    (hpath : ∀ x ∈ tuples,
      MarkedTree.IsPath children (tupleHistory x))
    (hunmarked : ∀ x ∈ tuples,
      (MarkedTree.pathSignature marked (tupleHistory x)).count false ≤ w)
    (hchildren : ∀ σ, (children σ).card ≤ Delta)
    (hmarked : ∀ σ,
      ((children σ).filter fun x ↦ marked σ x = true).card ≤ h)
    (hhDelta : h ≤ Delta) (hwm : w ≤ m) :
    tuples.card ≤ 2 ^ m * Delta ^ w * h ^ (m - w) := by
  exact (card_tuples_le_boundedPaths tuples children marked hpath hunmarked).trans
    (MarkedTree.card_boundedPaths_le children marked hchildren hmarked hhDelta hwm)

/-! ## Specialization to container consistency -/

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- All available extensions of a reverse history by a vertex from `vertices`.
The incidence of the new pair, as well as every forward-independence
compatibility condition with the old history, is contained in
`Container.CanExtend`. -/
def consistentChildren (vertices : Finset (P × P))
    (R : P → P → Prop) [DecidableRel R]
    (σ : List (P × P)) : Finset (P × P) := by
  classical
  exact vertices.filter fun p ↦ Container.CanExtend R p σ

@[simp] theorem mem_consistentChildren_iff
    (vertices : Finset (P × P)) (R : P → P → Prop)
    [DecidableRel R] (p : P × P) (σ : List (P × P)) :
    p ∈ consistentChildren vertices R σ ↔
      p ∈ vertices ∧ Container.CanExtend R p σ := by
  classical
  simp [consistentChildren]

/-- Following the `CanExtend` child finsets is equivalent to container
consistency together with membership of every entry in the ambient vertex
finset. -/
theorem isPath_consistentChildren_iff
    (vertices : Finset (P × P)) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) :
    MarkedTree.IsPath (consistentChildren vertices R) σ ↔
      Container.Consistent R σ ∧ ∀ p ∈ σ, p ∈ vertices := by
  induction σ with
  | nil => simp [MarkedTree.IsPath]
  | cons p σ ih =>
      simp only [MarkedTree.IsPath, Container.consistent_cons_iff,
        mem_consistentChildren_iff, ih, List.mem_cons]
      aesop

/-- A specialized marked-tree bound for tuples of incident pairs satisfying
the container consistency relation. -/
theorem card_consistent_tuples_le_of_markedTree
    {Delta h m w : ℕ}
    (vertices : Finset (P × P)) (R : P → P → Prop)
    [DecidableRel R]
    (tuples : Finset (Fin m → (P × P)))
    (marked : List (P × P) → (P × P) → Bool)
    (hconsistent : ∀ x ∈ tuples, Container.Consistent R (tupleHistory x))
    (hmem : ∀ x ∈ tuples, ∀ i, x i ∈ vertices)
    (hunmarked : ∀ x ∈ tuples,
      (MarkedTree.pathSignature marked (tupleHistory x)).count false ≤ w)
    (hchildren : ∀ σ, (consistentChildren vertices R σ).card ≤ Delta)
    (hmarked : ∀ σ,
      ((consistentChildren vertices R σ).filter
        fun x ↦ marked σ x = true).card ≤ h)
    (hhDelta : h ≤ Delta) (hwm : w ≤ m) :
    tuples.card ≤ 2 ^ m * Delta ^ w * h ^ (m - w) := by
  apply card_tuples_le_of_markedTree tuples
    (consistentChildren vertices R) marked
  · intro x hx
    rw [isPath_consistentChildren_iff]
    refine ⟨hconsistent x hx, ?_⟩
    intro p hp
    have hp' : p ∈ List.ofFn x := by
      simpa [tupleHistory] using hp
    rcases List.mem_ofFn.mp hp' with ⟨i, rfl⟩
    exact hmem x hx i
  · exact hunmarked
  · exact hchildren
  · exact hmarked
  · exact hhDelta
  · exact hwm

end

end Erdos920.TupleBound
