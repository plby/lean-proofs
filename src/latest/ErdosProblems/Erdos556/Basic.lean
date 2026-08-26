import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# Three-colour cycle Ramsey definitions

Colourings are symmetric functions on ordered pairs. The diagonal is ignored;
each colour graph is loopless. Containment means a (not necessarily induced)
copy of Mathlib's canonical cycle graph.
-/

namespace Erdos556

open SimpleGraph
open scoped SimpleGraph

/-- A colouring of the edges of a complete graph with three colours.
Values on the diagonal have no significance. -/
structure ThreeColouring (V : Type*) where
  colour : V → V → Fin 3
  symm : ∀ u v, colour u v = colour v u

/-- The simple graph consisting of the edges of one colour. -/
def ThreeColouring.graph {V : Type*} (c : ThreeColouring V) (i : Fin 3) :
    SimpleGraph V where
  Adj u v := u ≠ v ∧ c.colour u v = i
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, (c.symm v u).trans h.2⟩⟩
  loopless := ⟨by simp⟩

@[simp] theorem ThreeColouring.graph_adj {V : Type*} (c : ThreeColouring V)
    (i : Fin 3) (u v : V) :
    (c.graph i).Adj u v ↔ u ≠ v ∧ c.colour u v = i := Iff.rfl

/-- Pull a colouring back along any map of vertex sets. -/
def ThreeColouring.comap {V W : Type*} (c : ThreeColouring V) (f : W → V) :
    ThreeColouring W where
  colour u v := c.colour (f u) (f v)
  symm u v := c.symm (f u) (f v)

theorem ThreeColouring.graph_comap {V W : Type*} (c : ThreeColouring V)
    (f : W ↪ V) (i : Fin 3) :
    (c.comap f).graph i = (c.graph i).comap f := by
  ext u v
  simp only [graph_adj, comap, SimpleGraph.comap_adj]
  exact and_congr_left fun _ => f.injective.ne_iff.symm

/-- Every three-colouring on `m` vertices contains a monochromatic `n`-cycle. -/
def IsRamseyOrder (n m : ℕ) : Prop :=
  ∀ c : ThreeColouring (Fin m), ∃ i : Fin 3, cycleGraph n ⊑ c.graph i

/-- The three-colour cycle Ramsey number, as the infimum of the admissible
natural-number orders. Qualitative existence is proved separately. -/
noncomputable def ramseyNumber (n : ℕ) : ℕ :=
  sInf {m : ℕ | IsRamseyOrder n m}

theorem IsRamseyOrder.mono {n a b : ℕ} (h : IsRamseyOrder n a) (hab : a ≤ b) :
    IsRamseyOrder n b := by
  intro c
  let f : Fin a ↪ Fin b := Fin.castLEEmb hab
  obtain ⟨i, hi⟩ := h (c.comap f)
  refine ⟨i, ?_⟩
  rw [c.graph_comap f i] at hi
  exact hi.trans (SimpleGraph.Embedding.comap f (c.graph i)).isContained

theorem IsRamseyOrder.of_equiv {n m : ℕ} {V : Type*}
    (h : IsRamseyOrder n m) (e : Fin m ≃ V) (c : ThreeColouring V) :
    ∃ i : Fin 3, cycleGraph n ⊑ c.graph i := by
  obtain ⟨i, hi⟩ := h (c.comap e.toEmbedding)
  refine ⟨i, ?_⟩
  rw [c.graph_comap e.toEmbedding i] at hi
  exact hi.trans (SimpleGraph.Embedding.comap e.toEmbedding (c.graph i)).isContained

end Erdos556
