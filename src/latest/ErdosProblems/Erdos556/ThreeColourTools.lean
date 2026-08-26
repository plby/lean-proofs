import ErdosProblems.Erdos556.Basic

/-! Elementary interfaces for the three colour graphs. -/

namespace Erdos556

open SimpleGraph

instance ThreeColouring.graphDecidableAdj {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (i : Fin 3) : DecidableRel (c.graph i).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ c.colour u v = i))

theorem fin_three_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega

theorem ThreeColouring.isClique_of_excluded_colours {V : Type*}
    (c : ThreeColouring V) (S : Finset V) (i j k : Fin 3)
    (hall : ∀ a : Fin 3, a = i ∨ a = j ∨ a = k)
    (hi : ∀ u ∈ S, ∀ v ∈ S, ¬ (c.graph i).Adj u v)
    (hj : ∀ u ∈ S, ∀ v ∈ S, ¬ (c.graph j).Adj u v) : (c.graph k).IsClique (S : Set V) := by
  intro u hu v hv huv
  rcases hall (c.colour u v) with h | h | h
  · exact (hi u hu v hv ⟨huv, h⟩).elim
  · exact (hj u hu v hv ⟨huv, h⟩).elim
  · exact ⟨huv, h⟩

end Erdos556
