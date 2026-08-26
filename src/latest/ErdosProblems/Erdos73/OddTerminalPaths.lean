import ErdosProblems.Erdos73.OddPathBarrierHitting
import ErdosProblems.Erdos73.OddPathLift

/-! The odd terminal-path packing and covering theorem, proved from finite matching theory. -/

namespace Erdos73

open SimpleGraph Finset OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : Finset V}

open scoped Classical in
theorem OddPathBarrierWitness.hits_oddTerminalPaths {k : ℕ}
    (B : OddPathBarrierWitness G A k) : HitsOddTerminalPaths G A B.deletion := by
  intro Q hQ hdis
  obtain ⟨P, hP, hproj⟩ := exists_augmentingPath_of_oddTerminalPath hQ
  apply B.not_surviving_augmentingPath hP
  intro x hx hxX
  exact Finset.disjoint_left.mp hdis (hproj x hx) hxX

theorem odd_terminal_paths_packing_or_covering (G : SimpleGraph V) (A : Finset V) (k : ℕ) :
    HasOddTerminalPathPacking G A k ∨
      ∃ X : Finset V, X.card ≤ 2 * k - 2 ∧ HitsOddTerminalPaths G A X := by
  classical
  by_cases hpack : HasOddTerminalPathPacking G A k
  · exact Or.inl hpack
  · obtain ⟨B⟩ := exists_oddPathBarrierWitness hpack
    exact Or.inr ⟨B.deletion, by have hh := B.deletion_card; omega, B.hits_oddTerminalPaths⟩

end Erdos73
