import ErdosProblems.Erdos591.ArchitectTriangle
import ErdosProblems.Erdos591.BuilderBranch

/-! # The exact positive relation on the literal good-sequence carrier -/

namespace Erdos591.Positive.Game.Payoff

open Ordinal Erdos591.Negative.Exact

theorem triangle_free_red_set (blue : SimpleGraph G) (htri : blue.CliqueFree 3) :
    ∃ S : Set G, blueᶜ.IsClique S ∧ typeLT S = (ω ^ (ω ^ 2) : Ordinal.{0}) := by
  obtain ⟨H, hHN, hH, b, _v, _hvalue, _hmono, hcases⟩ :=
    uniformization (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) blue
  rcases hcases with ⟨σ, hwin⟩ | hbuilder
  · exact (architect_triangle hHN hH blue hwin htri).elim
  · exact Macro.Forest.builder_red_set hH hHN b blue hbuilder htri

#print axioms triangle_free_red_set

end Erdos591.Positive.Game.Payoff
