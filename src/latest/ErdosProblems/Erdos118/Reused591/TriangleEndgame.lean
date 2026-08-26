import ErdosProblems.Erdos118.Reused591.SharedTailHistory

namespace Erdos118.Reused591

/-!
# Recovering the triangle from three shared-word winning plays

These are the endpoint transport lemmas for the architect construction.
They require the actual three winning boards and their shared literal
coordinate words; constructing those boards remains a separate task.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_of_done {N H : Set ℕ} {blue : SimpleGraph G}
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    {p : Concrete.Hist N} (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hp : p.position.pending = none) (hd : Concrete.done p.position.board = true) :
    Winning blue (p.position.mode.getD false) p.position.board := by
  have hk : (exactGame N blue).kind p =
      .terminal (payoff blue (p.position.mode.getD false) p.position.board) :=
    (Concrete.kind_terminal_iff (payoff blue) p _).mpr ⟨hp, hd, rfl⟩
  exact (payoff_true_iff blue _ _).mp (hwin p _ .refl hk)

theorem triangle_of_shared_coordinates {blue : SimpleGraph G} {st su tu : Board}
    {m₁ m₂ m₃ : Bool} (hst : Winning blue m₁ st) (hsu : Winning blue m₂ su)
    (htu : Winning blue m₃ tu)
    (hs : st.left.coordinates = su.left.coordinates)
    (ht : st.right.coordinates = tu.left.coordinates)
    (hu : su.right.coordinates = tu.right.coordinates) : ¬ blue.CliqueFree 3 := by
  classical
  obtain ⟨s, t, hclear₁, hblue₁, _⟩ := hst
  obtain ⟨s', u, hclear₂, hblue₂, _⟩ := hsu
  obtain ⟨t', u', hclear₃, hblue₃, _⟩ := htu
  have hss : s = s' := literal_vertex_unique
    (hclear₁.1.coordinates.trans (hs.trans hclear₂.1.coordinates.symm))
  have htt : t = t' := literal_vertex_unique
    (hclear₁.2.1.coordinates.trans (ht.trans hclear₃.1.coordinates.symm))
  have huu : u = u' := literal_vertex_unique
    (hclear₂.2.1.coordinates.trans (hu.trans hclear₃.2.1.coordinates.symm))
  subst s'
  subst t'
  subst u'
  intro hfree
  exact hfree {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hblue₁, hblue₂, hblue₃⟩)

#print axioms winning_of_done
#print axioms triangle_of_shared_coordinates

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
