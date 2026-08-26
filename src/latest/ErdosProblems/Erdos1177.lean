import ErdosProblems.Erdos1177.Proof

/-!
Lean 4.33.0 port of Eric Li's Lean 4.28.0 formalization, developed with Aristotle.
Upstream release v1.0.0; source and attribution are recorded in Erdos1177/README.md.
The source namespace is renamed to keep the independent Erdos593 import separate.
-/

open Cardinal

namespace Erdos1177

universe u

/-- The three answers are yes, no, and yes, respectively. -/
theorem erdos_1177 :
    (∀ G : FTS, G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) →
      ∃ (W : Type u) (H : Hypergraph W),
        H.IsTripleSystem ∧ H.HasChromatic (Cardinal.aleph 1 : Cardinal.{u}) ∧
        ¬ G.Embeds H ∧ #W ≤
          (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u}))) ∧
    (∃ G H : FTS,
      G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) ∧
      H.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) ∧
      ¬ ∃ (W : Type u) (K : Hypergraph W),
        K.IsTripleSystem ∧ K.HasChromatic (Cardinal.aleph 1 : Cardinal.{u}) ∧
        ¬ G.Embeds K ∧ ¬ H.Embeds K) ∧
    (∀ (G : FTS) (κ : Cardinal.{u}), ℵ₀ < κ → G.FGnonempty κ →
      ∀ lam : Cardinal.{u}, ℵ₀ < lam → G.FGnonempty lam) := by
  exact ⟨problem_1177_part1_aleph_one, problem_1177_part2_aleph_one,
    problem_1177_part3_unconditional⟩

end Erdos1177

#print axioms Erdos1177.problem_1177_part1_aleph_one
#print axioms Erdos1177.problem_1177_part2_aleph_one
#print axioms Erdos1177.problem_1177_part3_unconditional
#print axioms Erdos1177.erdos_1177
