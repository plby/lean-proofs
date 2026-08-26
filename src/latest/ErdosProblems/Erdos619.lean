/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the original proof repository.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 619.
Informal proof: Claude Fable 5.
Formal proof: GPT-5.5 with Codex, following a formalization sketch and guidance
from Claude Fable 5. Human contributor and publisher: Nick (Nikolas) Kuhn.
Source: https://www.erdosproblems.com/619#post-6986
https://github.com/nick-kuhn/erdos-619/tree/7f65718b8c1019ecc24e6c9a6b04ec4c66a4e26f
Original Lean/Mathlib version: 4.28.0.
Original Mathlib revision: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos619.Pendant
import ErdosProblems.Erdos619.Statement

open SimpleGraph

namespace Erdos619

/-- The two repositories' edge-counting conventions agree. -/
lemma addedEdgeCount_eq_ncard {n : ℕ} (G H : SimpleGraph (Fin n)) :
    addedEdgeCount G H = ((H \ G).edgeSet).ncard := by
  classical
  rw [edgeSet_sdiff, ← coe_edgeFinset H, ← coe_edgeFinset G, ← Finset.coe_sdiff,
    Set.ncard_coe_finset, addedEdgeCount]

/-- If `m` satisfies the `IsHR r G` predicate, then it equals the formal-conjectures
quantity `Erdos619.minNewEdges r G`. -/
lemma IsHR.minNewEdges_eq {n r m : ℕ} {G : SimpleGraph (Fin n)} (h : IsHR r G m) :
    Erdos619.minNewEdges r G = m := by
  obtain ⟨H, hle, hfree, hdiam, hcount, hmin⟩ := h
  have hmem : m ∈ {k | ∃ H' : SimpleGraph (Fin n),
      G ≤ H' ∧ H'.CliqueFree 3 ∧ H'.ediam ≤ (r : ℕ∞) ∧ ((H' \ G).edgeSet).ncard = k} :=
    ⟨H, hle, hfree, hdiam, by rw [← addedEdgeCount_eq_ncard]; exact hcount⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨m, hmem⟩ ?_)
  rintro k ⟨K, hKle, hKfree, hKdiam, rfl⟩
  rw [← addedEdgeCount_eq_ncard]
  exact hmin K hKle hKfree hKdiam

/-- The formal-conjectures conjecture implies the source's
`erdos_619_conjecture`: specialise the vertex type to `Fin n` and convert the `IsHR`
hypothesis via `IsHR.minNewEdges_eq`. -/
lemma erdos_619_conjecture_of_fc
    (hfc : ∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      G.Connected → G.CliqueFree 3 →
      (Erdos619.minNewEdges 4 G : ℝ) < (1 - c) * Fintype.card V) :
    erdos_619_conjecture := by
  obtain ⟨c, hc, hbound⟩ := hfc
  refine ⟨c, hc, fun n G m hconn hfree hm => ?_⟩
  have h := hbound (Fin n) G hconn hfree
  rw [hm.minNewEdges_eq, Fintype.card_fin] at h
  exact h

theorem not_erdos_619 :
    ¬ (∃ c > (0 : ℝ), ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      G.Connected → G.CliqueFree 3 →
      (minNewEdges 4 G : ℝ) < (1 - c) * Fintype.card V) := by
  intro h
  exact erdos_619_solution (erdos_619_conjecture_of_fc h)

#print axioms not_erdos_619
-- 'Erdos619.not_erdos_619' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms counterexample_family
-- 'Erdos619.counterexample_family' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos619
