/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1034

noncomputable section

def Y_set {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (T :
  Finset V) : Finset V :=
  Finset.univ.filter (fun v => 2 ≤ (G.neighborFinset v ∩ T).card)
def MaTangGraph (n : ℕ) (α : ℝ) (s : ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    let b := ⌊α * n⌋₊
    let uB := (u : ℕ) < b
    let vB := (v : ℕ) < b
    (uB ≠ vB) ∨ (uB ∧ vB ∧ (u : ℕ) / s = (v : ℕ) / s ∧ u ≠ v)
  symm := by
    constructor
    intro u v h
    dsimp at h ⊢
    rcases h with h | ⟨huB, hvB, hdiv, huv⟩
    · exact Or.inl (Ne.symm h)
    · exact Or.inr ⟨hvB, huB, hdiv.symm, Ne.symm huv⟩
  loopless := by
    constructor
    intro u
    simp
instance instDecidableRel_MaTangGraphAdj (n : ℕ) (α : ℝ) (s : ℕ) :
    DecidableRel (MaTangGraph n α s).Adj := by
  intro u v
  dsimp [MaTangGraph]
  exact instDecidableOr
noncomputable def alpha_star : ℝ := 1 - 1 / Real.sqrt 10
noncomputable def c1 (α : ℝ) : ℝ := 2 * α - Real.sqrt (2 - 4 * (α - 1)^2)
section AristotleLemmas

noncomputable def s_func_robust (n : ℕ) (α : ℝ) : ℕ := Nat.ceil (c1 α * n) + 100
end AristotleLemmas

def erdos_1034 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n0 : ℕ,
      ∀ n ≥ n0,
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (G.edgeFinset.card : ℝ) > ((n : ℝ)^2 / 4) →
          ∃ T ∈ G.cliqueFinset 3,
            ((Y_set G T).card : ℝ) > (((1 : ℝ) / 2) - ε) * (n : ℝ)
end

end Erdos1034



namespace Erdos1034

open scoped Classical in
theorem MaTang_main (ε : ℝ) (hε : 0 < ε) :
  ∃ N : ℕ, ∀ n ≥ N,
    let G : SimpleGraph (Fin n) := MaTangGraph n alpha_star (s_func_robust n alpha_star)
    (G.edgeFinset.card : ℝ) > (n^2 : ℝ) / 4 ∧
    ∀ T ∈ G.cliqueFinset 3,
      ((Y_set G T).card : ℝ) ≤ (2 - Real.sqrt (5 / 2) + ε) * n := by
  sorry

end Erdos1034
open scoped Classical in
theorem Erdos1034.not_erdos_1034 :
    Not Erdos1034.erdos_1034
  := by
  sorry
