import Mathlib

namespace Erdos666

open SimpleGraph

abbrev hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → ZMod 2) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h => by

    simpa [hammingDist_comm] using h⟩
  loopless := ⟨fun x h => by

    simp [hammingDist] at h⟩
def HasCycleOfLength {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = k
end Erdos666

attribute [local instance] Classical.propDecidable


open SimpleGraph

namespace Erdos666

theorem not_erdos_666 :
  ¬ (∀ ε > 0,
      ∃ N,
        ∀ n ≥ N,
          ∀ G ≤ hypercubeGraph n,
            (G.edgeFinset.card : ℝ) ≥ ε * n * 2 ^ (n - 1) →
              HasCycleOfLength G 6) := by
  sorry

end Erdos666
