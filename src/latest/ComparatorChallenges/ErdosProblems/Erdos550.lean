/-
Upstream material by Eric Li; all rights reserved.
Definitions adapted for independent statement checking.
-/
import Mathlib

open SimpleGraph

namespace Erdos550

/-- The least order forcing a red copy of the first graph or a blue copy of the second. -/
noncomputable def ramsey {α β : Type*} (J : SimpleGraph α) (L : SimpleGraph β) : ℕ :=
  sInf {N | ∀ G : SimpleGraph (Fin N), J ⊑ G ∨ L ⊑ Gᶜ}

/-- A complete multipartite graph with the prescribed part sizes. -/
noncomputable def Kmult (k : ℕ) (m : Fin k → ℕ) :
    SimpleGraph ((i : Fin k) × Fin (m i)) :=
  completeMultipartiteGraph (fun i => Fin (m i))

theorem erdos_550 (k : ℕ) (hk : 2 ≤ k) (m : Fin k → ℕ)
    (hmono : Monotone m) (hpos : 1 ≤ m ⟨0, by omega⟩) :
    ∃ n0 : ℕ, ∀ n, n0 ≤ n → ∀ {V : Type} [Fintype V] (T : SimpleGraph V),
      T.IsTree → Fintype.card V = n →
      ramsey T (Kmult k m) ≤
        (k - 1) * (ramsey T (Kmult 2 (fun j => m (Fin.castLE hk j))) - 1)
          + m ⟨0, by omega⟩ := by
  sorry

end Erdos550
