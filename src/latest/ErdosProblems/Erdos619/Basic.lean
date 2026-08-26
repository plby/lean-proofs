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
import Mathlib

namespace Erdos619

/-- The number of new edges in `H` that were not already present in `G`. -/
noncomputable def addedEdgeCount {n : ℕ} (G H : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact (H.edgeFinset \ G.edgeFinset).card

/-- `IsHR r G m` says that `m` is the value of `h_r(G)`: it is achieved by a
triangle-free supergraph of `G` with extended diameter at most `r`, and is minimal among all such
supergraphs.

Using `ediam` avoids the junk value of `diam` on disconnected graphs, where `diam` is defined as
`ediam.toNat` and hence maps infinite extended diameter to `0`. -/
def IsHR {n : ℕ} (r : ℕ) (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∃ H : SimpleGraph (Fin n),
    G ≤ H ∧
      H.CliqueFree 3 ∧
        H.ediam ≤ (r : ℕ∞) ∧
          addedEdgeCount G H = m ∧
            ∀ K : SimpleGraph (Fin n),
              G ≤ K → K.CliqueFree 3 → K.ediam ≤ (r : ℕ∞) → m ≤ addedEdgeCount G K

/-- The original positive conjecture in Erdős Problem 619. -/
def erdos_619_conjecture : Prop :=
  ∃ c : ℝ,
    0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (m : ℕ),
        G.Connected →
          G.CliqueFree 3 →
            IsHR 4 G m →
              (m : ℝ) < (1 - c) * n

/-- The target statement for this project: the negation of Erdős Problem 619's conjecture. -/
def erdos_619 : Prop :=
  ¬ erdos_619_conjecture

end Erdos619
