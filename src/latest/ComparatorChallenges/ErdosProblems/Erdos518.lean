/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped SimpleGraph

noncomputable section

namespace Erdos518

variable {V : Type u}

open scoped Classical in
def IsPath (G : SimpleGraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ p.IsChain G.Adj

end Erdos518

namespace Erdos518

variable {V : Type u}

open scoped Classical in
def IsPathCover (G : SimpleGraph V) (ps : List (List V)) : Prop :=
  (∀ p ∈ ps, IsPath G p) ∧ ∀ v : V, ∃ p ∈ ps, v ∈ p

end Erdos518

namespace Erdos518

variable {V : Type u}

open scoped Classical in
def HasPathCoverAtMost (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ ps : List (List V), ps.length ≤ k ∧ IsPathCover G ps

end Erdos518

namespace Erdos518

open scoped Classical in
def Erdos518For (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  HasPathCoverAtMost G (Nat.sqrt n) ∨ HasPathCoverAtMost Gᶜ (Nat.sqrt n)

end Erdos518

namespace Erdos518

open scoped Classical in
theorem erdos518 (n : ℕ) (G : SimpleGraph (Fin n)) : Erdos518For n G := by
  sorry

end Erdos518

end
