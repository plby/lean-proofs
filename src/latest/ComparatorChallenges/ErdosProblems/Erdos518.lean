/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos518

variable {V : Type u}

def IsPath (G : SimpleGraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.Nodup ∧ p.IsChain G.Adj

variable {V : Type u}

def IsPathCover (G : SimpleGraph V) (ps : List (List V)) : Prop :=
  (∀ p ∈ ps, IsPath G p) ∧ ∀ v : V, ∃ p ∈ ps, v ∈ p

variable {V : Type u}

def HasPathCoverAtMost (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ ps : List (List V), ps.length ≤ k ∧ IsPathCover G ps

def Erdos518For (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  HasPathCoverAtMost G (Nat.sqrt n) ∨ HasPathCoverAtMost Gᶜ (Nat.sqrt n)

theorem erdos_518 (n : ℕ) (G : SimpleGraph (Fin n)) : Erdos518For n G := by
  sorry

end Erdos518
