/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos926

/-! ## The forbidden graph -/

/-- An index for an unordered pair, represented in increasing order. -/
def PairIndex (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}

/-- The vertices of `Hₖ`: center, branches, and pair-subdivision vertices. -/
abbrev HVertex (k : ℕ) := Unit ⊕ (Fin k ⊕ PairIndex k)

/-- Adjacency in the graph from Problem 926. -/
def HAdj {k : ℕ} : HVertex k → HVertex k → Prop
  | Sum.inl _, Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inl _), Sum.inl _ => True
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr p) => i = p.1.1 ∨ i = p.1.2
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inl i) => i = p.1.1 ∨ i = p.1.2
  | _, _ => False

/-- The graph `Hₖ` in Erdős Problem 926. -/
def Hk (k : ℕ) : SimpleGraph (HVertex k) where
  Adj := HAdj
  symm := ⟨by
    rintro (_ | (_ | _)) (_ | (_ | _)) <;> simp_all [HAdj]⟩
  loopless := ⟨by
    rintro (_ | (_ | _)) <;> simp [HAdj]⟩

theorem erdos_926 :
    ∀ k : ℕ, 4 ≤ k →
      (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (Hk k) : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

end Erdos926
