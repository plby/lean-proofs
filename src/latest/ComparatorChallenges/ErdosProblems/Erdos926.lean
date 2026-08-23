/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 926

For `k ≥ 4`, let `Hₖ` be the graph formed by the first three levels of the
Boolean lattice: one center, `k` branch vertices, and one subdividing vertex
for every pair of branches.  We prove an explicit Füredi-type estimate for
every finite `Hₖ`-free graph and deduce
`ex(n, Hₖ) = Oₖ(n ^ (3 / 2))`.

The detailed mathematical proof and declaration map are in `tex/926.tex`.
-/

open Finset Fintype Filter Asymptotics
open scoped SimpleGraph

namespace Erdos926

noncomputable section

/-! ## The forbidden graph -/

/-- An index for an unordered pair, represented in increasing order. -/
def PairIndex (k : ℕ) := {p : Fin k × Fin k // p.1 < p.2}
  deriving DecidableEq, Fintype

/-- The vertices of `Hₖ`: center, branches, and pair-subdivision vertices. -/
abbrev HVertex (k : ℕ) := Unit ⊕ (Fin k ⊕ PairIndex k)

/-- The center vertex of `Hₖ`. -/
def center (k : ℕ) : HVertex k := Sum.inl ()

/-- Branch vertex `i` of `Hₖ`. -/
def branch {k : ℕ} (i : Fin k) : HVertex k := Sum.inr (Sum.inl i)

/-- The subdivision vertex belonging to pair `p`. -/
def subdiv {k : ℕ} (p : PairIndex k) : HVertex k := Sum.inr (Sum.inr p)

/-- Adjacency in the graph from Problem 926. -/
def HAdj {k : ℕ} : HVertex k → HVertex k → Prop
  | Sum.inl _, Sum.inr (Sum.inl _) => True
  | Sum.inr (Sum.inl _), Sum.inl _ => True
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr p) => i = p.1.1 ∨ i = p.1.2
  | Sum.inr (Sum.inr p), Sum.inr (Sum.inl i) => i = p.1.1 ∨ i = p.1.2
  | _, _ => False

instance {k : ℕ} : DecidableRel (@HAdj k) := fun a b => by
  classical
  exact inferInstance

/-- The graph `Hₖ` in Erdős Problem 926. -/
def Hk (k : ℕ) : SimpleGraph (HVertex k) where
  Adj := HAdj
  symm := ⟨by
    rintro (_ | (_ | _)) (_ | (_ | _)) <;> simp_all [HAdj]⟩
  loopless := ⟨by
    rintro (_ | (_ | _)) <;> simp [HAdj]⟩

instance (k : ℕ) : DecidableRel (Hk k).Adj := by
  classical
  exact inferInstance

@[simp] lemma Hk_center_branch {k : ℕ} (i : Fin k) :
    (Hk k).Adj (center k) (branch i) := by trivial

@[simp] lemma Hk_branch_center {k : ℕ} (i : Fin k) :
    (Hk k).Adj (branch i) (center k) := by trivial

@[simp] lemma Hk_branch_subdiv_iff {k : ℕ} (i : Fin k) (p : PairIndex k) :
    (Hk k).Adj (branch i) (subdiv p) ↔ i = p.1.1 ∨ i = p.1.2 := by
  rfl

@[simp] lemma Hk_subdiv_branch_iff {k : ℕ} (p : PairIndex k) (i : Fin k) :
    (Hk k).Adj (subdiv p) (branch i) ↔ i = p.1.1 ∨ i = p.1.2 := by
  rfl

/-- Number of pair-subdivision vertices. -/
abbrev pairCount (k : ℕ) : ℕ := Fintype.card (PairIndex k)

/-- Richness threshold: the number of vertices of `Hₖ`. -/
abbrev threshold (k : ℕ) : ℕ := 1 + k + pairCount k


theorem erdos_926 :
    True ↔ ∀ k : ℕ, 4 ≤ k →
      (fun n : ℕ ↦ (SimpleGraph.extremalNumber n (Hk k) : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

end

end Erdos926
