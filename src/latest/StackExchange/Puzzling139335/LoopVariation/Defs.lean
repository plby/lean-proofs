import StackExchange.Puzzling139335.ArcVariation

/-!
# Concrete cyclic finite-resolution scores

A cyclic chain pays the truncated chord score between successive vertices and
also on the closing chord. The empty chain has score zero. The admissible
chains are actual finite increasing lists in a parameter set; no regularity
or finiteness property is incorporated into the definition.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

variable {α X : Type*} [PseudoMetricSpace X]

/-- Close a nonempty finite chain by repeating its first vertex. -/
def cycleScore (ε : ℝ) (f : α → X) : List α → ℝ
  | [] => 0
  | x :: xs => chainScore ε f ((x :: xs) ++ [x])

/-- Scores of concrete cyclically closed increasing parameter chains. -/
def cycleScoresOn [LE α] (ε : ℝ) (f : α → X) (s : Set α) : Set ℝ :=
  {r | ∃ xs, IsChainOn s xs ∧ r = cycleScore ε f xs}

/-- Cyclic truncated variation as the supremum of concrete cyclic scores. -/
def loopVariationOn [LE α] (ε : ℝ) (f : α → X) (s : Set α) : ℝ :=
  sSup (cycleScoresOn ε f s)

@[simp] theorem cycleScore_nil (ε : ℝ) (f : α → X) :
    cycleScore ε f [] = 0 := rfl

theorem cycleScore_nonneg (ε : ℝ) (f : α → X) (xs : List α) :
    0 ≤ cycleScore ε f xs := by
  cases xs with
  | nil => rfl
  | cons x xs => exact chainScore_nonneg ε f ((x :: xs) ++ [x])

theorem chainScore_le_cycleScore (ε : ℝ) (f : α → X) (xs : List α) :
    chainScore ε f xs ≤ cycleScore ε f xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      simpa only [chainScore, add_zero, cycleScore] using
        chainScore_add_le_append ε f (x :: xs) [x]

theorem zero_mem_cycleScoresOn [LE α] (ε : ℝ) (f : α → X) (s : Set α) :
    0 ∈ cycleScoresOn ε f s :=
  ⟨[], by simp [IsChainOn], rfl⟩

theorem cycleScoresOn_nonempty [LE α] (ε : ℝ) (f : α → X) (s : Set α) :
    (cycleScoresOn ε f s).Nonempty := ⟨0, zero_mem_cycleScoresOn ε f s⟩

theorem cycleScore_le_loopVariationOn [LE α] {ε : ℝ} {f : α → X} {s : Set α}
    (hb : BddAbove (cycleScoresOn ε f s)) {xs : List α} (hxs : IsChainOn s xs) :
    cycleScore ε f xs ≤ loopVariationOn ε f s :=
  le_csSup hb ⟨xs, hxs, rfl⟩

theorem loopVariationOn_nonneg [LE α] {ε : ℝ} {f : α → X} {s : Set α}
    (hb : BddAbove (cycleScoresOn ε f s)) : 0 ≤ loopVariationOn ε f s :=
  le_csSup hb (zero_mem_cycleScoresOn ε f s)

end

end Puzzling139335.LoopVariation
