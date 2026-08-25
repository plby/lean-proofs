import StackExchange.Puzzling139335.ArcVariation.Defs

/-!
# Reversing finite chains and interval parameters

Reversal preserves the concrete finite-chain score because each unoriented
chord occurs once.  Reflecting the parameters of a real interval and reversing
the resulting list therefore gives a score-preserving map on admissible chains.
-/

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {α β X : Type*} [PseudoMetricSpace X]

private theorem chainScore_append_pair_for_reverse (ε : ℝ) (f : α → X)
    (xs : List α) (a b : α) :
    chainScore ε f (xs ++ [a, b]) =
      chainScore ε f (xs ++ [a]) + chord ε (f a) (f b) := by
  induction xs using List.twoStepInduction with
  | nil => simp [chainScore]
  | singleton c => simp [chainScore]
  | cons_cons c d xs ih₁ ih₂ =>
      simpa [chainScore, add_assoc] using
        congrArg (fun r => chord ε (f c) (f d) + r) (ih₂ d)

/-- Reversing a finite chain preserves its score, for every real penalty. -/
theorem chainScore_reverse (ε : ℝ) (f : α → X) (xs : List α) :
    chainScore ε f xs.reverse = chainScore ε f xs := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b xs ih₁ ih₂ =>
      calc
        chainScore ε f (a :: b :: xs).reverse =
            chainScore ε f (b :: xs).reverse + chord ε (f b) (f a) := by
          simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
            List.nil_append] using chainScore_append_pair_for_reverse ε f xs.reverse b a
        _ = chord ε (f a) (f b) + chainScore ε f (b :: xs) := by
          rw [ih₂ b, chord_symm ε (f b) (f a), add_comm]
        _ = chainScore ε f (a :: b :: xs) := rfl

private theorem chainScore_map_for_reverse (ε : ℝ) (f : β → X) (g : α → β)
    (xs : List α) :
    chainScore ε f (xs.map g) = chainScore ε (fun t => f (g t)) xs := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b xs ih₁ ih₂ =>
      simpa only [List.map_cons, chainScore] using
        congrArg (fun r => chord ε (f (g a)) (f (g b)) + r) (ih₂ b)

/-- Reflect the parameters of an increasing chain, then reverse their order. -/
theorem IsChainOn.reflect_Icc {a b : ℝ} {xs : List ℝ}
    (hxs : IsChainOn (Icc a b) xs) :
    IsChainOn (Icc a b) ((xs.map (fun t => a + b - t)).reverse) := by
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_reverse, List.pairwise_map]
    exact hxs.1.imp (by intro x y hxy; linarith)
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ht)
    obtain ⟨hau, hub⟩ := hxs.2 u hu
    constructor <;> linarith

private theorem scoresOn_reflect_Icc_subset (ε : ℝ) (f : ℝ → X) (a b : ℝ) :
    scoresOn ε (fun t => f (a + b - t)) (Icc a b) ⊆
      scoresOn ε f (Icc a b) := by
  rintro r ⟨xs, hxs, rfl⟩
  refine ⟨(xs.map (fun t => a + b - t)).reverse, hxs.reflect_Icc, ?_⟩
  rw [chainScore_reverse, chainScore_map_for_reverse]

/-- Reflecting a real interval parameter preserves exactly the set of chain scores. -/
theorem scoresOn_reflect_Icc (ε : ℝ) (f : ℝ → X) (a b : ℝ) :
    scoresOn ε (fun t => f (a + b - t)) (Icc a b) =
      scoresOn ε f (Icc a b) := by
  apply Subset.antisymm (scoresOn_reflect_Icc_subset ε f a b)
  have h := scoresOn_reflect_Icc_subset ε (fun t => f (a + b - t)) a b
  have hinv : (fun t : ℝ => f (a + b - (a + b - t))) = f := by
    funext t
    congr 1
    ring
  simpa only [hinv] using h

/-- Interval-parameter reversal preserves truncated variation, without a finiteness premise. -/
theorem variationOn_reflect_Icc (ε : ℝ) (f : ℝ → X) (a b : ℝ) :
    variationOn ε (fun t => f (a + b - t)) (Icc a b) =
      variationOn ε f (Icc a b) := by
  unfold variationOn
  rw [scoresOn_reflect_Icc]

end

end Puzzling139335.ArcVariation
