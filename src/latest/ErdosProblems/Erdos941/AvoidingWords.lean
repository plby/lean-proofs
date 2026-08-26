import ErdosProblems.Erdos941.EdgeAvoidance

/-! # Finite sets of words counted by the avoidance recurrence -/

namespace Erdos941

section

variable {α : Type*} (step : α → Fin 3 → α) (target : α → Prop) [DecidablePred target]

def AvoidsWord : List (Fin 3) → α → Prop
  | [], s => ¬ target s
  | i :: w, s => ¬ target s ∧ AvoidsWord w (step s i)

noncomputable def avoidingWords : ℕ → α → Finset (List (Fin 3))
  | 0, s => if target s then ∅ else {[]}
  | n + 1, s => if target s then ∅ else
      Finset.univ.biUnion fun i : Fin 3 => (avoidingWords n (step s i)).image (List.cons i)

theorem mem_avoidingWords {k : ℕ} {s : α} {w : List (Fin 3)} :
    w ∈ avoidingWords step target k s ↔ w.length = k ∧ AvoidsWord step target w s := by
  classical
  induction k generalizing s w with
  | zero =>
    cases w <;> by_cases hs : target s <;> simp [avoidingWords, hs, AvoidsWord]
  | succ k ih =>
    cases w with
    | nil => by_cases hs : target s <;> simp [avoidingWords, AvoidsWord, hs]
    | cons i w =>
      by_cases hs : target s
      · simp [avoidingWords, hs, AvoidsWord]
      · simp [avoidingWords, hs, AvoidsWord, ih]

theorem card_avoidingWords_le (k : ℕ) (s : α) :
    (avoidingWords step target k s).card ≤ avoidanceCount step target k s := by
  classical
  induction k generalizing s with
  | zero => by_cases hs : target s <;> simp [avoidingWords, avoidanceCount, hs]
  | succ k ih =>
    by_cases hs : target s
    · simp [avoidingWords, avoidanceCount, hs]
    · simp only [avoidingWords, avoidanceCount, hs, ↓reduceIte]
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro i _
      exact Finset.card_image_le.trans (ih (step s i))

end

end Erdos941
