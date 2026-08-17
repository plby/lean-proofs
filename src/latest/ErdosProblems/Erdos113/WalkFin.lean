import Mathlib

open scoped SimpleGraph

namespace WF


def walkOfFin {W : Type*} {A : SimpleGraph W} :
    ∀ (n : ℕ) (f : Fin (n + 1) → W),
      (∀ i : Fin n, A.Adj (f i.castSucc) (f i.succ)) →
        A.Walk (f ⟨0, Nat.zero_lt_succ n⟩) (f ⟨n, Nat.lt_succ_self n⟩)
  | 0, f, _ => .nil
  | n + 1, f, h => by
      let g : Fin (n + 1) → W := fun i ↦ f i.succ
      have hg : ∀ i : Fin n, A.Adj (g i.castSucc) (g i.succ) := by
        intro i
        exact h i.succ
      exact (walkOfFin n g hg).cons (h ⟨0, Nat.zero_lt_succ n⟩)

@[simp] lemma walkOfFin_length {W : Type*} {A : SimpleGraph W}
    (n : ℕ) (f : Fin (n + 1) → W)
    (h : ∀ i : Fin n, A.Adj (f i.castSucc) (f i.succ)) :
    (walkOfFin n f h).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [walkOfFin, SimpleGraph.Walk.length_cons]
      rw [ih]

lemma walkOfFin_getVert {W : Type*} {A : SimpleGraph W}
    (n : ℕ) (f : Fin (n + 1) → W)
    (h : ∀ i : Fin n, A.Adj (f i.castSucc) (f i.succ))
    (i : ℕ) (hi : i ≤ n) :
    (walkOfFin n f h).getVert i = f ⟨i, Nat.lt_succ_iff.mpr hi⟩ := by
  induction n generalizing i with
  | zero =>
      have : i = 0 := by omega
      subst i
      simp [walkOfFin]
  | succ n ih =>
      by_cases hi0 : i = 0
      · subst i
        simp [walkOfFin]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        simp only [walkOfFin, SimpleGraph.Walk.getVert_cons_succ]
        exact ih (fun k : Fin (n + 1) ↦ f k.succ)
          (fun k : Fin n ↦ h k.succ) j (by omega)

end WF

