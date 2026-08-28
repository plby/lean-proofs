import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Finite displacement sums for actual broken-path realization

A completed prefix, one active displacement, and a zero tail give an exact
partial sum. Differences telescope to the prescribed vertices. These additive
identities let sphere segments be glued in their common ambient vector space.
-/

namespace Wikipedia.HopfProblem.OrbitPair.OrderedSums

variable {A : Type*} [AddMonoid A] {N : ℕ}

theorem partialSum_congr (f g : Fin N → A) (k : Fin (N + 1))
    (h : ∀ j : Fin N, (j : ℕ) < (k : ℕ) → f j = g j) :
    Fin.partialSum f k = Fin.partialSum g k := by
  revert h
  induction k using Fin.inductionOn with
  | zero => intro _; simp
  | succ j ih =>
    intro h
    rw [Fin.partialSum_succ, Fin.partialSum_succ,
      ih (fun q hq => h q (by
        change (q : ℕ) < (j : ℕ) at hq
        change (q : ℕ) < (j : ℕ) + 1
        omega)), h j (by change (j : ℕ) < (j : ℕ) + 1; omega)]

theorem partialSum_of_tail_zero (f : Fin N → A) (i : Fin N)
    (h : ∀ j, i < j → f j = 0) (k : Fin (N + 1)) (hik : i.succ ≤ k) :
    Fin.partialSum f k = Fin.partialSum f i.succ := by
  revert hik
  induction k using Fin.inductionOn with
  | zero =>
    intro h
    change (i : ℕ) + 1 ≤ 0 at h
    omega
  | succ j ih =>
    intro hij
    by_cases he : j = i
    · subst j
      rfl
    · have hlt : i < j := by
        have hne : (i : ℕ) ≠ (j : ℕ) := fun hv => he (Fin.ext hv.symm)
        change (i : ℕ) + 1 ≤ (j : ℕ) + 1 at hij
        change (i : ℕ) < (j : ℕ)
        omega
      rw [Fin.partialSum_succ, h j hlt, add_zero]
      apply ih
      change (i : ℕ) + 1 ≤ (j : ℕ)
      exact hlt

theorem partialSum_last_eq (f g : Fin N → A) (i : Fin N)
    (hbefore : ∀ j, j < i → f j = g j) (hafter : ∀ j, i < j → f j = 0) :
    Fin.partialSum f (Fin.last N) = Fin.partialSum g i.castSucc + f i := by
  rw [partialSum_of_tail_zero f i hafter (Fin.last N) (Fin.le_last _), Fin.partialSum_succ]
  rw [partialSum_congr f g i.castSucc (fun j hj => hbefore j hj)]

theorem continuous_partialSum {X : Type*} [TopologicalSpace X]
    [TopologicalSpace A] [ContinuousAdd A] {f : X → Fin N → A}
    (hf : ∀ i, Continuous (fun x => f x i)) (k : Fin (N + 1)) :
    Continuous (fun x => Fin.partialSum (f x) k) := by
  induction k using Fin.inductionOn with
  | zero => simpa only [Fin.partialSum_zero] using
      (continuous_const : Continuous (fun _ : X => (0 : A)))
  | succ j ih => simpa only [Fin.partialSum_succ] using! ih.add (hf j)

theorem partialSum_differences {V : Type*} [AddCommGroup V]
    (v : Fin (N + 1) → V) (k : Fin (N + 1)) :
    v 0 + Fin.partialSum (fun j : Fin N => v j.succ - v j.castSucc) k = v k := by
  induction k using Fin.inductionOn with
  | zero => simp
  | succ j ih =>
    rw [Fin.partialSum_succ, ← add_assoc, ih]
    abel

end Wikipedia.HopfProblem.OrbitPair.OrderedSums
