import Wikipedia.NoExoticSixSphere.RelativeSimplexHomotopyFamily
import Mathlib.Data.Nat.Init

/-!
# Extending a stationary-bottom stage to a full coherent family

Below the supplied stage the family is literally stationary. Above it,
the actual simplex-extension construction is iterated. The common degree
agrees exactly, so the full family has the original initial maps, face
identities, and subspace preservation in every dimension.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeSimplexHomotopyFamily.Stage

variable {X : Type} [TopologicalSpace X] {U : Set X} {n : ℕ} (D : Stage U n)

def extendTo (k : ℕ) (hk : n ≤ k) : Stage U k :=
  Nat.leRecOn hk (fun S ↦ S.next) D

theorem extendTo_self : D.extendTo n (Nat.le_refl n) = D := Nat.leRecOn_self D

theorem extendTo_succ (k : ℕ) (hk : n ≤ k) (hk' : n ≤ k + 1) :
    D.extendTo (k + 1) hk' = (D.extendTo k hk).next := Nat.leRecOn_succ hk D

def totalFamily (k : ℕ) : C(Simplex k, X) → C(I × Simplex k, X) :=
  if hk : n ≤ k then (D.extendTo k hk).lower else stationarySimplexHomotopy k

theorem totalFamily_of_le (k : ℕ) (hk : n ≤ k) :
    D.totalFamily k = (D.extendTo k hk).lower := dif_pos hk

theorem totalFamily_of_lt (k : ℕ) (hk : k < n) :
    D.totalFamily k = stationarySimplexHomotopy k := dif_neg (by omega)

theorem totalFamily_self : D.totalFamily n = D.lower := by
  rw [D.totalFamily_of_le n (Nat.le_refl n), D.extendTo_self]

theorem totalFamily_succ : D.totalFamily (n + 1) = D.upper := by
  rw [D.totalFamily_of_le (n + 1) (by omega),
    D.extendTo_succ n (Nat.le_refl n) (by omega), D.extendTo_self]
  rfl

theorem totalFamily_initial (k : ℕ) (smp : C(Simplex k, X)) (s : Simplex k) :
    D.totalFamily k smp (0, s) = smp s := by
  by_cases hk : n ≤ k
  · rw [D.totalFamily_of_le k hk]
    exact (D.extendTo k hk).lower_zero smp s
  · rw [D.totalFamily_of_lt k (by omega)]
    rfl

theorem totalFamily_face (hD : D.lower = stationarySimplexHomotopy n) (k : ℕ) :
    FaceCompatibleHomotopies k (D.totalFamily k) (D.totalFamily (k + 1)) := by
  by_cases hk : n ≤ k
  · rw [D.totalFamily_of_le k hk, D.totalFamily_of_le (k + 1) (by omega),
      D.extendTo_succ k hk (by omega)]
    exact (D.extendTo k hk).face
  · by_cases he : n = k + 1
    · subst n
      rw [D.totalFamily_self, hD, D.totalFamily_of_lt k (by omega)]
      intro smp i
      ext p
      rfl
    · rw [D.totalFamily_of_lt k (by omega), D.totalFamily_of_lt (k + 1) (by omega)]
      intro smp i
      ext p
      rfl

theorem totalFamily_mem (k : ℕ) (smp : C(Simplex k, X)) (hs : ∀ s, smp s ∈ U)
    (p : I × Simplex k) : D.totalFamily k smp p ∈ U := by
  by_cases hk : n ≤ k
  · rw [D.totalFamily_of_le k hk]
    exact (D.extendTo k hk).lower_mem smp hs p
  · rw [D.totalFamily_of_lt k (by omega)]
    exact hs p.2

end NoExoticSixSphere.RelativeSimplexHomotopyFamily.Stage
