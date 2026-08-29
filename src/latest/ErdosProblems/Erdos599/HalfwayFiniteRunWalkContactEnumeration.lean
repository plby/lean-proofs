/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteRunWalkContactCoordinates

/-!
# Ordered finite contact coordinates

For an actual finite run walk, enumerate the initial coordinate, every
vertex in `X`, and the terminal coordinate in their literal traversal order.
The resulting points are injective and consecutive entries have no omitted
`X`-contact between them.
-/

noncomputable section

open Set

namespace Erdos599.Alternating

universe u

variable {V : Type u} {D : Digraph V}

namespace FiniteRunWalk

def breakPositions (W : FiniteRunWalk D) (X : Set V) :
    Finset (Fin (W.finalPosition + 1)) := by
  classical
  exact Finset.univ.filter fun n =>
    n.1 = 0 ∨ n.1 = W.finalPosition ∨ W.vertex n.1 ∈ X

theorem zero_mem_breakPositions (W : FiniteRunWalk D) (X : Set V) :
    (⟨0, Nat.zero_lt_succ _⟩ : Fin (W.finalPosition + 1)) ∈
      W.breakPositions X := by
  classical
  simp [breakPositions]

theorem final_mem_breakPositions (W : FiniteRunWalk D) (X : Set V) :
    (⟨W.finalPosition, Nat.lt_succ_self _⟩ :
      Fin (W.finalPosition + 1)) ∈ W.breakPositions X := by
  classical
  simp [breakPositions]

theorem breakPositions_nonempty (W : FiniteRunWalk D) (X : Set V) :
    (W.breakPositions X).Nonempty :=
  ⟨_, W.zero_mem_breakPositions X⟩

def breakCount (W : FiniteRunWalk D) (X : Set V) : Nat :=
  (W.breakPositions X).card - 1

theorem breakPositions_card (W : FiniteRunWalk D) (X : Set V) :
    (W.breakPositions X).card = W.breakCount X + 1 := by
  have hpos := (W.breakPositions_nonempty X).card_pos
  rw [breakCount]
  omega

noncomputable def breakOrderIso (W : FiniteRunWalk D) (X : Set V) :
    Fin (W.breakCount X + 1) ≃o ↥(W.breakPositions X) :=
  Finset.orderIsoOfFin (W.breakPositions X) (W.breakPositions_card X)

noncomputable def breakPosition (W : FiniteRunWalk D) (X : Set V)
    (i : Fin (W.breakCount X + 1)) : Nat :=
  (W.breakOrderIso X i).1.1

theorem breakPosition_mem (W : FiniteRunWalk D) (X : Set V)
    (i : Fin (W.breakCount X + 1)) :
    (⟨W.breakPosition X i, (W.breakOrderIso X i).1.2⟩ :
      Fin (W.finalPosition + 1)) ∈ W.breakPositions X :=
  (W.breakOrderIso X i).2

theorem breakPosition_le_final (W : FiniteRunWalk D) (X : Set V)
    (i : Fin (W.breakCount X + 1)) :
    W.breakPosition X i ≤ W.finalPosition := by
  exact Nat.le_of_lt_succ (W.breakOrderIso X i).1.2

theorem breakPosition_strictMono (W : FiniteRunWalk D) (X : Set V) :
    StrictMono (W.breakPosition X) := by
  intro i j hij
  exact (W.breakOrderIso X).strictMono hij

theorem breakPosition_injective (W : FiniteRunWalk D) (X : Set V) :
    Function.Injective (W.breakPosition X) :=
  (W.breakPosition_strictMono X).injective

@[simp] theorem breakPosition_zero (W : FiniteRunWalk D) (X : Set V) :
    W.breakPosition X ⟨0, Nat.zero_lt_succ _⟩ = 0 := by
  let z : ↥(W.breakPositions X) :=
    ⟨⟨0, Nat.zero_lt_succ _⟩, W.zero_mem_breakPositions X⟩
  let j := (W.breakOrderIso X).symm z
  have hle : (W.breakOrderIso X ⟨0, Nat.zero_lt_succ _⟩) ≤ z := by
    simpa [j] using (W.breakOrderIso X).monotone (Fin.zero_le j)
  exact Nat.eq_zero_of_le_zero hle

@[simp] theorem breakPosition_last (W : FiniteRunWalk D) (X : Set V) :
    W.breakPosition X ⟨W.breakCount X, Nat.lt_succ_self _⟩ =
      W.finalPosition := by
  let z : ↥(W.breakPositions X) :=
    ⟨⟨W.finalPosition, Nat.lt_succ_self _⟩, W.final_mem_breakPositions X⟩
  let j := (W.breakOrderIso X).symm z
  have hle : W.finalPosition ≤
      W.breakPosition X ⟨W.breakCount X, Nat.lt_succ_self _⟩ := by
    calc
      W.finalPosition = W.breakPosition X j := by
        change z.1.1 = (W.breakOrderIso X j).1.1
        simp [j]
      _ ≤ W.breakPosition X ⟨W.breakCount X, Nat.lt_succ_self _⟩ :=
        (W.breakPosition_strictMono X).monotone (Fin.le_last j)
  apply Nat.le_antisymm (W.breakPosition_le_final X _)
  exact hle

theorem breakPosition_endpoint_or_mem (W : FiniteRunWalk D) (X : Set V)
    (i : Fin (W.breakCount X + 1)) :
    W.breakPosition X i = 0 ∨
      W.breakPosition X i = W.finalPosition ∨
        W.vertex (W.breakPosition X i) ∈ X := by
  have hmem := W.breakPosition_mem X i
  classical
  simpa only [breakPositions, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.ext_iff] using hmem

theorem mem_range_breakPosition_of_mem
    (W : FiniteRunWalk D) (X : Set V)
    (n : Nat) (hn : n ≤ W.finalPosition)
    (hnX : W.vertex n ∈ X) :
    n ∈ Set.range (W.breakPosition X) := by
  let a : Fin (W.finalPosition + 1) := ⟨n, Nat.lt_succ_iff.2 hn⟩
  have ha : a ∈ W.breakPositions X := by
    classical
    simp [breakPositions, a, hnX]
  let b : ↥(W.breakPositions X) := ⟨a, ha⟩
  exact ⟨(W.breakOrderIso X).symm b, by
    change ((W.breakOrderIso X) ((W.breakOrderIso X).symm b)).1.1 = n
    rw [(W.breakOrderIso X).apply_symm_apply]
    ⟩

/-- There is no omitted cut contact strictly between two consecutive break
coordinates. -/
theorem no_mem_between_consecutive
    (W : FiniteRunWalk D) (X : Set V)
    (i : Fin (W.breakCount X))
    {n : Nat}
    (hleft : W.breakPosition X i.castSucc < n)
    (hright : n < W.breakPosition X i.succ) :
    W.vertex n ∉ X := by
  intro hnX
  have hnfinal : n ≤ W.finalPosition :=
    (Nat.le_of_lt hright).trans (W.breakPosition_le_final X i.succ)
  obtain ⟨j, hj⟩ := W.mem_range_breakPosition_of_mem X n hnfinal hnX
  have hij : i.castSucc < j := by
    apply (W.breakPosition_strictMono X).lt_iff_lt.mp
    simpa [hj] using hleft
  have hji : j < i.succ := by
    apply (W.breakPosition_strictMono X).lt_iff_lt.mp
    simpa [hj] using hright
  change i.1 < j.1 at hij
  change j.1 < i.1 + 1 at hji
  omega

noncomputable def breakPoint (W : FiniteRunWalk D) (X : Set V)
    (i : Fin (W.breakCount X + 1)) : V :=
  W.vertex (W.breakPosition X i)

theorem breakPoint_injective (W : FiniteRunWalk D) (X : Set V) :
    Function.Injective (W.breakPoint X) := by
  intro i j hij
  apply (W.breakPosition_injective X)
  apply W.vertex_injective_on
    (W.breakPosition_le_final X i) (W.breakPosition_le_final X j)
  exact hij

end FiniteRunWalk
end Erdos599.Alternating

#print axioms Erdos599.Alternating.FiniteRunWalk.breakPosition_strictMono
#print axioms Erdos599.Alternating.FiniteRunWalk.mem_range_breakPosition_of_mem
#print axioms Erdos599.Alternating.FiniteRunWalk.no_mem_between_consecutive
#print axioms Erdos599.Alternating.FiniteRunWalk.breakPoint_injective
