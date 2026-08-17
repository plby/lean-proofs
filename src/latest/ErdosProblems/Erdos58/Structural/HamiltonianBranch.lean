/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos58.Independent
import ErdosProblems.Erdos58.StructuralAlt
import Mathlib.Tactic

/-!
# The Hamiltonian branch of the longest-odd-cycle argument

The fan count in `StructuralAlt` rules out an odd Hamiltonian cycle at the
structural minimum-degree threshold.  Consequently, a designated longest odd
cycle always has a vertex outside it.  This is the first conclusion required
by the independent-exterior rigidity argument.
-/

namespace Erdos58.Structural

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At the Gyárfás threshold a longest odd cycle cannot contain every vertex.
The proof uses only the checked odd-Hamiltonian fan count. -/
theorem longestOddCycle_exterior_nonempty {j : ℕ} (hj : 0 < j)
    (C : LongestOddCycle G)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hodd : (oddCycleLengths G).ncard ≤ j) :
    C.carrierᶜ.Nonempty := by
  by_contra houtside
  have hempty : C.carrierᶜ = ∅ := Set.not_nonempty_iff_eq_empty.mp houtside
  have hcarrier : C.carrier = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx
    have hxc : x ∈ C.carrierᶜ := hx
    rw [hempty] at hxc
    exact hxc
  have hcard : Fintype.card V = C.length := by
    calc
      Fintype.card V = Nat.card V := Nat.card_eq_fintype_card.symm
      _ = Set.univ.ncard := (Set.ncard_univ V).symm
      _ = C.carrier.ncard := by rw [hcarrier]
      _ = C.length := C.ncard_carrier
  obtain ⟨hoddLength, v, p, hpCycle, hpLength⟩ :=
    C.length_mem_oddCycleLengths
  have hpHamiltonian : p.IsHamiltonianCycle :=
    SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
      ⟨hpCycle, by omega⟩
  exact StructuralAlt.no_odd_hamiltonian_cycle_of_degree_and_length_bound
    hj hdegree hodd ⟨v, p, hpHamiltonian, hpLength ▸ hoddLength⟩

end Erdos58.Structural
