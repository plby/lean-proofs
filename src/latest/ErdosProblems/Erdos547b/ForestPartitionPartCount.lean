/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.ForestPartitionConstructor

/-!
# Number of parts in the Zhao forest partition

The constructor stores Zhao's bound separately on the two root-parity
classes.  Since those classes partition the root indices, their sum gives the
coarse total-part bound used throughout Section 6.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.TreePartition

open Finset Fintype SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- The two root-parity filters cover every component index. -/
theorem rootParity_zero_union_one
    (P : ZhaoForestPartition T globalRoot small) :
    (Finset.univ.filter fun i : Fin P.numParts ↦
        T.dist globalRoot (P.roots i) % 2 = 0) ∪
      (Finset.univ.filter fun i : Fin P.numParts ↦
        T.dist globalRoot (P.roots i) % 2 = 1) = Finset.univ := by
  ext i
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]
  have hmod : T.dist globalRoot (P.roots i) % 2 < 2 :=
    Nat.mod_lt _ (by omega)
  omega

/-- Total number of components obtained by adding the two stored parity
bounds. -/
theorem numParts_le_two_mul_rootBound
    (P : ZhaoForestPartition T globalRoot small) :
    P.numParts ≤ 2 * ((Fintype.card V + small) / (small + 1)) := by
  let A := Finset.univ.filter fun i : Fin P.numParts ↦
    T.dist globalRoot (P.roots i) % 2 = 0
  let B := Finset.univ.filter fun i : Fin P.numParts ↦
    T.dist globalRoot (P.roots i) % 2 = 1
  have hcover : A ∪ B = Finset.univ := by
    simpa only [A, B] using rootParity_zero_union_one P
  have hcard : P.numParts ≤ A.card + B.card := by
    calc
      P.numParts = #(Finset.univ : Finset (Fin P.numParts)) := by simp
      _ = #(A ∪ B) := by rw [hcover]
      _ ≤ A.card + B.card := Finset.card_union_le A B
  have hA : A.card ≤ (Fintype.card V + small) / (small + 1) := by
    simpa [A] using P.parity_root_bound (0 : Fin 2)
  have hB : B.card ≤ (Fintype.card V + small) / (small + 1) := by
    simpa [B] using P.parity_root_bound (1 : Fin 2)
  omega

end Erdos547b.TreePartition

#print axioms Erdos547b.TreePartition.numParts_le_two_mul_rootBound
