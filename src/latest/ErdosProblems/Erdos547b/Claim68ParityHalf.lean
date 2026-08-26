/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma614

/-!
# The branch-closed parity half in Zhao Claim 6.8

The two source forests `F_a` and `F_b` are unions of whole cut-forest
components, selected by the parity of their component roots.  This module
constructs those literal vertex sets and then chooses the larger one.  In
particular it replaces the unconstrained `partA partB : Finset V` parameters
of the purely numerical Claim-6.8 lemma by the branch-closed sets actually
used by Claims 6.16 and 6.17.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoClaim68ParityHalf

open Finset SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {T : SimpleGraph V} [DecidableRel T.Adj]
variable {globalRoot : V} {small : ℕ}

/-- Non-root vertices in components whose root has parity `q`. -/
def parityPart (P : ZhaoForestPartition T globalRoot small) (q : Fin 2) :
    Finset V :=
  (partitionNonroots P).filter fun v ↦
    T.dist globalRoot (P.roots (P.componentIndex v)) % 2 = q.val

theorem parityPart_subset_nonroots
    (P : ZhaoForestPartition T globalRoot small) (q : Fin 2) :
    parityPart P q ⊆ partitionNonroots P :=
  Finset.filter_subset _ _

/-- The two component-parity classes cover every non-root vertex. -/
theorem parityPart_zero_union_one
    (P : ZhaoForestPartition T globalRoot small) :
    parityPart P 0 ∪ parityPart P 1 = partitionNonroots P := by
  ext v
  simp only [parityPart, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hv, -⟩ | ⟨hv, -⟩)
    · exact hv
    · exact hv
  · intro hv
    refine Or.imp (⟨hv, ·⟩) (⟨hv, ·⟩) ?_
    have hlt : T.dist globalRoot (P.roots (P.componentIndex v)) % 2 < 2 :=
      Nat.mod_lt _ (by omega)
    omega

/-- The two component-parity classes are disjoint. -/
theorem parityPart_zero_disjoint_one
    (P : ZhaoForestPartition T globalRoot small) :
    Disjoint (parityPart P 0) (parityPart P 1) := by
  rw [Finset.disjoint_left]
  intro v hv0 hv1
  have h0 := (Finset.mem_filter.mp hv0).2
  have h1 := (Finset.mem_filter.mp hv1).2
  omega

/-- The source's `F_a - Rt(F_a)`: the larger component-parity class. -/
def majorPart (P : ZhaoForestPartition T globalRoot small) : Finset V :=
  if (parityPart P 1).card ≤ (parityPart P 0).card then
    parityPart P 0
  else parityPart P 1

/-- The source's `F_b - Rt(F_b)`: the other component-parity class. -/
def minorPart (P : ZhaoForestPartition T globalRoot small) : Finset V :=
  if (parityPart P 1).card ≤ (parityPart P 0).card then
    parityPart P 1
  else parityPart P 0

def majorParity (P : ZhaoForestPartition T globalRoot small) : Fin 2 :=
  if (parityPart P 1).card ≤ (parityPart P 0).card then 0 else 1

def minorParity (P : ZhaoForestPartition T globalRoot small) : Fin 2 :=
  if (parityPart P 1).card ≤ (parityPart P 0).card then 1 else 0

@[simp] theorem parityPart_majorParity
    (P : ZhaoForestPartition T globalRoot small) :
    parityPart P (majorParity P) = majorPart P := by
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card <;>
    simp [majorParity, majorPart, h]

@[simp] theorem parityPart_minorParity
    (P : ZhaoForestPartition T globalRoot small) :
    parityPart P (minorParity P) = minorPart P := by
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card <;>
    simp [minorParity, minorPart, h]

theorem major_minor_disjoint
    (P : ZhaoForestPartition T globalRoot small) :
    Disjoint (majorPart P) (minorPart P) := by
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card
  · simpa [majorPart, minorPart, h] using parityPart_zero_disjoint_one P
  · simpa [majorPart, minorPart, h] using
      (parityPart_zero_disjoint_one P).symm

theorem major_union_minor
    (P : ZhaoForestPartition T globalRoot small) :
    majorPart P ∪ minorPart P = partitionNonroots P := by
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card
  · simpa [majorPart, minorPart, h] using parityPart_zero_union_one P
  · simpa [majorPart, minorPart, h, Finset.union_comm] using
      parityPart_zero_union_one P

theorem minor_card_le_major_card
    (P : ZhaoForestPartition T globalRoot small) :
    (minorPart P).card ≤ (majorPart P).card := by
  by_cases h : (parityPart P 1).card ≤ (parityPart P 0).card
  · simpa [majorPart, minorPart, h] using h
  · simp only [majorPart, minorPart, h, if_false]
    omega

/-- The canonical parity half supplies all structural parameters of the
numerical Claim 6.8 theorem. -/
theorem claim6_8_canonicalParityHalf
    (P : ZhaoForestPartition T globalRoot small)
    (d : ℝ) (hd : 0 ≤ d) (n : ℕ)
    (hcardT : Fintype.card V = n + 1)
    (horiginalLeaves :
      (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
        11 * Real.sqrt d * n)
    (hhierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * n)
    (hhierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * n) :
    (1 - 12 * Real.sqrt d) * n ≤
        ((partitionNonroots P \ partitionLevelOneLeaves P).card : ℝ) ∧
      (n : ℝ) / 2 - 12 * Real.sqrt d * n <
        ((majorPart P \ partitionLevelOneLeaves P).card : ℝ) := by
  exact Erdos547b.ZhaoClaim68.claim6_8 P d hd hcardT
    (majorPart P) (minorPart P) (major_minor_disjoint P)
      (major_union_minor P) (minor_card_le_major_card P)
      horiginalLeaves hhierarchyF hhierarchyA

end Erdos547b.ZhaoClaim68ParityHalf

#print axioms Erdos547b.ZhaoClaim68ParityHalf.parityPart_zero_union_one
#print axioms Erdos547b.ZhaoClaim68ParityHalf.major_union_minor
#print axioms Erdos547b.ZhaoClaim68ParityHalf.claim6_8_canonicalParityHalf

