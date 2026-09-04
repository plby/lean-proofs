import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Erdos547b

open Finset
open SimpleGraph

/-- A vertex is a leaf when it has degree exactly one. -/
def IsLeaf {V : Type*} (T : SimpleGraph V) [T.LocallyFinite] (v : V) : Prop :=
  T.degree v = 1

/-- The leaves of `T` that lie in the finite vertex set `B`. -/
noncomputable def leavesIn {V : Type*} (T : SimpleGraph V) [T.LocallyFinite]
    (B : Finset V) : Finset V := by
  classical
  exact B.filter (IsLeaf T)

/-- `A,B` are a proper bipartition of `T`: every vertex lies in one of the two
nonempty parts, and every edge goes between the parts. -/
structure IsProperBipartition {V : Type*} [Fintype V]
    (T : SimpleGraph V) (A B : Finset V) : Prop where
  bipartite : T.IsBipartiteWith (A : Set V) (B : Set V)
  cover : (A : Set V) ∪ (B : Set V) = Set.univ
  left_nonempty : A.Nonempty
  right_nonempty : B.Nonempty

/-- **Zhao, Fact 6.9 (cardinality form).** In a finite tree with a proper
bipartition `A,B`, if `A` is no larger than `B`, then the larger part contains
at least `|B| - |A| + 1` leaves. -/
theorem card_leavesIn_larger_part {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (A B : Finset V)
    (hT : T.IsTree) (hpart : IsProperBipartition T A B)
    (hAB : A.card ≤ B.card) :
    B.card - A.card + 1 ≤ (leavesIn T B).card := by
  classical
  have hdisj : Disjoint A B := Finset.disjoint_coe.mp hpart.bipartite.disjoint
  have hcover : A ∪ B = Finset.univ := by
    ext v
    have hv := Set.ext_iff.mp hpart.cover v
    simpa using hv
  have hcardV : Fintype.card V = A.card + B.card := by
    rw [← Finset.card_univ, ← hcover,
      Finset.card_union_of_disjoint hdisj]
  have hcardApos : 0 < A.card := Finset.card_pos.mpr hpart.left_nonempty
  have hcardBpos : 0 < B.card := Finset.card_pos.mpr hpart.right_nonempty
  have hcardVtwo : 1 < Fintype.card V := by omega
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcardVtwo
  have hedge : T.edgeFinset.card = A.card + B.card - 1 := by
    have h := hT.card_edgeFinset
    rw [hcardV] at h
    omega
  have hsumB : (∑ v ∈ B, T.degree v) = T.edgeFinset.card :=
    SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hpart.bipartite
  have hpoint (v : V) (hv : v ∈ B) :
      2 ≤ T.degree v + if IsLeaf T v then 1 else 0 := by
    have hpos : 0 < T.degree v := hT.preconnected.degree_pos_of_nontrivial v
    by_cases hleaf : IsLeaf T v
    · rw [if_pos hleaf]
      have hdeg : T.degree v = 1 := by
        simpa only [IsLeaf] using hleaf
      omega
    · have htwo : 2 ≤ T.degree v := by
        have hne : T.degree v ≠ 1 := by
          intro heq
          apply hleaf
          simpa only [IsLeaf] using heq
        omega
      rw [if_neg hleaf]
      omega
  have hdegreeLeaf :
      2 * B.card ≤ (∑ v ∈ B, T.degree v) + (leavesIn T B).card := by
    calc
      2 * B.card = ∑ v ∈ B, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ B, (T.degree v + if IsLeaf T v then 1 else 0) := by
        exact Finset.sum_le_sum fun v hv => hpoint v hv
      _ = (∑ v ∈ B, T.degree v) + (leavesIn T B).card := by
        rw [Finset.sum_add_distrib]
        simp [leavesIn]
  rw [hsumB, hedge] at hdegreeLeaf
  omega

/-- Zhao's Fact 6.9 with named bipartition sizes. -/
theorem card_leavesIn_larger_part_of_sizes {V : Type*} [Fintype V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (A B : Finset V) (a b : ℕ)
    (hT : T.IsTree) (hpart : IsProperBipartition T A B)
    (hA : A.card = a) (hB : B.card = b) (hab : a ≤ b) :
    b - a + 1 ≤ (leavesIn T B).card := by
  subst a
  subst b
  exact card_leavesIn_larger_part T A B hT hpart hab

end Erdos547b

#print axioms Erdos547b.card_leavesIn_larger_part
#print axioms Erdos547b.card_leavesIn_larger_part_of_sizes
