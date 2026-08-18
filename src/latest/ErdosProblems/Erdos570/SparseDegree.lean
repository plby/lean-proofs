/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.DegreeTwoPath
import ErdosProblems.Erdos570.Components

/-!
# Degree bookkeeping for sparse connected targets

This is the numerical half of the Burr--Erdős--Faudree--Rousseau--Schelp
suspended-path lemma.  We keep deliberately relaxed integer constants, which
are more convenient for the later formal decomposition.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

def leafVertices (H : GraphCode) [DecidableRel H.graph.Adj] :
    Finset (Fin H.vertexCount) :=
  Finset.univ.filter fun v ↦ H.graph.degree v = 1

def degreeTwoVertices (H : GraphCode) [DecidableRel H.graph.Adj] :
    Finset (Fin H.vertexCount) :=
  Finset.univ.filter fun v ↦ H.graph.degree v = 2

def branchVertices (H : GraphCode) [DecidableRel H.graph.Adj] :
    Finset (Fin H.vertexCount) :=
  Finset.univ.filter fun v ↦ 3 ≤ H.graph.degree v

def sparseCoreVertices (H : GraphCode) [DecidableRel H.graph.Adj] :
    Finset (Fin H.vertexCount) :=
  Finset.univ \ degreeTwoVertices H

/-- Cyclomatic excess in a form that is zero on trees. -/
def sparseExcess (H : GraphCode) : ℕ :=
  H.edgeCount + 1 - H.vertexCount

theorem connected_edge_add_one_eq_vertex_add_excess
    (H : GraphCode) (hconn : H.graph.Connected) :
    H.edgeCount + 1 = H.vertexCount + sparseExcess H := by
  unfold sparseExcess
  have hle : H.vertexCount ≤ H.edgeCount + 1 := by
    simpa [GraphCode.edgeCount] using
      hconn.card_vert_le_card_edgeSet_add_one
  omega

@[simp] theorem mem_leafVertices (H : GraphCode) [DecidableRel H.graph.Adj]
    (v : Fin H.vertexCount) :
    v ∈ leafVertices H ↔ H.graph.degree v = 1 := by
  simp [leafVertices]

@[simp] theorem mem_degreeTwoVertices (H : GraphCode) [DecidableRel H.graph.Adj]
    (v : Fin H.vertexCount) :
    v ∈ degreeTwoVertices H ↔ H.graph.degree v = 2 := by
  simp [degreeTwoVertices]

@[simp] theorem mem_branchVertices (H : GraphCode) [DecidableRel H.graph.Adj]
    (v : Fin H.vertexCount) :
    v ∈ branchVertices H ↔ 3 ≤ H.graph.degree v := by
  simp [branchVertices]

@[simp] theorem mem_sparseCoreVertices (H : GraphCode) [DecidableRel H.graph.Adj]
    (v : Fin H.vertexCount) :
    v ∈ sparseCoreVertices H ↔ H.graph.degree v ≠ 2 := by
  simp [sparseCoreVertices]

theorem degree_pos_of_noIsolated (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H)
    (v : Fin H.vertexCount) : 0 < H.graph.degree v := by
  exact (H.graph.degree_pos v).mpr (hH v)

theorem sparseCore_eq_leaf_union_branch (H : GraphCode)
    [DecidableRel H.graph.Adj] (hH : NoIsolated H) :
    sparseCoreVertices H = leafVertices H ∪ branchVertices H := by
  ext v
  simp only [mem_sparseCoreVertices, Finset.mem_union, mem_leafVertices,
    mem_branchVertices]
  have hv := degree_pos_of_noIsolated H hH v
  omega

theorem leaf_disjoint_branch (H : GraphCode) [DecidableRel H.graph.Adj] :
    Disjoint (leafVertices H) (branchVertices H) := by
  rw [Finset.disjoint_left]
  intro v hvleaf hvbranch
  rw [mem_leafVertices] at hvleaf
  rw [mem_branchVertices] at hvbranch
  omega

theorem sparseCore_card_eq (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) :
    (sparseCoreVertices H).card =
      (leafVertices H).card + (branchVertices H).card := by
  rw [sparseCore_eq_leaf_union_branch H hH,
    Finset.card_union_of_disjoint (leaf_disjoint_branch H)]

theorem degreeTwo_card_add_core_card (H : GraphCode)
    [DecidableRel H.graph.Adj] :
    (degreeTwoVertices H).card + (sparseCoreVertices H).card =
      H.vertexCount := by
  have h := Finset.card_sdiff_add_card_eq_card
    (show degreeTwoVertices H ⊆
      (Finset.univ : Finset (Fin H.vertexCount)) from Finset.subset_univ _)
  simpa [sparseCoreVertices, add_comm] using h

theorem branch_card_le_leaf_add_twice_excess
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected) :
    (branchVertices H).card ≤
      (leafVertices H).card + 2 * sparseExcess H := by
  classical
  have hpoint : ∀ v : Fin H.vertexCount,
      2 + (if 3 ≤ H.graph.degree v then 1 else 0) ≤
        H.graph.degree v + (if H.graph.degree v = 1 then 1 else 0) := by
    intro v
    have hv := degree_pos_of_noIsolated H hH v
    split <;> split <;> omega
  have hsum := Finset.sum_le_sum fun v (_ : v ∈
      (Finset.univ : Finset (Fin H.vertexCount))) ↦ hpoint v
  have hdegree : ∑ v : Fin H.vertexCount, H.graph.degree v =
      2 * H.edgeCount := by
    simpa [GraphCode.edgeCount_eq_card_edgeFinset] using
      H.graph.sum_degrees_eq_twice_card_edges
  have hbranchfilter :
      ((Finset.univ : Finset (Fin H.vertexCount)).filter
        fun v ↦ 3 ≤ H.graph.degree v).card = (branchVertices H).card := by
    apply congrArg Finset.card
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_branchVertices]
  have hleaffilter :
      ((Finset.univ : Finset (Fin H.vertexCount)).filter
        fun v ↦ H.graph.degree v = 1).card = (leafVertices H).card := by
    apply congrArg Finset.card
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_leafVertices]
  have hleft : ∑ v : Fin H.vertexCount,
      (2 + (if 3 ≤ H.graph.degree v then 1 else 0)) =
      2 * H.vertexCount + (branchVertices H).card := by
    have hconst : ∑ _v : Fin H.vertexCount, 2 = 2 * H.vertexCount := by
      simp [mul_comm]
    have hbool : ∑ v : Fin H.vertexCount,
        (if 3 ≤ H.graph.degree v then 1 else 0) =
          (branchVertices H).card := by
      simpa [branchVertices] using
        (Finset.sum_boole (s := (Finset.univ : Finset (Fin H.vertexCount)))
          (p := fun v ↦ 3 ≤ H.graph.degree v))
    rw [Finset.sum_add_distrib, hconst, hbool]
  have hright : ∑ v : Fin H.vertexCount,
      (H.graph.degree v + (if H.graph.degree v = 1 then 1 else 0)) =
      2 * H.edgeCount + (leafVertices H).card := by
    have hbool : ∑ v : Fin H.vertexCount,
        (if H.graph.degree v = 1 then 1 else 0) =
          (leafVertices H).card := by
      simpa [leafVertices] using
        (Finset.sum_boole (s := (Finset.univ : Finset (Fin H.vertexCount)))
          (p := fun v ↦ H.graph.degree v = 1))
    rw [Finset.sum_add_distrib, hdegree, hbool]
  rw [hleft, hright] at hsum
  have hexact := connected_edge_add_one_eq_vertex_add_excess H hconn
  omega

theorem sparseCore_card_le
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected) :
    (sparseCoreVertices H).card ≤
      2 * (leafVertices H).card + 2 * sparseExcess H := by
  rw [sparseCore_card_eq H hH]
  have hb := branch_card_le_leaf_add_twice_excess H hH hconn
  omega

theorem sum_degree_sparseCore_add_twice_degreeTwo
    (H : GraphCode) [DecidableRel H.graph.Adj] :
    (∑ v ∈ sparseCoreVertices H, H.graph.degree v) +
        2 * (degreeTwoVertices H).card = 2 * H.edgeCount := by
  classical
  have hpart :
      (∑ v ∈ (Finset.univ : Finset (Fin H.vertexCount)) \
          degreeTwoVertices H, H.graph.degree v) +
        ∑ v ∈ degreeTwoVertices H, H.graph.degree v =
          ∑ v : Fin H.vertexCount, H.graph.degree v :=
    Finset.sum_sdiff
      (show degreeTwoVertices H ⊆
        (Finset.univ : Finset (Fin H.vertexCount)) from Finset.subset_univ _)
  have htwo : ∑ v ∈ degreeTwoVertices H, H.graph.degree v =
      2 * (degreeTwoVertices H).card := by
    calc
      ∑ v ∈ degreeTwoVertices H, H.graph.degree v =
          ∑ _v ∈ degreeTwoVertices H, 2 := by
            apply Finset.sum_congr rfl
            intro v hv
            exact mem_degreeTwoVertices H v |>.mp hv
      _ = 2 * (degreeTwoVertices H).card := by simp [mul_comm]
  have hdegree : ∑ v : Fin H.vertexCount, H.graph.degree v =
      2 * H.edgeCount := by
    simpa [GraphCode.edgeCount_eq_card_edgeFinset] using
      H.graph.sum_degrees_eq_twice_card_edges
  rw [← hdegree, ← htwo]
  simpa [sparseCoreVertices, add_comm] using hpart

theorem sum_degree_sparseCore_le
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected) :
    (∑ v ∈ sparseCoreVertices H, H.graph.degree v) ≤
      4 * (leafVertices H).card + 6 * sparseExcess H := by
  have hsum := sum_degree_sparseCore_add_twice_degreeTwo H
  have hsplit := degreeTwo_card_add_core_card H
  have hcore := sparseCore_card_le H hH hconn
  have hexact := connected_edge_add_one_eq_vertex_add_excess H hconn
  omega

end Erdos570
